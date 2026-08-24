/*
 * This file is part of the AzerothCore Project. See AUTHORS file for Copyright information
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2 of the License, or (at your
 * option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program. If not, see <http://www.gnu.org/licenses/>.
 */

// ToCloud9 cluster partition enforcement for random bots. Each worldserver
// only owns the maps assigned to it by the servers registry; a random bot
// that ends up on a foreign map (portal, boat, zeppelin...) is logged out
// here and handed off through NATS (playerbots.login-request) to the
// worldserver that owns the map — or re-randomized onto an owned map when
// no playerbots-enabled worldserver serves the destination
// (AiPlayerbot.ClusterBotMaps).

#include "BattlegroundMgr.h"
#include "CharacterCache.h"
#include "DBCStores.h"
#include "InstanceSaveMgr.h"
#include "Group.h"
#include "GroupMgr.h"
#include "Log.h"
#include "ObjectAccessor.h"
#include "ObjectGuid.h"
#include "Opcodes.h"
#include "Player.h"
#include "PlayerbotAIConfig.h"
#include "Playerbots.h"
#include "PlayerbotsCluster.h"
#include "PositionValue.h"
#include "Random.h"
#include "RandomPlayerbotMgr.h"
#include "ScriptMgr.h"
#include "TC9Sidecar.h"
#include "WorldSession.h"
#include "WorldSessionMgr.h"

#include <algorithm>
#include <cstdio>
#include <mutex>
#include <thread>
#include <unordered_map>
#include <vector>

namespace
{
    constexpr char CLUSTER_LOGIN_REQUEST_SUBJECT[] = "playerbots.login-request";
    // Asks whichever shard currently hosts a grouped bot to send it to its
    // master. The partition keeps a bot on the shard owning the map it is
    // saved on, which is not necessarily the shard hosting the player who
    // grouped it: the group forms over NATS, but the bot then sits in another
    // process and can neither be seen nor followed. Carries the master's
    // position so the receiving shard can teleport the bot onto it.
    constexpr char CLUSTER_GROUP_ANCHOR_SUBJECT[] = "playerbots.group-anchor";
    constexpr char GROUP_INVITE_CREATED_SUBJECT[] = "group.invite.created";
    constexpr char GUILD_INVITE_CREATED_SUBJECT[] = "guild.invite.created";
    constexpr char GROUP_MESSAGE_NEW_SUBJECT[] = "group.message.new";
    // The gateway swallows whisper and guild chat: it answers the chat service
    // itself and never forwards the packet to the worldserver, so the vanilla
    // OnPlayerCanUseChat hooks never fire and in-process bots stay deaf
    // (BUG-TC9-057). These two subjects re-inject the message on the world side.
    // The whisper subject is published per gateway, hence the wildcard token.
    constexpr char WHISPER_INCOME_SUBJECT[] = "chat.gw.*.income.whisper";
    constexpr char GUILD_MESSAGE_NEW_SUBJECT[] = "guild.message.new";
    constexpr char MATCHMAKING_INVITED_SUBJECT[] = "matchmaking.pvpqueue.invited";
    constexpr char MATCHMAKING_QUEUED_SUBJECT[] = "matchmaking.pvpqueue.joined";
    constexpr char MATCHMAKING_EXPIRED_SUBJECT[] = "matchmaking.pvpqueue.invite.expired";
    constexpr uint32 CLUSTER_KICK_COOLDOWN_MS = 30 * 1000;  // per bot, breaks kick<->handoff loops
    constexpr uint32 CLUSTER_LOGIN_DELAY_MS = 2 * 1000;     // lets the sender's logout save reach the DB
    constexpr int32 CLUSTER_BG_JOIN_RETRY_MS = 500;         // local BG instance can lag behind the invite
    constexpr int32 CLUSTER_BG_JOIN_ATTEMPTS = 20;
    // Safety net only: matchmaking owns the queue timers, the map is cleared
    // on invite/expire events; the TTL just unblocks bots after lost events.
    constexpr int32 CLUSTER_BG_QUEUE_TTL_MS = 10 * 60 * 1000;

    // Fed from map-update worker threads, drained on the world thread.
    std::mutex clusterPendingMutex;
    std::vector<ObjectGuid> clusterPendingKicks;

    // World thread only.
    std::unordered_map<ObjectGuid::LowType, int32> clusterKickCooldowns;
    struct ClusterPendingLogin
    {
        ObjectGuid::LowType guid;
        uint32 mapId;
        int32 delay;
    };
    std::vector<ClusterPendingLogin> clusterPendingLogins;

    // A bot handed to another shard arrives after OnAddMember has already run
    // everywhere, so nothing re-binds it to the master waiting in the dungeon.
    // Re-check shortly after the login lands. World thread only.
    struct ClusterPendingGroupBind
    {
        ObjectGuid::LowType guid;
        int32 delay;
    };
    std::vector<ClusterPendingGroupBind> clusterPendingGroupBinds;
    constexpr int32 CLUSTER_GROUP_BIND_DELAY_MS = 3000;

    bool clusterSubscribed = false;

    // Fed from the sidecar-query threads, drained on the world thread.
    struct ClusterPendingBGJoin
    {
        ObjectGuid::LowType guid;
        uint32 bgTypeId;
        uint32 instanceId;
        int32 attemptsLeft;
        int32 delay;
        // Backfill joins (C-BG.5) bypass the matchmaking queue: the service
        // never invited the bot, so a joined confirmation would be rejected.
        bool notifyMatchmaking = true;
    };
    std::mutex clusterPendingBGMutex;
    std::vector<ClusterPendingBGJoin> clusterPendingBGJoins;

    // World thread only. Random bots we enqueued into the matchmaking BG
    // queues (C-BG.3), keyed by guid; value = remaining safety TTL.
    std::unordered_map<ObjectGuid::LowType, int32> clusterBGQueuedBots;

    bool IsMapServedByClusterBots(uint32 mapId)
    {
        std::vector<uint32> const& maps = sPlayerbotAIConfig.clusterBotMaps;
        return maps.empty() || std::find(maps.begin(), maps.end(), mapId) != maps.end();
    }

    // Runs on the world thread (delivered through ProcessHooks).
    void OnClusterLoginRequest(char const* /*subject*/, char const* payload, int payloadLen)
    {
        uint32 guidLow = 0;
        uint32 mapId = 0;
        std::string data(payload, payloadLen);
        if (sscanf(data.c_str(), "{\"g\":%u,\"m\":%u}", &guidLow, &mapId) != 2)
            return;

        if (!sPlayerbotAIConfig.enabled || !sToCloud9Sidecar->IsMapAssigned(mapId))
            return;

        for (ClusterPendingLogin const& pending : clusterPendingLogins)
            if (pending.guid == guidLow)
                return;

        clusterPendingLogins.push_back({guidLow, mapId, int32(CLUSTER_LOGIN_DELAY_MS)});
    }

    // Where a group actually is, as seen by the shard hosting one of its real
    // players. Broadcast on every group change and every map change, and
    // consumed by every other shard to bring its own grouped bots along.
    //
    // This replaces the earlier per-bot "follow" message, which keyed off the
    // group leader. LFG groups are routinely led by a bot, so that message was
    // never sent for the one case it was written for.
    struct ClusterPendingAnchor
    {
        ObjectGuid::LowType groupLow;
        // Whose instance the bots belong in. TeleportTo takes no instance, so
        // without binding to this player's save first every bot resolves its
        // own copy of the dungeon and the master arrives alone.
        ObjectGuid::LowType anchorLow;
        uint32 mapId;
        uint32 instanceId;
        float x, y, z, o;
        bool publish;
        // The roster travels WITH the anchor. A group formed inside a
        // worldserver (every LFG party) was never registered with the group
        // service, so no other shard has it and a GetGroupByGUID lookup on the
        // receiving side finds nothing -- the message was published into the
        // void and the bots never came. Carrying the members makes delivery
        // independent of whether the group was mirrored.
        std::vector<ObjectGuid::LowType> members;
    };

    // Fed from map-update worker threads (OnMapChanged), drained on the world
    // thread. Teleporting a player from another map's update thread is not
    // safe, so the hook only records the anchor.
    std::mutex clusterPendingAnchorMutex;
    std::vector<ClusterPendingAnchor> clusterPendingAnchors;

    // The group's master is whichever real player this shard can see, not the
    // leader. GetFirstMember() walks Player objects, so it only ever yields
    // members hosted in this process -- exactly the ones we can speak for.
    Player* FindLocalGroupAnchor(Group* group)
    {
        for (GroupReference* itr = group->GetFirstMember(); itr != nullptr; itr = itr->next())
        {
            Player* member = itr->GetSource();
            if (!member || !member->GetSession() || member->GetSession()->IsBot())
                continue;

            return member;
        }

        return nullptr;
    }

    // Point a bot at the real player this shard hosts. Idempotent: the anchor
    // is re-applied whenever the group moves, and a bot handed to a new shard
    // has to be re-bound there because OnAddMember already fired elsewhere.
    void BindBotToAnchor(Player* bot, Player* anchor, Group* group)
    {
        PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot);
        if (!botAI || botAI->GetMaster() == anchor)
            return;

        bool isRandomBot = sRandomPlayerbotMgr.IsRandomBot(bot);
        if (!isRandomBot)
            return;  // alt bots keep their owner

        LOG_INFO("playerbots", "Cluster: bot {} now following {}", bot->GetName(), anchor->GetName());

        botAI->SetMaster(anchor);
        botAI->ResetStrategies();
        botAI->ChangeStrategy(group->isLFGGroup() ? "+follow,-bg" : "+follow,-lfg,-bg",
                              BOT_STATE_NON_COMBAT);
        botAI->Reset();
    }

    void QueueGroupAnchor(Group* group, Player* anchor, bool publish)
    {
        if (!group || !anchor)
            return;

        ClusterPendingAnchor pending;
        pending.groupLow = group->GetGUID().GetCounter();
        pending.anchorLow = anchor->GetGUID().GetCounter();
        pending.mapId = anchor->GetMapId();
        pending.instanceId = anchor->GetInstanceId();
        pending.x = anchor->GetPositionX();
        pending.y = anchor->GetPositionY();
        pending.z = anchor->GetPositionZ();
        pending.o = anchor->GetOrientation();
        pending.publish = publish;
        for (auto const& slot : group->GetMemberSlots())
            pending.members.push_back(slot.guid.GetCounter());

        std::lock_guard<std::mutex> lock(clusterPendingAnchorMutex);
        for (ClusterPendingAnchor& existing : clusterPendingAnchors)
        {
            if (existing.groupLow == pending.groupLow)
            {
                pending.publish = pending.publish || existing.publish;
                existing = pending;
                return;
            }
        }

        clusterPendingAnchors.push_back(pending);
    }

    // Runs on the world thread (delivered through ProcessHooks), same as the
    // login request above.
    //
    // A bot grouped by a player on another shard is invisible to that player:
    // the group forms over NATS, but the bot stays in the process owning the
    // map it is saved on. This teleports it onto its master instead of trying
    // to move it between shards directly -- the destination map belongs to the
    // master's shard, so the existing partition path (OnPlayerUpdateZone ->
    // ProcessPendingKicks -> handoff) picks the bot up and delivers it there,
    // and because the logout saves the new position it loads next to its
    // master rather than back where it started. One transport, not two.
    void OnClusterGroupAnchor(char const* /*subject*/, char const* payload, int payloadLen)
    {
        uint32 groupLow = 0;
        uint32 anchorLow = 0;
        uint32 mapId = 0;
        uint32 instanceId = 0;
        float x = 0.f, y = 0.f, z = 0.f, o = 0.f;
        std::string data(payload, payloadLen);
        if (sscanf(data.c_str(), "{\"gg\":%u,\"a\":%u,\"m\":%u,\"i\":%u,\"x\":%f,\"y\":%f,\"z\":%f,\"o\":%f}",
                   &groupLow, &anchorLow, &mapId, &instanceId, &x, &y, &z, &o) != 8)
            return;

        if (!sPlayerbotAIConfig.enabled)
            return;

        ClusterPendingAnchor pending;
        pending.groupLow = groupLow;
        pending.anchorLow = anchorLow;
        pending.mapId = mapId;
        pending.instanceId = instanceId;
        pending.x = x;
        pending.y = y;
        pending.z = z;
        pending.o = o;
        pending.publish = false;

        // Deliberately no GetGroupByGUID guard: an LFG group exists only in
        // the worldserver that built it, so requiring a local group here threw
        // the message away on exactly the shards holding the bots.
        if (size_t const memPos = data.find("\"mem\":"); memPos != std::string::npos)
        {
            char const* cursor = data.c_str() + memPos + 6;
            while (*cursor)
            {
                char* end = nullptr;
                unsigned long const guid = strtoul(cursor, &end, 10);
                if (end == cursor)
                    break;

                if (guid)
                    pending.members.push_back(ObjectGuid::LowType(guid));

                cursor = (*end == ',') ? end + 1 : end;
                if (*end != ',')
                    break;
            }
        }

        std::lock_guard<std::mutex> lock(clusterPendingAnchorMutex);
        clusterPendingAnchors.push_back(pending);
    }

    // Minimal extractor for one numeric field of the groupserver JSON events
    // (envelope {"v":...,"t":...,"p":{...}} built by EventToSendGenericPayload).
    bool ExtractJsonUInt64(std::string const& json, char const* key, uint64& out)
    {
        std::string needle = std::string("\"") + key + "\":";
        size_t pos = json.find(needle);
        if (pos == std::string::npos)
            return false;

        return sscanf(json.c_str() + pos + needle.size(), "%llu", (unsigned long long*)&out) == 1;
    }

    // String variant. Handles the escapes Go's json.Marshal emits inside chat
    // text; exotic escapes (\uXXXX) are kept raw — chat commands are plain
    // words, anything else was never a command to begin with.
    bool ExtractJsonString(std::string const& json, char const* key, std::string& out)
    {
        std::string needle = std::string("\"") + key + "\":\"";
        size_t pos = json.find(needle);
        if (pos == std::string::npos)
            return false;

        out.clear();
        for (size_t i = pos + needle.size(); i < json.size(); ++i)
        {
            char c = json[i];
            if (c == '"')
                return true;

            if (c == '\\' && i + 1 < json.size())
            {
                char next = json[++i];
                if (next == '"' || next == '\\' || next == '/')
                    out += next;
                else
                {
                    out += '\\';
                    out += next;
                }
                continue;
            }

            out += c;
        }

        return false;  // unterminated string
    }

    // Array-of-numbers variant ("Receivers":[1,2,...]).
    bool ExtractJsonUInt64Array(std::string const& json, char const* key, std::vector<uint64>& out)
    {
        std::string needle = std::string("\"") + key + "\":[";
        size_t pos = json.find(needle);
        if (pos == std::string::npos)
            return false;

        char const* cursor = json.c_str() + pos + needle.size();
        while (*cursor && *cursor != ']')
        {
            unsigned long long value = 0;
            int consumed = 0;
            if (sscanf(cursor, "%llu%n", &value, &consumed) != 1)
                return false;

            out.push_back(uint64(value));
            cursor += consumed;
            if (*cursor == ',')
                ++cursor;
        }

        return *cursor == ']';
    }

    // Runs on the world thread (delivered through ProcessHooks). The group
    // service created an invite for a character without gateway session; if
    // that character is one of our local random bots, accept on its behalf
    // (BUG-022: the SMSG_GROUP_INVITE only reaches gateway sessions).
    void OnClusterGroupInviteCreated(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled)
            return;

        std::string data(payload, payloadLen);
        uint64 inviteeGUID = 0;
        if (!ExtractJsonUInt64(data, "InviteeGUID", inviteeGUID) || !inviteeGUID)
            return;

        Player* bot = ObjectAccessor::FindPlayer(
            ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(inviteeGUID)));
        if (!bot || !bot->GetSession() || !bot->GetSession()->IsBot())
            return;  // not one of our in-process sessions (real players use the gateway)

        if (!sRandomPlayerbotMgr.IsRandomBot(bot))
        {
            // Alt bots mirror vanilla AcceptInvitationAction: only their owner
            // may pull them into a group (cluster stand-in for the
            // PLAYERBOT_SECURITY_INVITE check — the inviter can be cross-shard,
            // so compare GUIDs instead of resolving a local Player).
            PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot);
            uint64 inviterGUID = 0;
            if (!botAI || !botAI->GetMaster() ||
                !ExtractJsonUInt64(data, "InviterGUID", inviterGUID) ||
                botAI->GetMaster()->GetGUID().GetCounter() != ObjectGuid::LowType(inviterGUID))
                return;
        }

        if (bot->GetGroup())
            return;  // already grouped (local mirror fed by group.* events)

        LOG_INFO("playerbots", "Cluster: accepting group invite for bot {}", bot->GetName());

        // Blocking gRPC call: keep it off the world thread. Group state comes
        // back asynchronously through the group.created/member.added events.
        uint64 guidCounter = bot->GetGUID().GetCounter();
        std::thread([guidCounter]() {
            sToCloud9Sidecar->GroupAcceptInvite(guidCounter);
        }).detach();
    }

    // Runs on the world thread (delivered through ProcessHooks). The guild
    // service created an invite for a character without gateway session; if
    // that character is one of our local random bots, accept on its behalf.
    // Mirror of OnClusterGroupInviteCreated (SMSG_GUILD_INVITE only reaches
    // gateway sessions, so the vanilla "guild invite"->"guild accept" trigger
    // never fires for in-process bots).
    void OnClusterGuildInviteCreated(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled)
            return;

        std::string data(payload, payloadLen);
        uint64 inviteeGUID = 0;
        if (!ExtractJsonUInt64(data, "InviteeGUID", inviteeGUID) || !inviteeGUID)
            return;

        Player* bot = ObjectAccessor::FindPlayer(
            ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(inviteeGUID)));
        if (!bot || !bot->GetSession() || !bot->GetSession()->IsBot())
            return;  // not one of our in-process sessions (real players use the gateway)

        if (!sRandomPlayerbotMgr.IsRandomBot(bot))
        {
            // Alt bots: only their owner may pull them into a guild (cluster
            // stand-in for the security check; the inviter can be cross-shard,
            // so compare GUIDs instead of resolving a local Player).
            PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot);
            uint64 inviterGUID = 0;
            if (!botAI || !botAI->GetMaster() ||
                !ExtractJsonUInt64(data, "InviterGUID", inviterGUID) ||
                botAI->GetMaster()->GetGUID().GetCounter() != ObjectGuid::LowType(inviterGUID))
                return;
        }

        if (bot->GetGuildId())
            return;  // already in a guild (local mirror fed by guild.* events)

        LOG_INFO("playerbots", "Cluster: accepting guild invite for bot {}", bot->GetName());

        // Snapshot the bot's character on the world thread; the guild service's
        // InviteAccepted RPC needs the full member row. Blocking gRPC call runs
        // off-thread; the guild membership comes back via guild.member.added.
        uint64 guidCounter = bot->GetGUID().GetCounter();
        std::string name = bot->GetName();
        uint32 lvl = bot->GetLevel();
        uint32 race = bot->getRace();
        uint32 classId = bot->getClass();
        uint32 gender = bot->getGender();
        uint32 areaId = bot->GetZoneId();
        uint64 accountId = bot->GetSession()->GetAccountId();
        std::thread([=]() {
            sToCloud9Sidecar->GuildAcceptInvite(guidCounter, name, lvl, race, classId, gender, areaId, accountId);
        }).detach();
    }

    // Runs on the world thread (delivered through ProcessHooks). Behind the
    // gateway, group/raid chat is served by the group service: the sender's
    // CMSG_MESSAGECHAT never reaches this worldserver, so the vanilla
    // OnPlayerCanUseChat(Group*) hook — the entry point for every chat
    // command (follow, stay, summon...) — never fires for in-process bots.
    // Feed the receivers that are local bots from the NATS mirror instead.
    void OnClusterGroupChatMessage(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled)
            return;

        std::string data(payload, payloadLen);
        uint64 senderGUID = 0;
        if (!ExtractJsonUInt64(data, "SenderGUID", senderGUID) || !senderGUID)
            return;

        // HandleCommand needs the sender as a local Player. Alt bots live on
        // their owner's shard so the interesting sender always resolves; a
        // cross-shard sender has no local Player to command through.
        Player* sender = ObjectAccessor::FindPlayer(
            ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(senderGUID)));
        if (!sender)
            return;

        if (sender->GetSession() && sender->GetSession()->IsBot())
            return;  // bot chatter already goes through the vanilla local hook

        uint64 messageType = 0;
        std::string msg;
        std::vector<uint64> receivers;
        if (!ExtractJsonUInt64(data, "MessageType", messageType) ||
            !ExtractJsonString(data, "Msg", msg) || msg.empty() ||
            !ExtractJsonUInt64Array(data, "Receivers", receivers))
            return;

        for (uint64 guid : receivers)
        {
            if (guid == senderGUID)
                continue;

            Player* member = ObjectAccessor::FindPlayer(
                ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(guid)));
            if (!member || !member->GetSession() || !member->GetSession()->IsBot())
                continue;

            if (PlayerbotAI* botAI = GET_PLAYERBOT_AI(member))
                botAI->HandleCommand(uint32(messageType), msg, sender);
        }
    }

    // Whisper re-injection. Unlike the group hook we must NOT filter on
    // session->IsBot(): a selfbot (".playerbot bot self") is a real player who
    // happens to carry a PlayerbotAI, and it is the only channel it can be
    // commanded through. The vanilla hook's own condition is simply "does the
    // receiver have an AI", so we mirror it.
    // We only feed the AI here; delivering the text to a human client stays the
    // gateway's job, so there is no double delivery.
    void OnClusterWhisper(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled)
            return;

        std::string data(payload, payloadLen);
        uint64 senderGUID = 0;
        uint64 receiverGUID = 0;
        std::string msg;
        if (!ExtractJsonUInt64(data, "SenderGUID", senderGUID) || !senderGUID ||
            !ExtractJsonUInt64(data, "ReceiverGUID", receiverGUID) || !receiverGUID ||
            !ExtractJsonString(data, "Msg", msg) || msg.empty())
            return;

        // HandleCommand needs the sender as a local Player; a cross-shard
        // sender cannot be resolved (same limitation as the group hook).
        Player* sender = ObjectAccessor::FindPlayer(
            ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(senderGUID)));
        if (!sender)
            return;

        if (sender->GetSession() && sender->GetSession()->IsBot())
            return;  // bot chatter already goes through the vanilla local hook

        Player* receiver = ObjectAccessor::FindPlayer(
            ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(receiverGUID)));
        if (!receiver)
            return;

        if (PlayerbotAI* botAI = GET_PLAYERBOT_AI(receiver))
            botAI->HandleCommand(CHAT_MSG_WHISPER, msg, sender);
    }

    // Guild chat re-injection. Vanilla semantics are deliberately preserved:
    // only the sender's OWN bots react, never every bot of the guild — our
    // main guild holds several hundred of them and a single line would
    // otherwise command them all.
    void OnClusterGuildChatMessage(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled)
            return;

        std::string data(payload, payloadLen);
        uint64 senderGUID = 0;
        std::string msg;
        if (!ExtractJsonUInt64(data, "SenderGUID", senderGUID) || !senderGUID ||
            !ExtractJsonString(data, "Msg", msg) || msg.empty())
            return;

        Player* sender = ObjectAccessor::FindPlayer(
            ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(senderGUID)));
        if (!sender)
            return;

        if (sender->GetSession() && sender->GetSession()->IsBot())
            return;

        PlayerbotMgr* playerbotMgr = PlayerbotsMgr::instance().GetPlayerbotMgr(sender);
        if (!playerbotMgr)
            return;

        for (PlayerBotMap::const_iterator it = playerbotMgr->GetPlayerBotsBegin();
             it != playerbotMgr->GetPlayerBotsEnd(); ++it)
        {
            Player* const bot = it->second;
            if (!bot || bot->GetGuildId() != sender->GetGuildId())
                continue;

            if (PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot))
                botAI->HandleCommand(CHAT_MSG_GUILD, msg, sender);
        }
    }

    // Runs on the world thread (delivered through ProcessHooks). The
    // matchmaking service invited players to a battleground; an in-process
    // bot has no gateway session, so nobody accepts the invite nor performs
    // the enterBattleground sequence (queue data -> AddPlayers -> joined
    // confirmation) on its behalf (chantier C-BG, DESIGN-bots-bg-cluster.md).
    void OnClusterBGInvite(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled)
            return;

        std::string data(payload, payloadLen);
        std::vector<uint64> invited;
        if (!ExtractJsonUInt64Array(data, "PlayersGUID", invited))
            return;

        for (uint64 guidRaw : invited)
        {
            Player* bot = ObjectAccessor::FindPlayer(
                ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(guidRaw)));
            if (!bot || !bot->GetSession() || !bot->GetSession()->IsBot())
                continue;

            clusterBGQueuedBots.erase(bot->GetGUID().GetCounter());

            if (sRandomPlayerbotMgr.IsRandomBot(bot) && !sPlayerbotAIConfig.randomBotJoinBG)
                continue;  // random bots opt into BG queues through RandomBotJoinBG (C-BG.3)

            LOG_INFO("playerbots", "Cluster: bot {} invited to BG, querying assignment", bot->GetName());

            // Blocking gRPC calls: keep them off the world thread. The join
            // itself needs the world thread, so it comes back through
            // clusterPendingBGJoins.
            uint64 guidCounter = bot->GetGUID().GetCounter();
            std::thread([guidCounter]() {
                uint32 bgTypeId = 0;
                uint32 instanceId = 0;
                uint32 mapId = 0;
                bool isLocal = false;
                if (!sToCloud9Sidecar->BattlegroundQueueDataForLocalPlayer(
                        guidCounter, bgTypeId, instanceId, mapId, isLocal))
                {
                    LOG_INFO("playerbots", "Cluster: no BG assignment for invited bot guid {}", guidCounter);
                    return;
                }

                if (!isLocal)
                {
                    // C-BG.2 (cross-shard: pending BG in the login-request)
                    // not implemented: let the invite expire.
                    LOG_INFO("playerbots", "Cluster: bot guid {} BG instance {} runs on another shard, skipping",
                             guidCounter, instanceId);
                    return;
                }

                std::lock_guard<std::mutex> lock(clusterPendingBGMutex);
                clusterPendingBGJoins.push_back({ObjectGuid::LowType(guidCounter), bgTypeId, instanceId,
                                                 CLUSTER_BG_JOIN_ATTEMPTS, CLUSTER_BG_JOIN_RETRY_MS});
            }).detach();
        }
    }

    // Runs on the world thread (delivered through ProcessHooks). A player
    // entered a matchmaking BG queue; in vanilla RandomBotJoinBG makes random
    // bots fill both factions so the battleground pops, but the vanilla
    // detection reads the LOCAL AC queue, empty behind the gateway. Fill the
    // matchmaking queue instead, from the shard hosting the battleground map
    // (the only one whose bots can force-join at the pop, see C-BG.1 above).
    void OnClusterBGQueueJoined(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled || !sPlayerbotAIConfig.randomBotJoinBG)
            return;

        std::string data(payload, payloadLen);

        uint64 arenaType = 0;
        if (ExtractJsonUInt64(data, "ArenaType", arenaType) && arenaType)
            return;  // arenas are out of scope

        uint64 typeId = 0;
        uint64 minLvl = 0;
        uint64 maxLvl = 0;
        std::vector<uint64> queued;
        if (!ExtractJsonUInt64(data, "TypeID", typeId) ||
            !ExtractJsonUInt64(data, "PVPQueueMinLVL", minLvl) ||
            !ExtractJsonUInt64(data, "PVPQueueMaxLVL", maxLvl) ||
            !ExtractJsonUInt64Array(data, "PlayersGUID", queued) || queued.empty())
            return;

        // Our own fills echo back through this event: an enqueue where every
        // player is a local bot must not trigger another fill. A human
        // grouping with alt bots still counts as a real enqueue (skipping it
        // left the opposite faction unfilled: observed as a 10v5 join).
        bool allLocalBots = true;
        for (uint64 guidRaw : queued)
        {
            Player* who = ObjectAccessor::FindPlayer(
                ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(guidRaw)));
            if (!who || !who->GetSession() || !who->GetSession()->IsBot())
            {
                allLocalBots = false;
                break;
            }
        }
        if (allLocalBots)
            return;

        Battleground* bgTemplate = sBattlegroundMgr->GetBattlegroundTemplate(BattlegroundTypeId(typeId));
        if (!bgTemplate || !sToCloud9Sidecar->IsMapAssigned(bgTemplate->GetMapId()))
            return;

        uint32 perFaction = std::max<uint32>(1, bgTemplate->GetMinPlayersPerTeam());

        struct BGFillPick
        {
            ObjectGuid::LowType guid;
            uint32 level;
            uint32 pvpTeamId;  // matchmaking enum: 1 alliance, 2 horde
        };
        uint32 needed[2] = {perFaction, perFaction};  // TEAM_ALLIANCE, TEAM_HORDE

        // The queued humans hold slots on their own faction: don't double-book
        // them with bots (a solo queuer used to produce 6v5).
        for (uint64 guidRaw : queued)
        {
            CharacterCacheEntry const* entry = sCharacterCache->GetCharacterCacheByGuid(
                ObjectGuid::Create<HighGuid::Player>(ObjectGuid::LowType(guidRaw)));
            if (!entry)
                continue;

            TeamId team = Player::TeamIdForRace(entry->Race);
            if (team <= TEAM_HORDE && needed[team])
                --needed[team];
        }

        std::vector<BGFillPick> picks;

        for (auto it = sRandomPlayerbotMgr.GetPlayerBotsBegin();
             it != sRandomPlayerbotMgr.GetPlayerBotsEnd(); ++it)
        {
            Player* bot = it->second;
            if (!bot || !bot->IsInWorld() || !bot->GetSession() || !bot->GetSession()->IsBot() ||
                !sRandomPlayerbotMgr.IsRandomBot(bot))
                continue;

            if (bot->GetGroup() || bot->InBattleground() || bot->InBattlegroundQueue() || !bot->IsAlive())
                continue;

            uint32 level = bot->GetLevel();
            if (level < minLvl || level > maxLvl)
                continue;

            if (clusterBGQueuedBots.count(bot->GetGUID().GetCounter()))
                continue;  // already sitting in a matchmaking queue

            TeamId team = bot->GetTeamId();
            if (team > TEAM_HORDE || !needed[team])
                continue;

            --needed[team];
            picks.push_back({bot->GetGUID().GetCounter(), level, team == TEAM_HORDE ? 2u : 1u});
            if (!needed[TEAM_ALLIANCE] && !needed[TEAM_HORDE])
                break;
        }

        if (picks.empty())
            return;

        for (BGFillPick const& pick : picks)
            clusterBGQueuedBots[pick.guid] = CLUSTER_BG_QUEUE_TTL_MS;

        LOG_INFO("playerbots",
                 "Cluster: filling BG type {} bracket {}-{} queue with {} bots ({} alliance / {} horde still short)",
                 typeId, minLvl, maxLvl, picks.size(), needed[TEAM_ALLIANCE], needed[TEAM_HORDE]);

        // Blocking gRPC calls: keep them off the world thread, sequential to
        // spare the matchmaking service.
        uint32 bgTypeId = uint32(typeId);
        std::thread([picks, bgTypeId]() {
            for (BGFillPick const& pick : picks)
                if (!sToCloud9Sidecar->EnqueueLocalPlayerToBattleground(
                        pick.guid, pick.level, bgTypeId, pick.pvpTeamId))
                    LOG_WARN("playerbots", "Cluster: BG enqueue failed for bot guid {}", pick.guid);
        }).detach();
    }

    // Runs on the world thread (delivered through ProcessHooks). Invited
    // players who never joined got dropped from the queue: free the bots so
    // a later enqueue can pick them again.
    void OnClusterBGInviteExpired(char const* /*subject*/, char const* payload, int payloadLen)
    {
        if (!sPlayerbotAIConfig.enabled)
            return;

        std::string data(payload, payloadLen);
        std::vector<uint64> expired;
        if (!ExtractJsonUInt64Array(data, "PlayersGUID", expired))
            return;

        for (uint64 guidRaw : expired)
            clusterBGQueuedBots.erase(ObjectGuid::LowType(guidRaw));
    }
}

namespace PlayerbotsCluster
{
    bool PoolFilterActive()
    {
        return sToCloud9Sidecar->ClusterModeEnabled();
    }

    bool ShouldSkipPoolCandidate(uint32 mapId)
    {
        // Strict partition: only pick characters saved on maps this
        // worldserver owns. Characters on maps served by nobody (e.g.
        // blood elf/draenei starters while no shard owns map 530) stay
        // benched until a shard owns their map: re-randomizing them is
        // unreliable (RandomTeleportForLevel has no valid location for
        // some level/race combos and can land outside randomBotMaps,
        // observed as kalimdor bots leaking to map 0).
        return sToCloud9Sidecar->ClusterModeEnabled()
            && !sToCloud9Sidecar->IsMapAssigned(mapId);
    }
}

class PlayerbotsClusterPlayerScript : public PlayerScript
{
public:
    PlayerbotsClusterPlayerScript() : PlayerScript("PlayerbotsClusterPlayerScript", {
        PLAYERHOOK_ON_UPDATE_ZONE,
        PLAYERHOOK_ON_BEFORE_TELEPORT,
        PLAYERHOOK_ON_MAP_CHANGED
    }) {}

    // A real player changing map is the only reliable signal that a group has
    // moved somewhere its bots are not. LFG dungeon entry is the case that
    // matters: LFGMgr teleports the members it can resolve locally and skips
    // everyone else, so on a partitioned cluster the human lands in the
    // instance alone. Record the anchor; the world thread does the work.
    //
    // May run on map-update worker threads: only collect, never act here.
    void OnPlayerMapChanged(Player* player) override
    {
        if (!sToCloud9Sidecar->ClusterModeEnabled() || !sPlayerbotAIConfig.enabled)
            return;

        if (!player->GetSession() || player->GetSession()->IsBot())
            return;

        if (player->InBattleground())
            return;  // matchmaking owns BG membership (C-BG.5)

        if (Group* group = player->GetGroup())
            QueueGroupAnchor(group, player, true);
    }

    // A random bot pulled out of a running battleground shrinks its team below
    // MinPlayersPerTeam and AC ends the match "not enough players" (observed:
    // bot silently teleported to its grind map mid-WSG). Veto the teleport and
    // log the attempt so the trigger path becomes visible.
    bool OnPlayerBeforeTeleport(Player* player, uint32 mapid, float /*x*/, float /*y*/, float /*z*/,
                                float /*orientation*/, uint32 /*options*/, Unit* /*target*/) override
    {
        if (!sToCloud9Sidecar->ClusterModeEnabled())
            return true;

        if (!player->GetSession() || !player->GetSession()->IsBot() ||
            !sRandomPlayerbotMgr.IsRandomBot(player))
            return true;

        Battleground* bg = player->GetBattleground();
        if (!bg || mapid == bg->GetMapId())
            return true;

        if (bg->GetStatus() != STATUS_WAIT_JOIN && bg->GetStatus() != STATUS_IN_PROGRESS)
            return true;

        LOG_INFO("playerbots", "Cluster: blocked teleport of BG participant bot {} to map {} (bg instance {} status {})",
                 player->GetName(), mapid, bg->GetInstanceID(), uint32(bg->GetStatus()));
        return false;
    }

    // May run on map-update worker threads: only collect, never act here.
    void OnPlayerUpdateZone(Player* player, uint32 /*newZone*/, uint32 /*newArea*/) override
    {
        if (!sToCloud9Sidecar->ClusterModeEnabled())
            return;

        if (!player->GetSession() || !player->GetSession()->IsBot())
            return;

        if (sToCloud9Sidecar->IsMapAssigned(player->GetMapId()))
            return;

        std::lock_guard<std::mutex> lock(clusterPendingMutex);
        if (std::find(clusterPendingKicks.begin(), clusterPendingKicks.end(), player->GetGUID()) ==
            clusterPendingKicks.end())
            clusterPendingKicks.push_back(player->GetGUID());
    }
};

class PlayerbotsClusterWorldScript : public WorldScript
{
public:
    PlayerbotsClusterWorldScript() : WorldScript("PlayerbotsClusterWorldScript", {
        WORLDHOOK_ON_UPDATE
    }) {}

    void OnUpdate(uint32 diff) override
    {
        if (!sToCloud9Sidecar->ClusterModeEnabled())
            return;

        if (!clusterSubscribed && sPlayerbotAIConfig.enabled)
            clusterSubscribed =
                sToCloud9Sidecar->NatsSubscribe(CLUSTER_LOGIN_REQUEST_SUBJECT, &OnClusterLoginRequest) &&
                sToCloud9Sidecar->NatsSubscribe(CLUSTER_GROUP_ANCHOR_SUBJECT, &OnClusterGroupAnchor) &&
                sToCloud9Sidecar->NatsSubscribe(GROUP_INVITE_CREATED_SUBJECT, &OnClusterGroupInviteCreated) &&
                sToCloud9Sidecar->NatsSubscribe(GUILD_INVITE_CREATED_SUBJECT, &OnClusterGuildInviteCreated) &&
                sToCloud9Sidecar->NatsSubscribe(GROUP_MESSAGE_NEW_SUBJECT, &OnClusterGroupChatMessage) &&
                sToCloud9Sidecar->NatsSubscribe(WHISPER_INCOME_SUBJECT, &OnClusterWhisper) &&
                sToCloud9Sidecar->NatsSubscribe(GUILD_MESSAGE_NEW_SUBJECT, &OnClusterGuildChatMessage) &&
                sToCloud9Sidecar->NatsSubscribe(MATCHMAKING_INVITED_SUBJECT, &OnClusterBGInvite) &&
                sToCloud9Sidecar->NatsSubscribe(MATCHMAKING_QUEUED_SUBJECT, &OnClusterBGQueueJoined) &&
                sToCloud9Sidecar->NatsSubscribe(MATCHMAKING_EXPIRED_SUBJECT, &OnClusterBGInviteExpired);

        UpdateCooldowns(diff);
        ProcessPendingAnchors();
        ProcessPendingKicks();
        ProcessPendingLogins(diff);
        ProcessPendingGroupBinds(diff);
        ProcessPendingBGJoins(diff);
    }

private:
    void UpdateCooldowns(uint32 diff)
    {
        for (auto itr = clusterKickCooldowns.begin(); itr != clusterKickCooldowns.end();)
        {
            itr->second -= int32(diff);
            if (itr->second <= 0)
                itr = clusterKickCooldowns.erase(itr);
            else
                ++itr;
        }

        for (auto itr = clusterBGQueuedBots.begin(); itr != clusterBGQueuedBots.end();)
        {
            itr->second -= int32(diff);
            if (itr->second <= 0)
                itr = clusterBGQueuedBots.erase(itr);
            else
                ++itr;
        }
    }

    void ProcessPendingAnchors()
    {
        std::vector<ClusterPendingAnchor> anchors;
        {
            std::lock_guard<std::mutex> lock(clusterPendingAnchorMutex);
            if (clusterPendingAnchors.empty())
                return;

            anchors.swap(clusterPendingAnchors);
        }

        for (ClusterPendingAnchor const& anchor : anchors)
        {
            Group* group = sGroupMgr->GetGroupByGUID(anchor.groupLow);

            if (anchor.publish)
            {
                std::string payload = "{\"gg\":" + std::to_string(anchor.groupLow) +
                                      ",\"a\":" + std::to_string(anchor.anchorLow) +
                                      ",\"m\":" + std::to_string(anchor.mapId) +
                                      ",\"i\":" + std::to_string(anchor.instanceId);
                char pos[96];
                snprintf(pos, sizeof(pos), ",\"x\":%.3f,\"y\":%.3f,\"z\":%.3f,\"o\":%.3f",
                         anchor.x, anchor.y, anchor.z, anchor.o);
                payload += pos;
                payload += ",\"mem\":";
                for (size_t i = 0; i < anchor.members.size(); ++i)
                    payload += (i ? "," : "") + std::to_string(anchor.members[i]);
                payload += "}";

                sToCloud9Sidecar->NatsPublish(CLUSTER_GROUP_ANCHOR_SUBJECT, payload);
            }

            MoveLocalGroupBots(group, anchor);
        }
    }

    // The core only teleports the members it can see: LFGMgr skips anyone
    // ObjectAccessor::FindConnectedPlayer cannot resolve, and a portal or
    // hearthstone moves the player alone in the first place. Bring the bots
    // this shard owns to wherever the anchor ended up.
    void MoveLocalGroupBots(Group* group, ClusterPendingAnchor const& anchor)
    {
        // Prefer the roster carried by the anchor: on a shard that never saw
        // the group created, it is the only member list available. Fall back
        // to the local group for anchors raised in this process.
        std::vector<ObjectGuid::LowType> members = anchor.members;
        if (members.empty() && group)
            for (auto const& slot : group->GetMemberSlots())
                members.push_back(slot.guid.GetCounter());

        Player* localAnchor = group ? FindLocalGroupAnchor(group) : nullptr;

        for (ObjectGuid::LowType memberLow : members)
        {
            Player* bot = ObjectAccessor::FindPlayer(ObjectGuid::Create<HighGuid::Player>(memberLow));
            if (!bot || !bot->GetSession() || !bot->GetSession()->IsBot())
                continue;  // not in this process, or a real player

            if (bot->InBattleground())
                continue;  // BG participants stay with their match (C-BG.5)

            if (localAnchor && group)
                BindBotToAnchor(bot, localAnchor, group);

            if (bot->GetMapId() == anchor.mapId && bot->GetInstanceId() == anchor.instanceId)
                continue;

            // TeleportTo carries no instance, so bind the bot to the anchor's
            // save first -- otherwise the map is right, the copy is not, and
            // the master stands in an empty dungeon while the bots fight in
            // their own. Only possible while the anchor's save lives in this
            // process; across shards the instance cannot be shared at all.
            if (anchor.instanceId && anchor.anchorLow)
            {
                ObjectGuid const anchorGuid = ObjectGuid::Create<HighGuid::Player>(anchor.anchorLow);
                MapEntry const* mapEntry = sMapStore.LookupEntry(anchor.mapId);
                Difficulty const difficulty = (mapEntry && mapEntry->IsRaid())
                    ? bot->GetRaidDifficulty() : bot->GetDungeonDifficulty();

                if (InstanceSave* save = sInstanceSaveMgr->PlayerGetInstanceSave(anchorGuid, anchor.mapId, difficulty))
                    sInstanceSaveMgr->PlayerBindToInstance(bot->GetGUID(), save, false, bot);
            }

            LOG_INFO("playerbots", "Cluster: group anchor moves bot {} to map {} instance {}",
                     bot->GetName(), anchor.mapId, anchor.instanceId);

            bot->TeleportTo(anchor.mapId, anchor.x, anchor.y, anchor.z, anchor.o);
        }
    }

    void ProcessPendingKicks()
    {
        std::vector<ObjectGuid> kicks;
        {
            std::lock_guard<std::mutex> lock(clusterPendingMutex);
            kicks.swap(clusterPendingKicks);
        }

        for (ObjectGuid const& guid : kicks)
        {
            if (clusterKickCooldowns.count(guid.GetCounter()))
                continue;

            Player* bot = ObjectAccessor::FindPlayer(guid);
            if (!bot || !bot->GetSession() || !bot->GetSession()->IsBot())
                continue;

            uint32 mapId = bot->GetMapId();
            if (sToCloud9Sidecar->IsMapAssigned(mapId))
                continue;  // maps got reassigned meanwhile

            if (!sRandomPlayerbotMgr.IsRandomBot(bot))
                continue;  // alt bots follow their master, not the partition

            if (bot->InBattleground())
                continue;  // BG participants stay with their match (C-BG.5)

            // Never evict a bot that is standing with its master. The
            // partition governs where bots GRIND, not where a group may be:
            // a dungeon map belongs to the instance shard, but a real player
            // entering it is not partitioned and stays in whichever process
            // they were already in. The bot followed them there correctly,
            // and kicking it off the master's own map is what left players
            // alone in dungeons -- the group anchor delivered the bot and
            // this loop threw it straight back out.
            //
            // Position is deliberately NOT compared. Both earlier attempts
            // (instance equality, then map equality) tried to prove the bot
            // was already beside its master, and both lost the same race:
            // LFGMgr teleports members out of an unordered set and TeleportTo
            // is asynchronous, so a bot reaches the dungeon and fires its zone
            // update while the player is still in flight. The partition then
            // evicted the party a moment before the master landed.
            //
            // A grouped bot follows its master, not the partition -- the same
            // rule the alt-bot check above already applies. Where the group
            // should be is the anchor's business; this loop only decides where
            // UNGROUPED bots may grind.
            if (Group* group = bot->GetGroup())
            {
                bool groupHasRealPlayer = false;
                for (GroupReference* itr = group->GetFirstMember(); itr != nullptr; itr = itr->next())
                {
                    Player* member = itr->GetSource();
                    if (member && member->GetSession() && !member->GetSession()->IsBot())
                    {
                        groupHasRealPlayer = true;
                        break;
                    }
                }

                // Members hosted on other shards have no local Player, so fall
                // back to the roster: anyone the bot pool does not own is a
                // real player as far as this decision goes.
                if (!groupHasRealPlayer)
                {
                    for (auto const& slot : group->GetMemberSlots())
                    {
                        if (!sRandomPlayerbotMgr.IsRandomBot(slot.guid.GetCounter()))
                        {
                            groupHasRealPlayer = true;
                            break;
                        }
                    }
                }

                if (groupHasRealPlayer)
                {
                    if (Player* anchor = FindLocalGroupAnchor(group))
                    {
                        // Master is here, so the anchor decides where the bot
                        // goes and the partition must keep its hands off.
                        if (anchor->GetMapId() != bot->GetMapId() ||
                            anchor->GetInstanceId() != bot->GetInstanceId())
                            QueueGroupAnchor(group, anchor, false);

                        continue;
                    }

                    // No local anchor means the master is on another shard, and
                    // the bot has already teleported onto a map this one does
                    // not own -- its own private copy of the master's dungeon,
                    // which the master can never see. Exempting it here strands
                    // it there forever, because the handoff below is the only
                    // thing that can deliver it to the shard actually running
                    // that instance. Fall through: the followingMaster branch
                    // already hands grouped bots off rather than
                    // re-randomizing them.
                }
            }

            clusterKickCooldowns[guid.GetCounter()] = int32(CLUSTER_KICK_COOLDOWN_MS);

            // A grouped bot is always handed off, never re-randomized. It got
            // here by following its master -- through the area trigger relay
            // into a dungeon, most often -- and instance maps are not in
            // ClusterBotMaps, so the re-randomize branch below would drag it
            // back to its grind continent the moment the group zoned in. The
            // shard owning the destination accepts the handoff regardless of
            // whether it hosts a bot pool for that map.
            bool const followingMaster = bot->GetGroup() != nullptr;

            if (followingMaster || IsMapServedByClusterBots(mapId))
            {
                // Logout first so the receiving worldserver loads the
                // position saved on the destination map.
                LOG_INFO("playerbots", "Cluster: handing off bot {} on foreign map {}", bot->GetName(), mapId);
                sRandomPlayerbotMgr.LogoutPlayerBot(guid);

                char payload[64];
                int len = snprintf(payload, sizeof(payload), "{\"g\":%u,\"m\":%u}", guid.GetCounter(), mapId);
                sToCloud9Sidecar->NatsPublish(CLUSTER_LOGIN_REQUEST_SUBJECT, std::string(payload, len));
            }
            else
            {
                // No playerbots-enabled worldserver serves this map:
                // bring the bot back onto a map this worldserver owns.
                LOG_INFO("playerbots", "Cluster: re-randomizing bot {} from unserved map {}", bot->GetName(), mapId);
                sRandomPlayerbotMgr.RandomTeleportForLevel(bot);
                // Persist the new position now: the pool can log the bot out
                // before the next periodic save, which would leave the stale
                // unserved map in the DB and re-trigger this path forever.
                // (During a far teleport this schedules DELAYED_SAVE_PLAYER,
                // executed on arrival with the destination map.)
                bot->SaveToDB(false, false);
            }
        }
    }

    // World thread. Replicates the gateway's enterBattleground tail for an
    // in-process bot whose BG runs on THIS shard: AddPlayersToBattleground
    // equivalent (entry point + bg id + teleport) then joined confirmation,
    // plus the playerbots force-join state (BattleGroundJoinAction mirror).
    void ProcessPendingGroupBinds(uint32 diff)
    {
        for (auto itr = clusterPendingGroupBinds.begin(); itr != clusterPendingGroupBinds.end();)
        {
            itr->delay -= int32(diff);
            if (itr->delay > 0)
            {
                ++itr;
                continue;
            }

            Player* bot = ObjectAccessor::FindPlayer(ObjectGuid::Create<HighGuid::Player>(itr->guid));
            if (bot && bot->GetSession() && bot->GetSession()->IsBot())
            {
                if (Group* group = bot->GetGroup())
                    if (Player* anchor = FindLocalGroupAnchor(group))
                        QueueGroupAnchor(group, anchor, false);
            }

            itr = clusterPendingGroupBinds.erase(itr);
        }
    }

    void ProcessPendingBGJoins(uint32 diff)
    {
        std::vector<ClusterPendingBGJoin> joins;
        {
            std::lock_guard<std::mutex> lock(clusterPendingBGMutex);
            if (clusterPendingBGJoins.empty())
                return;
            joins.swap(clusterPendingBGJoins);
        }

        std::vector<ClusterPendingBGJoin> keep;
        for (ClusterPendingBGJoin& join : joins)
        {
            join.delay -= int32(diff);
            if (join.delay > 0)
            {
                keep.push_back(join);
                continue;
            }

            Player* bot = ObjectAccessor::FindPlayer(ObjectGuid::Create<HighGuid::Player>(join.guid));
            if (!bot || !bot->GetSession() || !bot->GetSession()->IsBot() || bot->InBattleground())
                continue;

            Battleground* bg = sBattlegroundMgr->GetBattleground(join.instanceId, BATTLEGROUND_TYPE_NONE);
            if (!bg)
            {
                // The local instance is created by the matchmaking's
                // StartBattleground call, which can land after the invite.
                if (--join.attemptsLeft > 0)
                {
                    join.delay = CLUSTER_BG_JOIN_RETRY_MS;
                    keep.push_back(join);
                }
                else
                    LOG_WARN("playerbots", "Cluster: BG instance {} never appeared locally, bot {} stays out",
                             join.instanceId, bot->GetName());
                continue;
            }

            BattlegroundTypeId bgTypeId = BattlegroundTypeId(join.bgTypeId);

            LOG_INFO("playerbots", "Cluster: bot {} force-joins BG type {} instance {}",
                     bot->GetName(), join.bgTypeId, join.instanceId);

            bot->SetEntryPoint();
            bot->SetBattlegroundId(bg->GetInstanceID(), bg->GetBgTypeID(), 1, true,
                                   bgTypeId == BATTLEGROUND_RB, bot->GetTeamId(true));
            sBattlegroundMgr->SendToBattleground(bot, bg->GetInstanceID(), bgTypeId);

            if (PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot))
            {
                WorldPacket emptyPacket;
                bot->GetSession()->HandleCancelMountAuraOpcode(emptyPacket);

                botAI->ResetStrategies(false);
                if (!bot->GetBattleground())
                    botAI->ChangeStrategy("+bg", BOT_STATE_NON_COMBAT);

                AiObjectContext* context = botAI->GetAiObjectContext();
                context->GetValue<uint32>("bg role")->Set(urand(0, 9));
                PositionMap& posMap = context->GetValue<PositionMap&>("position")->Get();
                PositionInfo pos = posMap["bg objective"];
                pos.Reset();
                posMap["bg objective"] = pos;
            }

            if (join.notifyMatchmaking)
            {
                // Blocking gRPC call: keep it off the world thread.
                uint64 guidCounter = join.guid;
                uint32 instanceId = join.instanceId;
                std::thread([guidCounter, instanceId]() {
                    if (!sToCloud9Sidecar->NotifyPlayerJoinedBattleground(guidCounter, instanceId))
                        LOG_WARN("playerbots", "Cluster: PlayerJoinedBattleground failed for bot guid {}", guidCounter);
                }).detach();
            }
        }

        if (!keep.empty())
        {
            std::lock_guard<std::mutex> lock(clusterPendingBGMutex);
            clusterPendingBGJoins.insert(clusterPendingBGJoins.end(), keep.begin(), keep.end());
        }
    }

    void ProcessPendingLogins(uint32 diff)
    {
        for (auto itr = clusterPendingLogins.begin(); itr != clusterPendingLogins.end();)
        {
            itr->delay -= int32(diff);
            if (itr->delay > 0)
            {
                ++itr;
                continue;
            }

            ObjectGuid guid = ObjectGuid::Create<HighGuid::Player>(itr->guid);
            if (sToCloud9Sidecar->IsMapAssigned(itr->mapId) && !ObjectAccessor::FindPlayer(guid))
            {
                LOG_INFO("playerbots", "Cluster: logging in handed-off bot guid {} for map {}", itr->guid, itr->mapId);
                sRandomPlayerbotMgr.AddPlayerBot(guid, 0);
                clusterPendingGroupBinds.push_back({itr->guid, int32(CLUSTER_GROUP_BIND_DELAY_MS)});
            }

            itr = clusterPendingLogins.erase(itr);
        }
    }
};

// Chantier C-DJ: bots must walk into the instance behind their master, like
// vanilla. The vanilla relay (PlayerbotMgr::HandleMasterIncomingPacket, fed
// by PlayerbotsServerScript) forwards the master's CMSG_AREATRIGGER to every
// random bot whose master POINTER matches — brittle in cluster, where the
// master's Player object is recreated on every shard switch. Relay through
// the local group mirror instead, skipping bots the vanilla loop already
// covered so the packet is delivered exactly once.
class PlayerbotsClusterServerScript : public ServerScript
{
public:
    PlayerbotsClusterServerScript() : ServerScript("PlayerbotsClusterServerScript", {
        SERVERHOOK_CAN_PACKET_RECEIVE
    }) {}

    void OnPacketReceived(WorldSession* session, WorldPacket const& packet) override
    {
        if (packet.GetOpcode() != CMSG_AREATRIGGER)
            return;

        if (!sPlayerbotAIConfig.enabled || !sToCloud9Sidecar->ClusterModeEnabled())
            return;

        Player* player = session->GetPlayer();
        if (!player || session->IsBot())
            return;

        Group* group = player->GetGroup();
        if (!group)
            return;

        bool masterMgrRelayed = GET_PLAYERBOT_MGR(player) != nullptr;
        uint32 covered = 0;
        uint32 relayed = 0;
        for (Group::MemberSlot const& slot : group->GetMemberSlots())
        {
            if (slot.guid == player->GetGUID())
                continue;

            Player* member = ObjectAccessor::FindPlayer(slot.guid);
            if (!member || !member->GetSession() || !member->GetSession()->IsBot())
                continue;

            PlayerbotAI* botAI = GET_PLAYERBOT_AI(member);
            if (!botAI)
                continue;

            if (masterMgrRelayed && botAI->GetMaster() == player)
            {
                ++covered;  // vanilla relay already delivered this packet
                continue;
            }

            botAI->HandleMasterIncomingPacket(packet);
            ++relayed;
        }

        if (covered || relayed)
            LOG_INFO("playerbots", "Cluster: area trigger from {}: {} bots on vanilla relay, {} relayed via group",
                     player->GetName(), covered, relayed);
    }
};

// Cluster equivalent of the post-accept block in AcceptInvitationAction:
// behind the gateway, bots never receive SMSG_GROUP_INVITE, they join
// through the group service and the local mirror (Group::AddMember fires
// this hook on the world thread). Without it the bot is linked to the
// group but keeps its random strategies (grind/travel) and never follows.
class PlayerbotsClusterGroupScript : public GroupScript
{
public:
    PlayerbotsClusterGroupScript() : GroupScript("PlayerbotsClusterGroupScript", {
        GROUPHOOK_ON_ADD_MEMBER,
        GROUPHOOK_ON_REMOVE_MEMBER,
        GROUPHOOK_ON_DISBAND
    }) {}

    void OnAddMember(Group* group, ObjectGuid guid) override
    {
        if (!sPlayerbotAIConfig.enabled || !sToCloud9Sidecar->ClusterModeEnabled())
            return;

        // Whichever real player this shard hosts speaks for the group. The
        // previous version keyed on the group leader and bailed when it was a
        // bot, which is the normal shape of an LFG group -- so none of this
        // ran for the case it was written for.
        Player* anchor = FindLocalGroupAnchor(group);

        Player* bot = ObjectAccessor::FindPlayer(guid);

        // The member is not in this process. If we host a real player from the
        // group, tell the shard that does host it where to send it. Without
        // this the group forms (member.added reaches every shard over NATS)
        // but the player is left alone, which is indistinguishable from the
        // bots simply not working.
        if (!bot)
        {
            if (anchor)
                QueueGroupAnchor(group, anchor, true);

            return;
        }

        // A real player joined a group we host. Broadcast where they are so
        // the shards holding the other members bring them over.
        if (!bot->GetSession() || !bot->GetSession()->IsBot())
        {
            QueueGroupAnchor(group, bot, true);
            return;
        }

        PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot);
        if (!botAI)
            return;

        // No real player here: either the group is all bots (vanilla
        // behaviour) or the human is on another shard and will send an anchor.
        if (!anchor || anchor == bot)
            return;

        // Alt bots keep their owner as master (vanilla AcceptInvitationAction
        // only rebinds the master for random bots), so BindBotToAnchor is a
        // no-op for them unless the anchor already is their owner.
        if (!sRandomPlayerbotMgr.IsRandomBot(bot) && botAI->GetMaster() != anchor)
            return;

        BindBotToAnchor(bot, anchor, group);
        botAI->TellMaster("Hello");

        // The bot is with us but the group may already be somewhere else (the
        // human joined, then zoned). Re-broadcast so it catches up.
        QueueGroupAnchor(group, anchor, true);
    }

    // A client "disband" is a Leave of the player (WoW semantics): the group
    // survives while >= 2 bots remain, stranding the alts grouped together
    // and unable to be re-invited (BUG-027). When the removed member is the
    // owner of local alt bots still in the group, make each alt leave through
    // the group service; their own removal (or the final disband) then puts
    // them back on follow.
    void OnRemoveMember(Group* group, ObjectGuid guid, RemoveMethod /*method*/,
                        ObjectGuid /*kicker*/, char const* /*reason*/) override
    {
        if (!sPlayerbotAIConfig.enabled || !sToCloud9Sidecar->ClusterModeEnabled())
            return;

        // The removed member is one of our local alt bots (owner uninvite or
        // our own GroupLeave below): resume following its owner.
        if (Player* bot = ObjectAccessor::FindPlayer(guid))
        {
            if (bot->GetSession() && bot->GetSession()->IsBot() && !sRandomPlayerbotMgr.IsRandomBot(bot))
            {
                ResumeFollowingOwner(bot);
                return;
            }
        }
        else
            // BUG-030: one alt missed its release with no trace; log the only
            // path where the removed member itself is unreachable.
            LOG_INFO("playerbots", "Cluster: removed member {} of group {} not found locally",
                     guid.GetCounter(), group->GetGUID().GetCounter());

        std::vector<uint64> altsToLeave;
        for (Group::MemberSlot const& slot : group->GetMemberSlots())
        {
            if (slot.guid == guid)
                continue;

            Player* bot = ObjectAccessor::FindPlayer(slot.guid);
            if (!bot || !bot->GetSession() || !bot->GetSession()->IsBot() ||
                sRandomPlayerbotMgr.IsRandomBot(bot))
                continue;

            PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot);
            if (!botAI || !botAI->GetMaster() || botAI->GetMaster()->GetGUID() != guid)
                continue;

            LOG_INFO("playerbots", "Cluster: owner left group {}, alt bot {} leaves too",
                     group->GetGUID().GetCounter(), bot->GetName());

            altsToLeave.push_back(bot->GetGUID().GetCounter());
        }

        if (altsToLeave.empty())
            return;

        // Blocking gRPC calls: keep them off the world thread, and SEQUENTIAL
        // on purpose - concurrent Leave calls race in the group service
        // (double disband panic, lost member removals). The last leave can
        // come back "group not found" once the service disbands the group
        // under 2 members; that's expected.
        std::thread([altsToLeave]() {
            for (uint64 altGuid : altsToLeave)
                sToCloud9Sidecar->GroupLeave(altGuid);
        }).detach();
    }

    // Catch-all: the group service disbands the group once it falls under 2
    // members; free every local alt bot still linked to it.
    void OnDisband(Group* group) override
    {
        if (!sPlayerbotAIConfig.enabled || !sToCloud9Sidecar->ClusterModeEnabled())
            return;

        for (Group::MemberSlot const& slot : group->GetMemberSlots())
        {
            Player* bot = ObjectAccessor::FindPlayer(slot.guid);
            if (bot && bot->GetSession() && bot->GetSession()->IsBot() &&
                !sRandomPlayerbotMgr.IsRandomBot(bot))
                ResumeFollowingOwner(bot);
        }
    }

private:
    static void ResumeFollowingOwner(Player* bot)
    {
        PlayerbotAI* botAI = GET_PLAYERBOT_AI(bot);
        if (!botAI)
        {
            LOG_WARN("playerbots", "Cluster: alt bot {} freed from group but has no AI", bot->GetName());
            return;
        }

        if (!botAI->GetMaster())
        {
            // BUG-030: the master pointer can be transiently null when the
            // removal lands; rebind it through the owner's real session
            // (alt bots share the owner's account, bot sessions are not in
            // the session map so this always yields the real player).
            if (WorldSession* ownerSession = sWorldSessionMgr->FindSession(bot->GetSession()->GetAccountId()))
            {
                Player* owner = ownerSession->GetPlayer();
                if (owner && owner->IsInWorld())
                {
                    LOG_INFO("playerbots", "Cluster: alt bot {} freed from group with no master, rebinding to {}",
                             bot->GetName(), owner->GetName());
                    botAI->SetMaster(owner);
                }
            }
        }

        if (!botAI->GetMaster())
        {
            // Owner unreachable on this shard: reset anyway, the next
            // invite rebinds the follow.
            LOG_WARN("playerbots", "Cluster: alt bot {} freed from group but has no master, resetting strategies only",
                     bot->GetName());
            botAI->ResetStrategies();
            botAI->Reset();
            return;
        }

        LOG_INFO("playerbots", "Cluster: alt bot {} freed from group, following {} again",
                 bot->GetName(), botAI->GetMaster()->GetName());

        botAI->ResetStrategies();
        botAI->ChangeStrategy("+follow", BOT_STATE_NON_COMBAT);
        botAI->Reset();
    }
};

// Chantier C-BG.5: a participant leaving a running battleground (human quit,
// bot yanked out) shrinks its team below MinPlayersPerTeam and AC schedules
// the "not enough players" premature end. Refill the short team with local
// random bots through the C-BG.1 force-join path (queue bypassed: the bots
// join the running instance directly).
class PlayerbotsClusterBGScript : public AllBattlegroundScript
{
public:
    PlayerbotsClusterBGScript() : AllBattlegroundScript("PlayerbotsClusterBGScript", {
        ALLBATTLEGROUNDHOOK_ON_BATTLEGROUND_REMOVE_PLAYER_AT_LEAVE
    }) {}

    void OnBattlegroundRemovePlayerAtLeave(Battleground* bg, Player* player) override
    {
        if (!sPlayerbotAIConfig.enabled || !sToCloud9Sidecar->ClusterModeEnabled())
            return;

        if (!bg || !bg->isBattleground() || bg->GetStatus() != STATUS_IN_PROGRESS)
            return;

        // The hook runs after the leaver's bg data reset: use the natural
        // faction (no cross-faction battlegrounds on 3.3.5).
        TeamId team = player->GetTeamId(true);
        if (team > TEAM_HORDE)
            return;

        uint32 have = bg->GetPlayersCountByTeam(team);
        uint32 minPerTeam = bg->GetMinPlayersPerTeam();
        if (have >= minPerTeam)
            return;

        uint32 need = minPerTeam - have;
        uint32 scheduled = 0;

        std::lock_guard<std::mutex> lock(clusterPendingBGMutex);
        for (auto it = sRandomPlayerbotMgr.GetPlayerBotsBegin();
             need && it != sRandomPlayerbotMgr.GetPlayerBotsEnd(); ++it)
        {
            Player* bot = it->second;
            if (!bot || !bot->IsInWorld() || !bot->GetSession() || !bot->GetSession()->IsBot() ||
                !sRandomPlayerbotMgr.IsRandomBot(bot))
                continue;

            if (bot->GetGroup() || bot->InBattleground() || bot->InBattlegroundQueue() || !bot->IsAlive())
                continue;

            if (bot->GetTeamId() != team)
                continue;

            uint32 level = bot->GetLevel();
            if (level < bg->GetMinLevel() || level > bg->GetMaxLevel())
                continue;

            ObjectGuid::LowType guidLow = bot->GetGUID().GetCounter();
            if (clusterBGQueuedBots.count(guidLow))
                continue;

            bool alreadyPending = false;
            for (ClusterPendingBGJoin const& pending : clusterPendingBGJoins)
            {
                if (pending.guid == guidLow)
                {
                    alreadyPending = true;
                    break;
                }
            }
            if (alreadyPending)
                continue;

            clusterPendingBGJoins.push_back({guidLow, uint32(bg->GetBgTypeID()), bg->GetInstanceID(),
                                             CLUSTER_BG_JOIN_ATTEMPTS, 0, false});
            --need;
            ++scheduled;
        }

        LOG_INFO("playerbots", "Cluster: backfilling BG instance {} team {} with {} bots ({} still short)",
                 bg->GetInstanceID(), uint32(team), scheduled, need);
    }
};

void AddPlayerbotsClusterScripts()
{
    new PlayerbotsClusterPlayerScript();
    new PlayerbotsClusterWorldScript();
    new PlayerbotsClusterGroupScript();
    new PlayerbotsClusterServerScript();
    new PlayerbotsClusterBGScript();
}
