/*
 * This file is part of the mod-playerbots module for AzerothCore. See AUTHORS file for Copyright
 * information; released under GNU GPL v2 license, redistribute/modify under version 2 of the License,
 * or (at your option) any later version.
 */

#ifndef PLAYERBOTS_VEHICLECOMBATSTRATEGY_H
#define PLAYERBOTS_VEHICLECOMBATSTRATEGY_H

#include "Strategy.h"

class PlayerbotAI;

/// Lets a crewed vehicle fight anywhere, not only in the battlegrounds whose strategies name each weapon by hand.
class VehicleCombatStrategy : public Strategy
{
public:
    VehicleCombatStrategy(PlayerbotAI* botAI) : Strategy(botAI) {}

    void InitTriggers(std::vector<TriggerNode*>& triggers) override;
    std::string const getName() override { return "vehicle combat"; }
};

#endif
