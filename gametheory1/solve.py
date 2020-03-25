#!/usr/bin/env python2.7
import gambit
import sys
import pulp
import numpy as np
import itertools
import copy

def is_list_sorted(l):
    return all(l[i] <= l[i + 1] for i in range(len(l) - 1)) 


class Game:
    def __init__(self, in_param):
        if isinstance(in_param, gambit.Game):
            self._from_gambit(in_param)
        else:
            assert isinstance(in_param, Game)
            self._from_Game(in_param)
    
    def _from_Game(self, game):
        assert isinstance(game, Game)
        self.nplayers = copy.deepcopy(game.nplayers)
        self.full_outcomes = np.copy(game.full_outcomes)
        self.full_outcomes.setflags(write=False)
        self.cur_outcomes = np.copy(game.cur_outcomes)
        self.player2strats = copy.deepcopy(game.player2strats)

    def _from_gambit(self, game):
        assert isinstance(game, gambit.Game)
        self.nplayers = len(game.players)
        # table of outcomes: #strat(P1) x #strat(P2) x .. x #strat(Pn) -> |Players|
        # table of outcomes: |Players| x #strat(P1) x #strat(P2) x .. x #strat(Pn)
        nstrats = [len(p.strategies) for p in game.players]
        self.full_outcomes = np.empty([len(game.players)] + nstrats)

        for strategy_profile in itertools.product(*[range(player_nstrats) for player_nstrats in nstrats]):
            for p in range(len(game.players)):
                self.full_outcomes[p][strategy_profile] =  game[strategy_profile][p]
        # make data read-only
        self.full_outcomes.setflags(write=False)

        # a mutable copy of the full outcomes array
        self.cur_outcomes = np.copy(self.full_outcomes)

        self.player2strats = {}
        for p in range(self.nplayers):
            # map player to column indexes of their strategies
            self.player2strats[p] = list(range(nstrats[p]))

    def nstrats_for_player(self, playerid):
        return len(self.player2strats[playerid])

    def arr_nstrats(self):
        """returns arr where arr_nstrats()[i] == #strats for player i"""
        return [self.nstrats_for_player(p) for p in range(self.nplayers)]

    def get_player_strat_ids(self, playerid):
        return copy.deepcopy(self.player2strats[playerid])

    def arr_unique_strat(self):
        assert np.product(self.arr_nstrats()) == 1
        return [self.player2strats[playerid][0] for playerid in range(self.nplayers)]


    def get_player_strat(self, playerid, stratid):
        assert isinstance (playerid, int)
        assert isinstance (stratid, int)
        assert stratid in self.player2strats[playerid]
        ixs = [playerid] + [slice(None) for _ in range(self.nplayers)]
        ixs[playerid+1] = self._stratid_to_arrix(playerid, stratid)
        return self.cur_outcomes[ixs]


    def remove_player_strat(self, playerid, stratid):
        assert isinstance (playerid, int)
        assert isinstance (stratid, int)
        assert stratid in self.player2strats[playerid]
        print("self.player2strats(before): %s" % self.player2strats)
        self.player2strats[playerid].remove(stratid)
        print("self.player2strats(after): %s" % self.player2strats)

        # recompute outcomes here
        self.cur_outcomes = self._outcomes_from_full_outcomes()


    def _stratid_to_arrix(self, playerid, stratid):
        assert stratid in self.player2strats[playerid]
        assert is_list_sorted(self.player2strats[playerid])
        return self.player2strats[playerid].index(stratid)

    def _strat_profile_to_arrixs(self, profile):
        assert isinstance(profile, tuple)

        ixs = []
        for p in range(self.nplayers):
            ixs.append(self._stratid_to_arrix(p, profile[p]))
        return tuple(ixs)

    def _outcomes_from_full_outcomes(self):
        """
        table of outcomes: 
        - #strat(P1) x #strat(P2) x .. x #strat(Pn) -> |Players|
        - |Players| x #strat(P1) x #strat(P2) x .. x #strat(Pn)
        """
        os = np.empty([self.nplayers] + self.arr_nstrats())
        for strategy_profile in itertools.product(*[self.player2strats[p] for p in range(self.nplayers)]):
            # print(self.full_outcomes.shape, os.shape)
            for p in range(self.nplayers):
                os[p][self._strat_profile_to_arrixs(strategy_profile)] =  \
                    self.full_outcomes[p][strategy_profile]
        return os

    def outcomes(self):
        reference = self._outcomes_from_full_outcomes()
        assert np.all(reference == self.cur_outcomes)
        return self.cur_outcomes

    def print_outcomes(self):
        """print outcomes as a string"""
        os = self.outcomes()
        nstrats = os.shape[1:]
        for strategy_profile in itertools.product(*[range(player_nstrats) for player_nstrats in nstrats]):
            # index array as x[..., strategy_profile]
            print("outcomes[strat=%s] = %s" % (strategy_profile, os[(Ellipsis,) + strategy_profile]))




def mk_outcomes_array(game):
    # number of strategies for each player
    nstrats = [len(p.strategies) for p in game.players]
    # table of outcomes: #strat(P1) x #strat(P2) x .. x #strat(Pn) -> |Players|
    # table of outcomes: |Players| x #strat(P1) x #strat(P2) x .. x #strat(Pn)
    outcomes = np.empty([len(game.players)] + nstrats)

    for strategy_profile in itertools.product(*[range(player_nstrats) for player_nstrats in nstrats]):
        for p in range(len(game.players)):
            outcomes[p][strategy_profile] =  game[strategy_profile][p]
    return outcomes

def print_outcomes(os):
    nstrats = os.shape[1:]
    for strategy_profile in itertools.product(*[range(player_nstrats) for player_nstrats in nstrats]):
        # index array as x[..., strategy_profile]
        print("outcomes[strat=%s] = %s" % (strategy_profile, os[(Ellipsis,) + strategy_profile]))


# create a way to index the outcomes array for:
# - player=playerid
# - strategy=stratid
def mkindex_player_strat(nplayers, playerid, stratid):
    assert isinstance (nplayers, int)
    assert isinstance (playerid, int)
    assert isinstance (stratid, int)
    ixs = [playerid] + [slice(None) for _ in range(nplayers)]
    ixs[playerid+1] = stratid
    ixs = tuple(ixs)
    return ixs


def iterate_strong_dominance(game, playerid, iteration=0): 
    """
    Return list containing the unique strongly dominant strategy
    Return empty list if not found
    """
    print("##iteration: |%s| computing iterated STRONG dominance for player: |%s| of |%s|##" % 
            (iteration, playerid, game.nplayers))
    # assert isinstance(os, np.array)
    assert isinstance(playerid, int)
    assert (playerid < game.nplayers)

    # we have found the dominant strategy
    if np.product(game.arr_nstrats()) == 1: 
        return [game.arr_unique_strat()]

    # number of strategies for player
    n_player_strats = game.nstrats_for_player(playerid)
    print("n_player_strats: %s" % n_player_strats)

    for cur_strat_id in game.get_player_strat_ids(playerid):
        cur_strat =  game.get_player_strat(playerid, cur_strat_id)

        strongly_dominated = False
        for other_strat_id in game.get_player_strat_ids(playerid):
            if other_strat_id == cur_strat_id: continue # skip ourselves

            other_strat =  game.get_player_strat(playerid, other_strat_id)
            cur_lt_other = cur_strat < other_strat

            print("player %s: comparing |%s=%s| with |%s=%s|: %s (all=%s)" %
                    (playerid, 
                     cur_strat_id, cur_strat, 
                     other_strat_id, other_strat,
                     cur_lt_other,
                     np.all(cur_lt_other)))

            # if strongly dominated, quit
            if np.all(cur_lt_other):  strongly_dominated = True; break

    if strongly_dominated:
        print("--")
        print("strategy |%s| for player |%s| is strongly_dominated. deleting strategy from outcomes..." % (cur_strat_id, playerid))
        game.print_outcomes()
        game.remove_player_strat(playerid, cur_strat_id)
        print("pruned outcomes: ")
        game.print_outcomes()
        print("--")
        return iterate_strong_dominance(game, (playerid+1) % game.nplayers, iteration+1)
    else:
        print ("##WARNING: unable to find strongly dominated strategy for player |%s|!##" % (playerid))
        game.print_outcomes()
        print ("##ENDWARNING##")
        return []



def calc_strong_dominance(game):
    assert isinstance(game, Game)
    game.print_outcomes()
    for p in range(0, game.nplayers):
        sdom = iterate_strong_dominance(game, p)
        if sdom: return sdom
    return []

def iterate_weak_dominance(game, playerid, iteration=0): 
    """
    Return list containing the unique strongly dominant strategy
    Return empty list if not found
    """
    print("##iteration: |%s| computing iterated WEAK dominance for player: |%s| of |%s|##" % 
            (iteration, playerid, game.nplayers))
    # assert isinstance(os, np.array)
    assert isinstance(playerid, int)
    assert (playerid < game.nplayers)

    # we have found the dominant strategy
    if np.product(game.arr_nstrats()) == 1: 
        return [game.arr_unique_strat()]

    # number of strategies for player
    n_player_strats = game.nstrats_for_player(playerid)
    print("n_player_strats: %s" % n_player_strats)

    strats_list = []

    for cur_strat_id in game.get_player_strat_ids(playerid):
        cur_strat =  game.get_player_strat(playerid, cur_strat_id)

        for other_strat_id in game.get_player_strat_ids(playerid):
            if other_strat_id == cur_strat_id: continue # skip ourselves

            other_strat =  game.get_player_strat(playerid, other_strat_id)
            cur_lt_other = np.all(cur_strat <= other_strat) and not np.all(cur_strat == other_strat)

            print("player %s: comparing |%s=%s| with |%s=%s|: %s (all=%s)" %
                    (playerid, 
                     cur_strat_id, cur_strat, 
                     other_strat_id, other_strat,
                     cur_lt_other,
                     np.all(cur_lt_other)))

            # if strongly dominated
            if cur_lt_other:
                gamecur = Game(game)
                gamecur.remove_player_strat(playerid, cur_strat_id)
                strats_list.extend(iterate_weak_dominance(gamecur, (playerid+1) % gamecur.nplayers))

        return strats_list
    else:
        print ("##WARNING: unable to find weakly dominated strategy for player |%s|!##" % (playerid))
        game.print_outcomes()
        print ("##ENDWARNING##")
        return  []


def calc_weak_dominances(game):
    assert isinstance(game, Game)
    game.print_outcomes()
    strats = []

    for p in range(0, game.nplayers):
        strats.extend(iterate_weak_dominance(game, p))
    return strats

if __name__ == "__main__":
    assert (len(sys.argv) == 3)
    g = gambit.Game.read_game(sys.argv[1])
    game = Game(g)
    allstrats = calc_strong_dominance(game)
    # if we do not have strongly dominant strategy eqm, then use
    # weakly
    allstrats += calc_weak_dominances(game)
    # remove duplicates
    allstrats = [strat for (strat, _) in itertools.groupby(allstrats)]


    print("##ALL STRATEGIES##")
    for (i, strat) in enumerate(allstrats):
        print("STRATEGY %3s | %60s" % (i, list(strat)))
    print("##END ALL STRATEGIES##")

    with open(sys.argv[2], "w") as f:
        if len(allstrats) == 0:
            f.write("No Dominant Strategy Equilibria exist")
        else:
            f.write("%s\n" % len(allstrats))
            for strat in allstrats:
                f.write(" ".join(map(str, strat)))
                f.write("\n")

