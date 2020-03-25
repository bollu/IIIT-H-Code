#!/usr/bin/env python2.7
import gambit
import sys
import pulp
import numpy as np
import itertools
import copy

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

    def arr_unique_strat(self):
        assert np.product(self.arr_nstrats()) == 1
        return [self.player2strats[playerid][0] for playerid in range(self.nplayers)]


    def get_player_strat(self, playerid, stratix):
        assert isinstance (playerid, int)
        assert isinstance (stratix, int)
        assert stratix < len(self.player2strats[playerid])
        ixs = [playerid] + [slice(None) for _ in range(self.nplayers)]
        ixs[playerid+1] = self.player2strats[playerid][stratix]
        ixs = tuple(ixs)
        return self.cur_outcomes[ixs]

    def remove_player_strat(self, playerid, stratix):
        assert isinstance (playerid, int)
        assert isinstance (stratix, int)
        assert stratix < len(self.player2strats[playerid])
        del self.player2strats[playerid][stratix]

        # recompute outcomes here
        self.cur_outcomes = self._outcomes_from_full_outcomes()


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
                os[p][strategy_profile] =  self.full_outcomes[p][strategy_profile]
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
# - strategy=stratix
def mkindex_player_strat(nplayers, playerid, stratix):
    assert isinstance (nplayers, int)
    assert isinstance (playerid, int)
    assert isinstance (stratix, int)
    ixs = [playerid] + [slice(None) for _ in range(nplayers)]
    ixs[playerid+1] = stratix
    ixs = tuple(ixs)
    return ixs


def old_iterate_strong_dominance(os, playerid): 
    # assert isinstance(os, np.array)
    assert isinstance(playerid, int)
    # number of strategies for each player
    nplayers = os.shape[0]
    nstrats = os.shape[1:]

    # number of strategies for player
    n_player_strats = nstrats[playerid]
    print("n_player_strats: %s" % n_player_strats)

    for cur_strat_ix in range(n_player_strats):
        cur_strat =  os[mkindex_player_strat(nplayers, playerid, cur_strat_ix)]

        strongly_dominated = False
        for other_strat_ix in range(n_player_strats):
            if other_strat_ix == cur_strat_ix: continue # skip ourselves

            other_strat =  os[mkindex_player_strat(nplayers, playerid, other_strat_ix)]
            cur_lt_other = cur_strat < other_strat

            print("player %s: comparing |%s=%s| with |%s=%s|: %s (all=%s)" %
                    (playerid, 
                     cur_strat_ix, cur_strat, 
                     other_strat_ix, other_strat,
                     cur_lt_other,
                     np.all(cur_lt_other)))

            # if strongly dominated, quit
            if np.all(cur_lt_other):  strongly_dominated = True; break

        if strongly_dominated:
            print("--")
            print("strategy |%s| for player |%s| is strongly_dominated. deleting strategy from outcomes..." % (cur_strat_ix, playerid))
            print(os)
            os =  remove_player_strat(os, playerid, cur_strat_ix)
            print("pruned outcomes: ")
            print(os)
            print("--")
                

        # index = 
        # print("---")
        # print("os[player=%s, strat=%s] :: %s:" % (playerid, strat_ix, index))
        # print("%s" % os[index])
        # print("---")

def iterate_strong_dominance(game, playerid): 
    """
    Return list containing the unique strongly dominant strategy
    Return empty list if not found
    """
    print("computing iterated strong dominance for player: |%s|" % playerid)
    # assert isinstance(os, np.array)
    assert isinstance(playerid, int)
    assert (playerid < game.nplayers)

    # we have found the dominant strategy
    if np.product(game.arr_nstrats()) == 1: 
        return [game.arr_unique_strat()]

    # number of strategies for player
    n_player_strats = game.nstrats_for_player(playerid)
    print("n_player_strats: %s" % n_player_strats)

    for cur_strat_ix in range(n_player_strats):
        cur_strat =  game.get_player_strat(playerid, cur_strat_ix)

        strongly_dominated = False
        for other_strat_ix in range(n_player_strats):
            if other_strat_ix == cur_strat_ix: continue # skip ourselves

            other_strat =  game.get_player_strat(playerid, other_strat_ix)
            cur_lt_other = cur_strat < other_strat

            print("player %s: comparing |%s=%s| with |%s=%s|: %s (all=%s)" %
                    (playerid, 
                     cur_strat_ix, cur_strat, 
                     other_strat_ix, other_strat,
                     cur_lt_other,
                     np.all(cur_lt_other)))

            # if strongly dominated, quit
            if np.all(cur_lt_other):  strongly_dominated = True; break

    if strongly_dominated:
        print("--")
        print("strategy |%s| for player |%s| is strongly_dominated. deleting strategy from outcomes..." % (cur_strat_ix, playerid))
        game.print_outcomes()
        game.remove_player_strat(playerid, cur_strat_ix)
        print("pruned outcomes: ")
        game.print_outcomes()
        print("--")
        return iterate_strong_dominance(game, (playerid+1) % game.nplayers)
    else:
        print ("##WARNING: unable to find strongly dominated strategy for player |%s|!##" % (playerid))
        game.print_outcomes()
        print ("##ENDWARNING##")
        return []



def calc_strong_dominance(game):
    assert isinstance(game, Game)
    game.print_outcomes()
    return iterate_strong_dominance(game, 0)

def iterate_weak_dominance(game, playerid): 
    """
    Return list containing the unique strongly dominant strategy
    Return empty list if not found
    """
    print("computing iterated weak dominance for player: |%s|" % playerid)
    # assert isinstance(os, np.array)
    assert isinstance(playerid, int)
    assert (playerid < game.nplayers)

    # we have found the dominant strategy
    if np.product(game.arr_nstrats()) == 1: 
        yield game.arr_unique_strat()

    # number of strategies for player
    n_player_strats = game.nstrats_for_player(playerid)
    print("n_player_strats: %s" % n_player_strats)

    for cur_strat_ix in range(n_player_strats):
        cur_strat =  game.get_player_strat(playerid, cur_strat_ix)

        strongly_dominated = False
        for other_strat_ix in range(n_player_strats):
            if other_strat_ix == cur_strat_ix: continue # skip ourselves

            other_strat =  game.get_player_strat(playerid, other_strat_ix)
            cur_lt_other = (cur_strat < other_strat) & (cur_strat != other_strat)

            print("player %s: comparing |%s=%s| with |%s=%s|: %s (all=%s)" %
                    (playerid, 
                     cur_strat_ix, cur_strat, 
                     other_strat_ix, other_strat,
                     cur_lt_other,
                     np.all(cur_lt_other)))

            # if strongly dominated
            if np.all(cur_lt_other):
                gamecur = Game(game)
                gamecur.remove_player_strat(playerid, cur_strat_ix)
                yield iterate_weak_dominance(game, (playerid+1) % game.nplayers)
    else:
        print ("##WARNING: unable to find weakly dominated strategy for player |%s|!##" % (playerid))
        game.print_outcomes()
        print ("##ENDWARNING##")
        return  # this is the same as just "yielding"


def calc_weak_dominances(game):
    assert isinstance(game, Game)
    game.print_outcomes()
    return iterate_weak_dominance(game, 0)

if __name__ == "__main__":
    assert (len(sys.argv) == 3)
    g = gambit.Game.read_game(sys.argv[1])
    game = Game(g)
    allstrats = calc_strong_dominance(game) + list(calc_weak_dominances(game))
    print("allstrats:\n%s" % ("\n".join(map(str, allstrats))))

    with open(sys.argv[2], "w") as f:
        f.write("%s\n" % len(allstrats))
        for strat in allstrats:
            f.write(" ".join(map(str, strat)))

