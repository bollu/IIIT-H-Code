#!/usr/bin/env python2.7
import gambit
import sys
import pulp
import numpy as np
import itertools


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

def iterate_strong_dominance(os, playerid): 
    # assert isinstance(os, np.array)
    assert isinstance(playerid, int)
    # number of strategies for each player
    nplayers = os.shape[0]
    nstrats = os.shape[1:]

    # number of strategies for player
    n_player_strats = nstrats[playerid]

    for strat_ix in range(n_player_strats):
        index = mkindex_player_strat(nplayers, playerid, strat_ix)
        print("---")
        print("os[player=%s, strat=%s] :: %s:" % (playerid, strat_ix, index))
        print("%s" % os[index])
        print("---")



def calc_strong_dominance(g):
    os = mk_outcomes_array(g)
    print_outcomes(os)
    iterate_strong_dominance(os, 0)


if __name__ == "__main__":
    assert (len(sys.argv) == 3)
    g = gambit.Game.read_game(sys.argv[1])
    calc_strong_dominance(g)

