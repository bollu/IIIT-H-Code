#!/usr/bin/env python2.7
import gambit
import sys
import pulp
import numpy as np
import itertools

assert (len(sys.argv) == 3)
g = gambit.Game.read_game(sys.argv[1])

# number of strategies for each player
nstrats = [len(p.strategies) for p in g.players]
# table of outcomes: #strat(P1) x #strat(P2) x .. x #strat(Pn) -> |Players|
# table of outcomes: #strat(P1) x #strat(P2) x .. x #strat(Pn) x |Players|
outcomes = np.empty(nstrats + [len(g.players)])

print("nstrats: %s" % nstrats)

for strategy_profile in itertools.product(*[range(pi_nstrats) for pi_nstrats in nstrats]):
    outcomes[strategy_profile] =  list(g[strategy_profile])
    print("outcomes[%s] = %s" % (strategy_profile, outcomes[strategy_profile]))

print("outcomes:\n%s" % outcomes)

