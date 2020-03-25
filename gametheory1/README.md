# Installation

- We use `python2.7` since that's the latest version of python Gambit
  supports (Gambit version 16.0.1).
- First, install [Gambit from source](https://gambitproject.readthedocs.io/en/latest/build.html#building-from-git-repository) 
  and the associated python bindings for `2.7`

# Algorithm: Strongly Dominant strategy

For strongly dominant strategies, we implement iterated dominance where we find
a dominated row and then elimiate it. We keep doing this till we end
with a single row.


```py
def iterate_strong_dominance(game, playerid, iteration=0): 
    ...
    # we have a single strategy
    if np.product(game.arr_nstrats()) == 1: 
        return [game.arr_unique_profile()]
    ...
    for cur_strat_id in game.get_player_strat_ids(playerid):
        cur_outcome =  game.get_player_subgame(playerid, cur_strat_id)

        strongly_dominated = False
        for other_strat_id in game.get_player_strat_ids(playerid):
            if other_strat_id == cur_strat_id: continue # skip ourselves

            other_outcome =  game.get_player_subgame(playerid, other_strat_id)
            cur_lt_other = cur_outcome < other_outcome
            ...
            # if strongly dominated, quit
            if np.all(cur_lt_other): strongly_dominated = True; break

    if strongly_dominated:
        ...
        game.remove_player_strat(playerid, cur_strat_id)
        ...
        return iterate_strong_dominance(game, (playerid+1) % game.nplayers, iteration+1)
    else:
        ...
        return []
```


# Algorithm: Weakly Dominant strategy

Since weakly dominant strategies cannot be detected by elimination,
we perform the expected brute-force search through the search space. We
iterate over all profiles, and check that the profile is "as good"
as every other profile, and is "strictly better"  than at least
one profile.

```py
def calc_weakly_dominant_exhaustive_search(game):
    # iterate over all possible strategies for all possible players
    weakdom = []
    for profile_cur in game.strategy_profiles():
        outcome_cur = game.get_outcome_for_profile(profile_cur) 

        strictly_better = False
        at_least_as_good = True
        for profile_other in game.strategy_profiles():
            if profile_cur == profile_other: continue
            outcome_other = game.get_outcome_for_profile(profile_other)

            at_least_as_good = at_least_as_good and np.all(outcome_cur >= outcome_other)
            strictly_better = strictly_better or np.any(outcome_cur > outcome_other)

            if not (at_least_as_good): break

        if at_least_as_good and strictly_better:
            weakdom.append(profile_cur)
    return weakdom
```



- 
