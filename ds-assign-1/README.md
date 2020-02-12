# Quicksort

Decide on the topology: each process attempts to send halves of the
data to child nodes. If no such child exists, perform job themselves.

# Single source shortest path

Use bellman-ford, relax edges in parallel per iteration. Split edges
per process, |E|/n. Gather distances each round.
