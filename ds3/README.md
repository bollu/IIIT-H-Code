# 20161105

## First question

- Spawn `n-1` processes. Have the main process be process `0`. 
- Have process `0` send message that fires off the whole round robin. Each
  process receives an output file handle, the PID of the 0th process, the PID
  of all the other spawned processes, the token, and who sent the process.
  This is enough information to decide who to send the token to text.

## Second question: parallel merge sort

Use `spawn` and `receive` to split at each sort step inside the function
`splitsort`
