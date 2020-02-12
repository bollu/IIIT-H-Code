# SampleI/O
1) Sample Input:

add_graph graph1 4
get_mst graph1
add_edge graph1 1 2 10
add_edge graph1 2 3 15
add_edge graph1 1 3 5
add_edge graph1 4 2 2
add_edge graph1 4 3 40
get_mst graph1

Sample Output:

-1
17

2) Client can send multiple requests. It should end when EOF is received.

