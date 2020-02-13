import java.util.*; 

// Class to represent a node in the graph 
class Node implements Comparator<Node> { 
    public int v, c;
    public Node() {} 
    public Node(int v, int c) { this.v = v; this.c = c; } 
  
    @Override
    public int compare(Node n1, Node n2) 
    { 
        if (n1.c < n2.c) { return -1; } else if (n1.c > n2.c) { return 1; }
        return 0; 
    } 
} 

