import java.io.*; 
import java.util.*;

class VertexPair implements Serializable, Comparator<VertexPair> {
    int u, v, w;

    public VertexPair() {};
    public VertexPair(int u, int v, int w) {
        this.u = u; this.v = v; this.w = w;
    }

    @Override
    public int compare(VertexPair a, VertexPair b) 
    { 
        if (a.w < b.w) { return -1; } else if (a.w > b.w) { return 1; }
        return 0; 
    } 

}
