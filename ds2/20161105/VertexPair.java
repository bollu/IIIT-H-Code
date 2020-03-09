import java.io.*; 
import java.util.*;

class VertexPair implements Serializable, Comparable<VertexPair> {
    int u, v, w;

    public VertexPair() {};
    public VertexPair(int u, int v, int w) {
        this.u = u; this.v = v; this.w = w;
    }
    @Override
    public int compareTo(VertexPair a) {
        if (this.w < a.w) return -1;
        else if (this.w == a.w) return 0;
        return 1;
    }

}
