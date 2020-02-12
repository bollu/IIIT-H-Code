import java.io.*; 

class VertexPair implements Serializable {
    int u, v, w;

    public VertexPair() {};
    public VertexPair(int u, int v, int w) {
        this.u = u; this.v = v; this.w = w;
    }
}
