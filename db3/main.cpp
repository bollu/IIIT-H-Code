// https://iq.opengenus.org/b-tree-search-insert-delete-operations/
// https://www.cs.helsinki.fi/u/mluukkai/tirak2010/B-tree.pdf
// https://www.cs.usfca.edu/~galles/visualization/BPlusTree.html
#include <sstream>
#include <iostream>
#include <fstream>
#include <vector>
#include <assert.h>
using namespace std;

const int TREE_N = 3;

// child[i] < router[i] < child[i+1]
// router only exists _between_ two children.
// C C C
//  R R
struct node {
    bool isleaf;
    vector<int> vals;
    vector<int> routers;
    vector<node *> children;
    node *parent;
    node *sibling;

    node() {
        isleaf = false;
        sibling = nullptr;
        parent = nullptr;
    }

    void check() {
        if (isleaf) { 
            assert(children.size() == 0);
            assert(routers.size() == 0);
        }
        if (!isleaf) { 
            assert(vals.size() == 0);
            assert(children.size() == routers.size() + 1);
            assert(children.size() >= 1);
        }
    }
};

struct btree {
    node *root;
    btree() { root = nullptr; }
};


node *gotoleaf(int k, node *cur) {
    for(int i = 0; i < cur->routers.size(); ++i) {
        if (cur->routers[i] < k) { 
            return gotoleaf(k, cur->children[i]);
        }
    }
    return gotoleaf(k, cur->children[cur->children.size()  -1]);
}

bool find(int k, btree b) {
    node *leaf = gotoleaf(k, b.root);
    
    int i = 1;
    while(i <= leaf->vals.size() && k > leaf->vals[i]) { i++; }
    if (i > leaf->vals.size()) { return false; }
    assert(k <= leaf->vals[i]);
    return k == leaf->vals[i];
};

void insert_recur(int x, btree b, node *n)  {
    if (n->isleaf) {
        if (n->vals.size() < TREE_N) {
            // look for index such that leaf[kloc] <= x.
            // Insert x there to maintain ordering.
            int kloc = 0;
            while (kloc < n->vals.size() && n->vals[kloc] > x) { kloc++; }
            assert(kloc < TREE_N);
            if (kloc < n->vals.size()) { assert(n->vals[kloc] <= x); }

            // shift to make space for x.
            for(int i = n->vals.size() + 1; i >= kloc; i--) { n->vals[i] = n->vals[i-1]; }
            // write x into the correct location
            n->vals[kloc] = x;
        } else {
            // we need to free up space to insert a node. amaze
            node *n2 = new node;
            n2->isleaf = true;

            // rejigger the sibling pointers.
            n2->sibling = n->sibling;
            n->sibling = n2;

            node *p = n->parent;
            assert(p->children.size() != TREE_N);
            n2->parent = p;


            const int split = n->children.size() / 2;

            for (int i = split+1,ix=0; i < n->children.size(); ++i) {
                n2->vals.push_back(n->vals[ix]);
            }

            n->vals.resize(split);

            int childloc = -1;
            for(int i = 0; i < p->children.size(); ++i) {
                if (p->children[i] == n) { childloc = i; break; }
            }
            assert(childloc != -1);
            assert(childloc >= 0);
            assert(childloc < p->children.size());

            p->children.push_back((node *)(0xDEADBEEF));
            for(int i = p->children.size() + 1; i >= childloc + 1;  i--) {
                p->children[i] = p->children[i-1];
            }
                   
            // C0 ||R0 || C1
            //      RNEW  CNEW
            // |
            // x
            p->routers.push_back(-42);
            for(int i = p->routers.size() + 1; i >= childloc;  i--) {
                p->routers[i] = p->routers[i-1];
            }
            p->children[childloc+1] = n2;
            p->routers[childloc] = n->vals[n->vals.size()-1];

        }

    } else {
        assert(!n->isleaf);
        if (n->children.size() == TREE_N) {
            node *left = new node;
            node *right = new node;
            // [0..split] is with n
            // [split+1..total] is with right_child
            const int split = n->children.size() / 2;
            const int splitrouter = n->routers[split];

            // x[split] <= router[split] <= x[split+1]
            // copy elements into right_child
            for (int ix = 0; ix <= split; ++ix) {
                node *child = n->children[ix];
                child->parent = left;
                left->children.push_back(child);
            }
            for (int i = split+1, ix=0; i <= n->children.size(); ++i, ++ix) {
                node *child = n->children[ix];
                child->parent = right;
                right->children.push_back(child);
            }

            // copy routers

            for (int ix = 0; ix <= split-1; ++ix) {
                left->routers.push_back(n->routers[ix]);
            }

            for(int i = split+1,ix=0; i < n->routers.size(); ++i,++ix) {
                right->routers.push_back(n->routers[ix]);
            }

            n->routers.clear();
            n->children.clear();
            n->children[0] = left;
            n->routers[0] = splitrouter;
            n->children[1] = right;
        }

        assert (n->children.size() < TREE_N);


        for (int i = 0; i < n->routers.size(); ++i) {
            if (x < n->routers[i]) {
                return insert_recur(x, b, n->children[i]);
            }
        }
        return insert_recur(x, b, n->children[n->children.size()-1]);
    }
}


void insert(int x, btree b) {
    if (b.root == nullptr) {
        b.root = new node();
        b.root->isleaf = false;
        
        b.root->children.push_back(new node);
        b.root->children[0]->isleaf = true;
        b.root->children[0]->vals.push_back(x);
        b.root->routers.push_back(x);
    } else {
        insert_recur(x, b, b.root);
    }
};

int count(int x, btree b) {};
int range(int x, int y, btree b) {};

int main(int argc, char *argv[]) {
    assert(argc == 2);
    cout << "reading: " << argv[1] << "\n";
    ifstream f; f.open(argv[1], std::ifstream::in);

    btree b;
    std::string l;
    while (getline(f, l)) {
        cout << "str: " << l << "\n";
        std::stringstream ss(l);

        string c; ss >> c;
        cout << "str: " << c << "\n";
        if (c == "INSERT") {
            int x; ss >> x; insert(x, b);
        } else if (c == "FIND") {
            int x; ss >> x; 
            if (find(x, b)) { cout << "YES\n"; } else { cout << "NO\n"; }
        } else if (c == "COUNT") {
            int x; ss >> x; cout << count(x, b) << "\n";
        } else if (c  == "RANGE") {
            int x, y; ss >> x >> y; cout << range(x, y, b) << "\n";
        }
    }
    return 0;
}
