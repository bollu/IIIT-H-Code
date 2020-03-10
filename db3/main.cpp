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


// child[i] < router[i] (STRICTLY LESS THAN)
// router[i] <= child[i+1]
// child[i] < router[i] <= child[i+1]
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

void printnode(node *n, int depth=0) {
    if (n == nullptr) return;
    n->check();

    for(int i = 0; i < depth; ++i) { cerr << "  " << "|"; }

    if (n->isleaf) {
        cerr << n << "|LEAF: [";
        for(int i = 0; i < n->vals.size(); ++i) {
            cerr << n->vals[i] << " ";
        }
        cerr << "]\n";
    } else {
        cerr << n << "|INTERNAL: [";
        for(int i = 0; i < n->routers.size(); ++i) {
            cerr << "|C:" << n->children[i] << "|R:" << int(n->routers[i]);
        }
        cerr << "|C:" << n->children[n->children.size() - 1];
        cerr << "]\n";

        for(int i =0; i < n->children.size(); ++i) {
            printnode(n->children[i], depth+1);
        }
    }
}


node *gotoleaf(int k, node *cur) {
    cerr << "gotoleaf(" << k << "," << cur << ")\n";
    assert(cur);
    if (cur->isleaf) { return cur; }
    assert(cur->children.size() > 0);

    for(int i = 0; i < cur->routers.size(); ++i) {
        if (k < cur->routers[i]) {
            return gotoleaf(k, cur->children[i]);
        }
    }
    return gotoleaf(k, cur->children[cur->children.size()-1]);
}

bool find(int k, btree &b) {
    if (!b.root) { return false; }

    assert(b.root);
    node *leaf = gotoleaf(k, b.root);
    assert(leaf->isleaf);
    cerr << "find(" << k << ") in leaf: " << leaf << "\n";
    
    for(int i = 0; i < leaf->vals.size(); ++i) {
        if (leaf->vals[i] == k) { return true; }
        // since array is sorted, if our leaf value ever exceeds the key
        // then quit.
        if (leaf->vals[i] > k) { return false; }
    }
    return false;
};

void insert_recur(int x, btree &b, node *n)  {
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
            n->check();
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
            p->check();
            n->check();
            n2->check();
        }

    } else { // for if (n->isleaf)
        assert(!n->isleaf);
        // split case
        if (n->children.size() == TREE_N) {
            node *left = new node;
            node *right = new node;

            left->isleaf = false;
            left->parent = n;
            left->sibling = right;

            right->isleaf = false;
            right->parent = n;

            // [0..split] is with n
            // [split+1..total] is with right_child
            const int split = n->children.size() / 2;
            const int splitrouter = n->routers[split];

            // x[split] <= router[split] <= x[split+1]
            // copy elements into right_child
            for (int i = 0; i <= split; ++i) {
                node *child = n->children[i];
                child->parent = left;
                left->children.push_back(child);
            }
            for (int i = split+1; i < n->children.size(); ++i) {
                node *child = n->children[i];
                child->parent = right;
                right->children.push_back(child);
            }

            // copy routers
            for (int i = 0; i <= split-1; ++i) {
                left->routers.push_back(n->routers[i]);
            }

            for(int i = split+1; i < n->routers.size(); ++i) {
                right->routers.push_back(n->routers[i]);
            }

            n->routers.clear();
            n->children.clear();

            n->children.push_back(left);
            n->routers.push_back(splitrouter);
            n->children.push_back(right);

            n->check();
            left->check();
            right->check();
        } 

        // now proceed with the computation
        // since now n has space creatred properly

        assert (n->children.size() < TREE_N);

        for(int i = 0; i < n->routers.size(); ++i) {
            if (x <= n->routers[i]) {
                insert_recur(x, b, n->children[i]);
            }
        }


        node *leaf = new node();
        leaf->isleaf = true;
        leaf->parent = n;
        leaf->vals.push_back(x);

        assert(n->children.size() < TREE_N);

        // C0:10 || ---
        // C0:10 || R0: 20 || C1:20 || --
        n->routers.push_back(x);
        n->children.push_back(leaf);
        n->check();
        leaf->check();
    } // end if(n->isleaf)
}


void insert(int x, btree &b) {
    if (b.root == nullptr) {
        cerr << "b.root == nullptr\n";
        b.root = new node();
        b.root->isleaf = false;
        
        b.root->children.push_back(new node);
        b.root->children[0]->isleaf = true;
        b.root->children[0]->vals.push_back(x);
        b.root->check();
    } else {
        insert_recur(x, b, b.root);
    }
};

int count_node(int x, node *n) {
    if (n->isleaf) {
        int count = 0;
        for(int i = 0; i < n->vals.size(); ++i) {
            if (n->vals[i] == x) { count++; }
            // once n->vals becomes greater, switch.
            if (n->vals[i] > x) { break; }
        }
        return count;
    } else {
        assert(!n->isleaf);
        assert(n->children.size() > 0);
        assert(n->children.size() > n->routers.size());
        int count = 0;
        for(int i = 0; i < n->routers.size(); ++i) {
            if (x <= n->routers[i]) {
                count += count_node(x, n->children[i]);
            }
        }
        // count the final child if necessary;
        if (n->routers.size() > 0) {
            if (x >= n->routers[n->routers.size() - 1]) {
                count += count_node(x, n->children[n->children.size() -1]);
            }
        }
        return count;

    }

    assert(false && "unreachable");

}

int count(int x, btree &b) {
    if (!b.root) { return 0; }
    return count_node(x, b.root);
}

int range_node(int x, int y, node *n) {
}

int range(int x, int y, btree &b) {
    if (!b.root) { return 0; }
    return range_node(x, y, b.root);
};


int main(int argc, char *argv[]) {
    assert(argc == 2);
    cerr << "reading: " << argv[1] << "\n";
    ifstream f; f.open(argv[1], std::ifstream::in);

    btree b;
    std::string l;
    while (getline(f, l)) {
        std::stringstream ss(l);

        string c; ss >> c;
        if (c == "INSERT") {
            int x; ss >> x; insert(x, b);
            assert(b.root);
        } else if (c == "FIND") {
            int x; ss >> x; 
            if (find(x, b)) { cout << "YES\n"; } else { cout << "NO\n"; }
        } else if (c == "COUNT") {
            int x; ss >> x; cout << count(x, b) << "\n";
        } else if (c  == "RANGE") {
            int x, y; ss >> x >> y; cout << range(x, y, b) << "\n";
        }
        cerr << "---after request: " << l << ":---\n";
        printnode(b.root, 2);
        cerr << "---\n";
    }
    return 0;
}
