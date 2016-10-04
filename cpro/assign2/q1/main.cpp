#include <iostream>
#include <algorithm>
using namespace std;
#define endl '\n'

const int N = 1e6;
int pos[N];
int n;
int ncows;

int try_place_with_dist(int x) {
    int cowsplaced = 1;
    int prevpos = pos[0];

    for(int i = 1; i < n; i++) {
        //try to place a cow in the current stall. If this is not
        //possible, try next stall.
        //we need sorted order to make sure that increasing i 
        //gives us larger distance between stalls
        if (pos[i] - prevpos >= x) {
            prevpos = pos[i];
            cowsplaced++;
            if (cowsplaced == ncows) {
                return 1;
            }
        }
    }
    return 0;
}

int get_optimal_placement() {
    int startpos = 0; 
    int endpos = pos[n - 1];
    int maxdist = -1;

    while(startpos < endpos) {
        int midpos = (startpos + endpos) / 2;
        if (try_place_with_dist(midpos) == 1) {
            startpos = midpos + 1;

            if (midpos > maxdist) { maxdist = midpos; }
        }
        else {
            endpos = midpos;
        }
    }

    return maxdist;
}

int main() {

    std::ios::sync_with_stdio(false);
    cin.tie(NULL);
    
    int t; cin>>t;
    while (t--) {
        cin>>n>>ncows;
        for(int i = 0; i < n; i++) {
            cin>>pos[i];
        }
        sort(pos, pos + n);
        cout<<get_optimal_placement()<<"\n";

    }

    return 0;

}
