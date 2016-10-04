#include <iostream>
using namespace std;
#define endl '\n'


//first player always wins, by argument of strategy stealing
int main() {

    std::ios::sync_with_stdio(false);
    cin.tie(NULL);
    

    int t; cin>>t;
    while(t--) {
        int n; cin>>n;
        int player; cin>>player;

        if (player == 0) {
            cout<<"Airborne wins\n";
        }else {
            cout<<"Pagfloyd wins\n";
        }
    }



    return 0;

}
