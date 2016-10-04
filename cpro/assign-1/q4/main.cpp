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
        if (n% 2 == 0) {
            cout<<"Thankyou Shaktiman\n";
        }
        else {
            cout<<"Sorry Shaktiman\n";
        }

    }



    return 0;

}
