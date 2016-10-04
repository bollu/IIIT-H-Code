#include <iostream>
using namespace std;
#define endl '\n'


int main() {

    std::ios::sync_with_stdio(false);
    cin.tie(NULL);

    int n; cin>>n;
    int total;
    while(n--) {
        int x; cin>>x;
        total = total ^ x;
    }

    cout<<total;


    
    return 0;

}
