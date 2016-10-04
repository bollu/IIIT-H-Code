#include <iostream>
using namespace std;
#define endl '\n'

int main() {

    std::ios::sync_with_stdio(false);
    cin.tie(NULL);
    

    int n; bool print = true;
    while (true) {
        cin>>n;

        if (n == 42) {
            print = false;
        }
        if (print) {
            cout<<n;
        }

    }
    return 0;

}
