#include <iostream>
#include <algorithm>
#include <vector>

using namespace std;
#define endl '\n'

const int N = 10;

int maxproduct(int *arr, int n) {
    int maxprod = arr[0], minprod = arr[0];
    int allmax = arr[0];
    for(int i = 1; i < n; i++) {
        if (arr[i] > 0) {
            maxprod = max(arr[i], maxprod * arr[i]);
            minprod = min(arr[i], minprod * arr[i]);
        } else {
            int maxprod_ = maxprod;
            maxprod = max(arr[i], minprod * arr[i]);
            minprod = min(arr[i], maxprod_ * arr[i]);
        }

        if (maxprod > allmax) {
            allmax = maxprod;
        }
    }
    return allmax;

}

int main() {

    std::ios::sync_with_stdio(false);
    cin.tie(NULL);
    
    int t; cin>>t;
    while (t--) {
        int n;
        cin>>n;
        int arr[N];

        for(int i = 0; i < n; i++) {
            cin>>arr[i];
        }
        cout<<maxproduct(arr, n)<<"\n";
    }

    return 0;

}
