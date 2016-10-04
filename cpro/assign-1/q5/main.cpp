#include <iostream>
#include <assert.h>
using namespace std;
#define endl '\n'

static const int N = 1e6;
int arr[N];

int binsearch(int value, int begin, int end) {
    if (begin > end) {
        return 0;
    }

    int mid = (begin + end) / 2;

    if (value == arr[mid]) {
        return 1;
    } else  if (value > arr[mid]) {
        return binsearch(value, mid + 1, end);
    }
    else {
        return binsearch(value, begin, mid - 1);
    }
    assert (false && "should not reach here");
}
int main() {

    std::ios::sync_with_stdio(false);
    cin.tie(NULL);

    int n; cin>>n;
        
    //NOTE: assuming the input is sorted...
    for(int i = 0; i < n; i++) {
        cin>>arr[i];
    }


    int value; cin>>value;

    int found = binsearch(value, 0, n - 1);

    if (found) {
        cout<<"found: "<<value<<"\n";
    }
    else {
        cout<<"not found: "<<value<<"\n";
    }
    
    return 0;

}
