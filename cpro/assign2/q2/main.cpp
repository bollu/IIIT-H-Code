#include <iostream>
#include <algorithm>
#include <vector>

using namespace std;
#define endl '\n'

typedef int digit;
typedef vector<digit> number;

//a b c 
//d e f x
//---------
//       af bf cf | intermediates[0]
//    ae   be   ce | intermediates[1]


template<typename T>
void printvec(vector<T> &v, string name="")  {
    cout<<name<<" : [";
    for(auto x : v) {
        cout<<x<<" ";
    }
    cout<<"]\n";
}

number add (number as, number bs) {
    number sum;
    const int n = max(as.size(), bs.size());
    for(int i = 0; i < n + 1; i++) {
        sum.push_back(0);
    }
    
    int carry = 0;
    for(int i = 0; i < n; i++) {
        int s = 0;
        if (i < as.size()) { s += as[i]; }
        if (i < bs.size()) { s += bs[i]; }
        s += carry;
        
        int digitsum = s % 10;
        carry = (s - digitsum) / 10;
        sum[i] = digitsum;

        //printvec(sum, "sum - " + std::to_string(i));
    }

    sum[n] = carry;
    return sum;

}


number product(number as, number bs) {
    number prod;

    //printvec(as, "as");
    //printvec(bs, "bs");

    vector<vector<int>> intermediates;
    for(int bi = 0; bi < bs.size(); bi++) {
        intermediates.push_back(vector<int>());
        for(int j = 0; j < as.size() + bs.size(); j++) {
            intermediates[bi].push_back(0);
        }
    }


    for(int i = 0; i < as.size() + bs.size(); i++) {
        prod.push_back(0);
    }


    for(int bi = 0; bi < bs.size(); bi++) {
        int digitcarry = 0;
        for(int ai = 0; ai < as.size(); ai++) {
            const int a = as[ai];
            const int b = bs[bi];

            const int totalprod = a * b + digitcarry;
            const int digitprod = totalprod % 10;
            digitcarry = (totalprod - digitprod) / 10;
            //cout<<"digit: "<<digitprod<<" | carry: "<<digitcarry<<"\n";

            intermediates[bi][ai + bi] += digitprod;
        }
        intermediates[bi][bi + as.size()] = digitcarry;
        //printvec(intermediates[bi], "int-" + std::to_string(bi));
    }
    

    for(int bi = 0; bi < bs.size(); bi++) {
        prod = add(prod, intermediates[bi]);
        //printvec(prod, "add-" + std::to_string(bi));
    }

    //remove zeroes at higher positions
    while(prod[prod.size() - 1] == 0 && prod.size() > 1) {
        prod.pop_back();
    }
    return prod;
}

int main() {

    std::ios::sync_with_stdio(false);
    cin.tie(NULL);
    
    number n[2];
    for(int i = 0; i < 2; i++) {
        string ns; cin>>ns;
        for(char c : ns) {
            n[i].push_back(c - '0');
        }
        reverse(n[i].begin(), n[i].end());
    }

    number p = product(n[0], n[1]);
    reverse(p.begin(), p.end());

    for(auto d : p) {
        cout<<d;
    }

    return 0;

}
