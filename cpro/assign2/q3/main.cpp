#include <iostream>
#include <algorithm>
#include <vector>

using namespace std;
#define endl '\n'

typedef int digit;
typedef vector<digit> number;

template<typename T>
void printvec(vector<T> &v, string name="")  {
    cout<<name<<" : [";
    for(auto x : v) {
        cout<<x<<" ";
    }
    cout<<"]\n";
}

//remove leading zeroes
//00012 -> 12
//in the representation, since ones place is at "0", this will be
//[1, 2, 0, 0, 0] -> [1, 2]
number trim(number a) {
    while(a[a.size() - 1] == 0 && a.size() > 1) {
        a.pop_back();
    }
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
    sum = trim(sum);
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

    prod = trim(prod);
    return prod;
}


//assumes a > b
number sub(number a, number b) {
    number sub;
    for(int i = 0; i < a.size(); i++) {
        sub.push_back(a[i]);
    }

    int carry = 0;
    for(int i = 0; i < b.size(); i++) {
        if (a[i] - b[i] - carry >= 0) {
            sub[i] = a[i] - b[i] - carry;
            carry = 0;
        } else {
            carry = 1;
            sub[i] = (10 + a[i]) - b[i] - carry;
        }
    }

    sub = trim(sub);
    return sub;
    
}

const vector<int> one = [1];
const vector<int> zero = [0];
number exp_slow(number a, number exp) {
    exp = trim(exp);
    a = trim(a);
    

    if (exp == zero)
        return one;
    } else if (exp == one)
        return a;
    }
    else {
        return prod(a, sub(exp, one));
    }
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

    number p = sub(n[0], n[1]);
    reverse(p.begin(), p.end());

    for(auto d : p) {
        cout<<d;
    }

    return 0;

}
