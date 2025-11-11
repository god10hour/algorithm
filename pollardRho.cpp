#include <bits/stdc++.h>
using namespace std;
using lint=uint64_t;

lint pow(__int128 n, __int128 k, lint mod) {
    __int128 r=1;
    while (k) {
        if (k&1)
            r=r*n%mod;
        n=n*n%mod;
        k/=2;
    }
    return r;
}

constexpr lint base[] {
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37
};
bool prime(lint n) {
    if (n<2) return 0;
    for (int p: base)
        if (n%p==0)
            return n==p;
    lint d=n-1;
    int s=__builtin_ctzll(d);
    d>>=s;

    auto f=[&](lint a)->bool {
        if (a%n==0) return 1;
        lint x=pow(a, d, n);
        if (x==1 || x==n-1) return 1;
        for (int r=1; r<s; r++) {
            x=(__int128)x*x%n;
            if (x==n-1) return 1;
            if (x==1) return 0;
        }
        return 0;
    };

    for (lint a: base) if (!f(a))
        return 0;
    return 1;
}

lint div(lint n) {
    if ((n&1)==0) return 2;
    if (prime(n)) return n;

    while (1) {
        lint c=rand()%n;
        lint y=rand()%(n-3)+2;
        lint m=256;
        auto step=[&](lint x)->lint {
            return ((__int128)x*x+c)%n;
        };

        lint d=1, r=1, q=1;
        while (d==1) {
            lint x=y;
            for (lint i=0; i<r; i++)
                y=step(y);

            lint k=0;
            while (k<r && d==1) {
                lint lim=min(m, r-k);
                for (lint i=0; i<lim; i++) {
                    y=step(y);
                    q=(__int128)q*llabs(x-y)%n;
                }
                d=gcd(q, n);
                k+=lim;
            }
            r<<=1;
        }
        if (d==n) {
            lint x=y;
            do {
                x=step(x);
                d=gcd(llabs(x-y), n);
            } while (d==1);
        }
        if (d!=n) return d;
    }
}

static void _fact(lint n, vector<lint> &r) {
    if (n==1) return;
    if (prime(n)) {
        r.push_back(n);
        return;
    }
    lint d=div(n);
    _fact(d, r);
    _fact(n/d, r);
}

vector<lint> factor(lint n) {
    vector<lint> r;
    for (int p: base)
        while (n%p==0)
            r.push_back(p), n/=p;
    if (n>1) _fact(n, r);
    sort(r.begin(), r.end());
    return r;
}

int main() {
    cin.tie(0)->sync_with_stdio(0);
    lint n;
    cin >> n;
    auto a=factor(n);
    for (auto x: a) cout << x << '\n';
}
