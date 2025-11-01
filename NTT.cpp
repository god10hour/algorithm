#include <bits/stdc++.h>
using namespace std;

#define int int64_t
template<int mod, int root>
struct NTT {
    static int pow(int n, int k) {
        int r=1;
        while (k) {
            if (k&1)
                r=r*n%mod;
            n=n*n%mod;
            k/=2;
        }
        return r;
    }

    static void ntt(vector<int> &v, bool inv) {
        int s=v.size();
        for (int i=1, j=0; i<s; i++) {
            int b=s/2;
            while (j>=b)
                j-=b, b/=2;
            j+=b;
            if (i<j) swap(v[i], v[j]);
        }
        for (int k=1; k<s; k*=2) {
            int w=pow(root, (mod-1)/(k*2));
            if (inv) w=pow(w, mod-2);
            for (int i=0; i<s; i+=k*2) {
                int uni=1;
                for (int j=0; j<k; j++) {
                    int a=v[i+j];
                    int b=v[i+j+k]*uni%mod;
                    v[i+j]=(a+b)%mod;
                    v[i+j+k]=(a-b+mod)%mod;
                    uni=uni*w%mod;
                }
            }
        }
        if (inv) {
            int I=pow(s, mod-2);
            for (int i=0; i<s; i++)
                v[i]=v[i]*I%mod;
        }
    }

    static vector<int> conv(vector<int> V, vector<int> U) {
        if (V.empty() || U.empty())return {};
        int s=1, n=V.size()+U.size()-1;
        while (s<n) s*=2;
        V.resize(s); ntt(V, 0);
        U.resize(s); ntt(U, 0);
        for (int i=0; i<s; i++)
            V[i]=V[i]*U[i]%mod;
        ntt(V, 1), V.resize(n);
        return V;
    }
};

template<int mod=0, int root=0>
struct Poly {
    inline static int lim=-1;
    vector<int> v;
    Poly()=default;
    explicit Poly(int n): v(n, 0) {}
    explicit Poly(const vector<int> &v): v(v) {}
    explicit Poly(vector<int> &&v): v(move(v)) {}

    [[nodiscard]] unsigned size() const { return v.size(); }
    void resize(int n) { v.resize(n); }
    int &operator[](int i) { return v[i]; }
    void selfcut(int m) { if (m<(int)v.size()) v.resize(m); }
    vector<int> cut(int m) {
        if (m>=(int)v.size()) return v;
        return vector<int>(v.begin(), v.begin()+m);
    }
    static void set(int m) { lim=m; }
    static void clear() { lim=-1; }
    void trim() {
        while (!v.empty() && v.back()==0)
            v.pop_back();
    }

    static Poly conv(const Poly &V, const Poly &U) {
        Poly r;
        if constexpr (mod)
            r.v=NTT<mod, root>::conv(V.v, U.v);
        if (lim>0 && r.v.size()>lim)
            r.resize(lim);
        return r;
    }

    Poly operator+(const Poly &o) const {
        int s=max(size(), o.size());
        if (lim>0) s=min(s, lim);
        Poly r(s);
        for (int i=0; i<s; i++) {
            int x=i<size()? v[i]:0;
            int y=i<o.size()? o.v[i]:0;
            if constexpr (mod) r[i]=(x+y)%mod;
            else r[i]=x+y;
        }
        return r;
    }
    Poly operator-(const Poly &o) const {
        int s=max(size(), o.size());
        if (lim>0) s=min(s, lim);
        Poly r(s);
        for (int i=0; i<s; i++) {
            int x=i<size()? v[i]:0;
            int y=i<o.size()? o.v[i]:0;
            if constexpr (mod) r[i]=(x-y+mod)%mod;
            else r[i]=x-y;
        }
        return r;
    }
    Poly operator*(const Poly &o) const {
        if (lim>0) {
            Poly w=conv(*this, o);
            if (lim>0 && w.size()>lim) w.resize(lim);
            return w;
        }
        return conv(*this, o);
    }

    Poly pow(Poly base, int k) {
        Poly r(1);
        r[0]=1;
        while (k) {
            if (k&1)
                r=r*base;
            base=base*base;
            k/=2;
        }
        if (lim>0 && base.size()>lim)
            base.resize(lim);
        return r;
    }
};
// using poly=Poly<469762049, 3>;

struct CRT {
    using u128=__uint128_t;
    static constexpr int MODS[3]={
        167772161, 469762049, 1224736769
    };
    static constexpr int ROOT=3;
    using P0=Poly<MODS[0], ROOT>;
    using P1=Poly<MODS[1], ROOT>;
    using P2=Poly<MODS[2], ROOT>;

    static int pow(int n, int k, int mod) {
        int r=1;
        while (k) {
            if (k&1)
                r=r*n%mod;
            n=n*n%mod;
            k/=2;
        }
        return r;
    }

    int combine(const int a[3], int p) {
        u128 r=0, mod=1;
        for (int i=0; i<3; i++) {
            int Mi=MODS[i], ri=r%Mi;
            if (ri<0) ri+=Mi;
            int diff=(a[i]+Mi-ri)%Mi;
            int inv=pow(mod%Mi, Mi-2, Mi);
            r+=mod*(diff*inv%Mi);
            mod*=Mi;
        }
        return r%p;
    }

    vector<int> conv(const vector<int> &V, const vector<int> &U, int p) {
        if (V.empty() || U.empty()) return {};
        int n=V.size()+U.size()-1;
        array<vector<int>, 3> v, u;
        for (int i=0; i<3; i++) v[i].resize(V.size());
        for (int i=0; i<3; i++) u[i].resize(U.size());

        for (int i=0; i<V.size(); i++)
            for (int j=0; j<3; j++) {
                v[j][i]=V[i]%MODS[j];
                if (v[j][i]<0) v[j][i]+=MODS[j];
            }
        for (int i=0; i<U.size(); i++)
            for (int j=0; j<3; j++) {
                u[j][i]=U[i]%MODS[j];
                if (u[j][i]<0) u[j][i]+=MODS[j];
            }

        P0 w0=P0::conv(P0(v[0]), P0(u[0]));
        P1 w1=P1::conv(P1(v[1]), P1(u[1]));
        P2 w2=P2::conv(P2(v[2]), P2(u[2]));
        if (w0.size()>n) w0.resize(n);
        if (w1.size()>n) w1.resize(n);
        if (w2.size()>n) w2.resize(n);

        vector<int> r(n);
        for (int i=0; i<n; i++) {
            int a[3]={
                i<w0.size()? w0.v[i]:0,
                i<w1.size()? w1.v[i]:0,
                i<w2.size()? w2.v[i]:0
            };
            r[i]=combine(a, p);
        }
        return r;
    }

    vector<int> pow(vector<int> base, int k, int p) {
        vector<int> r(1, 1);
        while (k) {
            if (k&1)
                r=conv(r, base, p);
            base=conv(base, base, p);
            k/=2;
        }
        return r;
    }
};
#undef int

int main() {
    cin.tie(0)->sync_with_stdio(0);

    // NTT Use
    vector<int64_t> A={1, 2, 3};
    int s=1; while (s<A.size()) s*=2;
    A.resize(s);
    NTT<469762049, 3>::ntt(A, 0);
    for (auto x: A) cout << x << ' ';
    cout << "\n\n";

    // NTT-friendly prime
    using poly=Poly<469762049, 3>;
    poly f(vector<int64_t>{1, 2, 3}), g(vector<int64_t>{4, 5}), h;
    h=f+g; for (auto x: h.v) cout << x << ' '; cout << '\n';
    h=f-g; for (auto x: h.v) cout << x << ' '; cout << '\n';
    h=f*g; for (auto x: h.v) cout << x << ' '; cout << '\n';
    h=f.pow(f, 3); for (auto x: h.v) cout << x << ' '; cout << '\n';
    cout << '\n';

    // Non-NTT-friendly prime
    CRT crt;
    vector<int64_t> v={1, 2, 3, 4};
    vector<int64_t> u={5, 6, 7};
    auto w=crt.conv(v, u, 1e9+7);
    for (auto x: w) cout << x << ' ';
}