#include <bits/stdc++.h>
using namespace std;
using lint=int64_t;

template<lint mod>
class LinRec {
public:
    explicit LinRec(const vector<lint> &S={}) {
        if (!S.empty())
            init(S);
    }

    void init(const vector<lint> &S) {
        seq_=S;
        for (auto &x: seq_) {
            x%=mod;
            if (x<0) x+=mod;
        }
        C_=berlekamp_massey(seq_);
        L_=C_.size()-1;
        rec_.assign(L_, 0);
        for (int i=0; i<L_; i++)
            rec_[i]=C_[i+1];
        init_.assign(seq_.begin(), seq_.begin()+max(0, L_));
    }

    lint nth(lint n) const {
        assert(ready());
        if (L_==0) return 0;
        if (n<init_.size())
            return init_[n];
        return nth_lin(init_, rec_, n);
    }

    int order() const { return L_; }
    const vector<lint> &recurrence() const { return rec_; }
    const vector<lint> &init() const { return init_; }
    const vector<lint> &characteristic_poly() const { return C_; }
    bool ready() const { return L_>=0 && init_.size()==L_; }

private:
    int L_=-1;
    vector<lint> seq_;
    vector<lint> C_;
    vector<lint> rec_;
    vector<lint> init_;

    static lint pow(lint n, lint k) {
        lint r=1;
        while (k) {
            if (k&1)
                r=r*n%mod;
            n=n*n%mod;
            k>>=1;
        }
        return r;
    }
    static lint inv(lint a) { return pow(a, mod-2); }

    static vector<lint> berlekamp_massey(const vector<lint> &s) {
        vector<lint> C{1}, B{1};
        lint b=1;
        int L=0, m=1;

        for (int n=0; n<s.size(); n++) {
            __int128 d=0;
            for (int i=1; i<=L; i++)
                d=(d+(__int128)C[i]*s[n-i])%mod;
            d=(s[n]-d)%mod;
            if (d<0) d+=mod;
            if (d==0) {
                m++;
                continue;
            }

            vector<lint> T=C;
            lint coef=d*inv(b)%mod;
            if (C.size()<B.size()+m)
                C.resize(B.size()+m, 0);
            for (int i=0; i<B.size(); i++)
                C[i+m]=(C[i+m]+(__int128)coef*B[i])%mod;

            if (2*L<=n) {
                L=n+1-L;
                B=move(T);
                b=d, m=1;
            }
            else m++;
        }
        for (int i=1; i<C.size(); i++)
            C[i]=(mod-C[i])%mod;
        return C;
    }

    static vector<lint> combine(
            const vector<lint> &a, const vector<lint> &b, const vector<lint> &rec
        ) {
        int L=rec.size();
        vector<lint> prod(L*2-1, 0);
        for (int i=0; i<L; i++) if (a[i])
            for (int j=0; j<L; j++)
                prod[i+j]=(prod[i+j]+(__int128)a[i]*b[j])%mod;
        // auto prod=NTT<mod, root>::conv(a, b);
        // if (prod.size()<L*2-1)
        //     prod.resize(L*2-1, 0);
        for (int i=2*L-2; i>=L; i--) {
            if (!prod[i]) continue;
            for (int j=1; j<=L; j++)
                prod[i-j]=(prod[i-j]+(__int128)prod[i]*rec[j-1])%mod;
        }
        prod.resize(L);
        return prod;
    }

    static lint nth_lin(const vector<lint> &init, const vector<lint> &rec, lint n) {
        int L=rec.size();
        if (n<init.size())
            return init[n];

        vector<lint> res(L, 0), base(L, 0);
        res[0]=1;
        if (L>1)
            base[1]=1;
        else base[0]=rec[0];

        lint k=n;
        while (k) {
            if (k&1)
                res=combine(res, base, rec);
            base=combine(base, base, rec);
            k>>=1;
        }
        __int128 r=0;
        for (int i=0; i<L; i++)
            r=(r+(__int128)res[i]*init[i])%mod;
        if (r<0) r+=mod;
        return r;
    }
};
