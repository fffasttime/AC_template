#include <iostream>
#include <iomanip>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cmath>
using namespace std;

struct Huge{
    static const int MAXN=1001;
    static const int BASE=10000;
    int Num[MAXN];
    int len;
    void init(const string &s){
        memset(Num,0,sizeof(Num));
        int rlen=s.size();
        len=0;
        int i;
        for (i=rlen-5;i>=0;i-=4){
            Num[len]=Num[len]*10+s[i+1]-'0';
            Num[len]=Num[len]*10+s[i+2]-'0';
            Num[len]=Num[len]*10+s[i+3]-'0';
            Num[len]=Num[len]*10+s[i+4]-'0';
            len++;
        }
        if (i<0) i+=4;
        for (int j=0;j<=i;j++)
            Num[len]=Num[len]*10+s[j]-'0';
        len++;
    }
    friend istream& operator>>(istream &i, Huge &v){
        string s;
        i>>s;
        v.init(s);
        return i;
    }
    friend ostream& operator<<(ostream &o, Huge &v){
        if (v.len==0 && v.Num[0]==0){
            o<<'0';
            return o;
        }
        o<<v.Num[v.len-1];
        for (int i=v.len-2;i>=0;i--)
            o<<setw(4)<<setfill('0')<<v.Num[i]; 
        return o;
    }
    void operator+=(const Huge &v)
    {
        int nlen=max(v.len,len);
        for (int i=0;i<nlen;i++){
            Num[i]+=v.Num[i];
            if (Num[i]>=BASE){
                Num[i]-=BASE;
                Num[i+1]++;
            }
        }
        if (Num[nlen]!=0) nlen++;
        len=nlen;
        //return (*this);
    }
    void operator-=(const Huge &v){
        int nlen=max(v.len,len);
        for (int i=0;i<nlen;i++){
            Num[i]-=v.Num[i];
            if (Num[i]<0){
                Num[i]+=BASE;
                Num[i+1]--;
            }
        }
        while (Num[nlen]==0 && nlen>=0) nlen--;
        len=nlen+1;
        //return (*this);
    }
    void operator*=(const Huge &v){
        Huge c;
        c.init("0");
        for (int i=0;i<len;i++)
            for (int j=0;j<v.len;j++){
                c.Num[i+j]+=Num[i]*v.Num[j];
                if (c.Num[i+j]>=BASE){
                    c.Num[i+j+1]+=c.Num[i+j]/BASE;
                    c.Num[i+j]%=BASE;
                }
            }
        c.len=len+v.len;
        while (c.Num[c.len]==0 && c.len>=0) c.len--;
        len=c.len+1;
        for (int i=0;i<len;i++) Num[i]=c.Num[i];
        //return (*this);
    }
    bool operator<(const Huge &v){
        if (len!=v.len) return len<v.len;
        for (int i=len-1;i>=0;i--)
            if (Num[i]!=v.Num[i]) return Num[i]<v.Num[i];
        return 0;
    }
};

int main()
{
    Huge a,b;
    cin>>a>>b;
    a*=b;
    cout<<a<<'\n';
    return 0;
}
