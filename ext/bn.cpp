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
    int num[MAXN]; //low digit on small pos
    int len;
    void set(const char *s){
        memset(num,0,sizeof(num));
        int rlen=strlen(s);
        len=0;
        int i;
        for (i=rlen-5;i>=0;i-=4){
            num[len]=num[len]*10+s[i+1]-'0';
            num[len]=num[len]*10+s[i+2]-'0';
            num[len]=num[len]*10+s[i+3]-'0';
            num[len]=num[len]*10+s[i+4]-'0';
            len++;
        }
        if (i<0) i+=4;
        for (int j=0;j<=i;j++)
            num[len]=num[len]*10+s[j]-'0';
        len++;
    }
    int c_str(char *o){
    	if (len==0 && num==0){
    		o[0]='0'; o[1]=0;
    		return 1;
		}
		sprintf(o,"%d",num[len-1]);
		int ret=strlen(o);
		for (int i=len-2;i>=0;i--){
			o[ret++]=num[i]/1000+'0';
			o[ret++]=num[i]/100%10+'0';
			o[ret++]=num[i]/10%10+'0';
			o[ret++]=num[i]%10+'0';
		}
		o[ret]=0;
		return ret;
	}
    //[!] this function is slow, use C-style input and init() on large data 
    friend istream& operator>>(istream &i, Huge &v){
        string s;
        i>>s; v.set(s.c_str());
        return i;
    }
    friend ostream& operator<<(ostream &o, Huge &v){
        if (v.len==0 && v.num[0]==0){
            o<<'0';
            return o;
        }
        o<<v.num[v.len-1];
        for (int i=v.len-2;i>=0;i--)
            o<<setw(4)<<setfill('0')<<v.num[i]; 
        return o;
    }
    void operator+=(const Huge &v){
        int nlen=max(v.len,len);
        for (int i=0;i<nlen;i++){
            num[i]+=v.num[i];
            if (num[i]>=BASE){
                num[i]-=BASE;
                num[i+1]++;
            }
        }
        if (num[nlen]) nlen++;
        len=nlen;
        //return (*this);
    }
    void operator-=(const Huge &v){
        int nlen=max(v.len,len);
        for (int i=0;i<nlen;i++){
            num[i]-=v.num[i];
            if (num[i]<0){
                num[i]+=BASE;
                num[i+1]--;
            }
        }
        while (num[nlen]==0 && nlen>=0) nlen--;
        len=nlen+1;
        //return (*this);
    }
    void operator*=(const Huge &v){
        Huge c;
        c.set("0");
        for (int i=0;i<len;i++)
            for (int j=0;j<v.len;j++){
                c.num[i+j]+=num[i]*v.num[j];
                if (c.num[i+j]>=BASE){
                    c.num[i+j+1]+=c.num[i+j]/BASE;
                    c.num[i+j]%=BASE;
                }
            }
        c.len=len+v.len;
        while (c.num[c.len]==0 && c.len>=0) c.len--;
        len=c.len+1;
        for (int i=0;i<len;i++) num[i]=c.num[i];
        //return (*this);
    }
    bool operator<(const Huge &v){
        if (len!=v.len) return len<v.len;
        for (int i=len-1;i>=0;i--)
            if (num[i]!=v.num[i]) return num[i]<v.num[i];
        return 0;
    }
    bool operator<=(const Huge &v){
        if (len!=v.len) return len<v.len;
        for (int i=len-1;i>=0;i--)
            if (num[i]!=v.num[i]) return num[i]<v.num[i];
        return 1;
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
