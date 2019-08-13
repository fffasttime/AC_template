/*
Name: AC_template_main
Author: fffasttime 
Date: 
Description: 
*/
//#pragma comment(linker, "/STACK:1024000000,1024000000")
//#pragma GCC optimize("Ofast,no-stack-protector")
//#pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx,tune=native")
//#pragma GCC optimize("unroll-loops")

#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <vector>
#include <set>
#include <map>
#include <queue>
#include <complex>
#include <cassert>
#include <algorithm>
using namespace std;
#define USE_ATTR
#ifdef USE_ATTR
#define inc(i,n) for (int i=0;i<n;i++)
#define icc(i,n) for (int i=1;i<=n;i++)
#define dec(i,n) for (int i=n-1;i>=0;i--)
#define dcc(i,n) for (int i=n;i>0;i--)
#define rep(i,a,b) for (int i=a;i<b;i++)
#define rpp(i,a,b) for (int i=a;i<=b;i++)
#define per(i,b,a) for (int i=b-1;i>=a;i--)
#define prr(i,b,a) for (int i=b;i>=a;i--)

#define MS(a,x) memset(a,x,sizeof(a))
//we can use initiallist in c++1x
#define MP make_pair
#define PII pair<int,int>
//std=c++11
#define MT make_tuple
#define TIII tuple<int, int, int>

#endif

typedef long long ll;
typedef double db;
typedef ll T;

//warning: Can't use other input method while using fread.
int rc(){
	//return getchar(); //if use fread, input won't stop until EOF
	static char buf[10000],*p1=buf,*p2=buf;
	return p1==p2&&(p2=(p1=buf)+fread(buf,1,10000,stdin),p1==p2)?EOF:*p1++;
}
int rd(int &x){
	x=0; int f=1,c=rc();
	while (!isdigit(c) && c!=-1) c=='-'?f=-1:0,c=rc();
	if (c==-1) return 0;
	while (isdigit(c)) x=x*10+c-'0', c=rc();
	x*=f; return 1;
}
int rd(char *x){
	int c=rc();
	while (isspace(c) && c!=-1) c=rc();
	if (c==-1) return 0;
	while (!isspace(c) && c!=-1) *(x++)=c,c=rc();
	*x=0; return 1;
}

int qrand(){
	static int seed=2333;
	return seed = (int)((((seed ^ 998244353)+19260817ll)*12345678ll)%1000000007);
}

T gcd(T a, T b){ return b==0?a:gcd(b, a%b);}
int gcd(int a, int b) {return b?gcd(b,a%b):a;}

ll qmul(ll x,ll y,ll p){
	ll t=(x*y-(ll)((long double)x/p*y+0.5)*p);
	return t<0 ? t+p : t;
}
//return a^x
T qpow(T a, int x){
	T ans=1;
	for (;x;a*=a,x>>=1)
		if (x&1)
			ans*=a;
	return ans;
}
ll qpow(ll a, ll x, ll p){
	ll ans=1;
	for (;x;a=qmul(a,a,p),x>>=1)
		if (x&1)
			ans=qmul(ans,a,p);
	return ans;
}

const int N=100;
struct Mat{
	ll m[N][N];
	Mat(){memset(m,0,sizeof(m));}
	void I(){for (int i=0;i<N;i++) m[i][i]=1;}
};
Mat mul(const Mat &a, const Mat &b){
	Mat c;
	for (int i=0;i<N;i++)
		for (int j=0;j<N;j++){
			for (int k=0;k<N;k++)
				c.m[i][j]+=a.m[i][k]*b.m[k][j];
			//c.m[i][j]%=p;
		}
	return c;
}
Mat qpow(Mat a, int x){
	Mat ans; ans.I();
	for (;x;a=mul(a,a),x>>=1)
		if (x&1)
			ans=mul(ans,a);
	return ans;
}

//require p is a prime
int inv(int x, int p){
	return qpow(x,p-2,p);
}

//int main(){}
