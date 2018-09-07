/*
Name: 
Author: fffasttime 
Date: 
Description: 
*/
//#pragma comment(linker, "/stack:200000000")
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
	ll t=(x*y-(ll)((long double)x/p*y+1.0e-8)*p);
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
			for (int k=0;k<=N;k++)
				c.m[i][j]+=a.m[i][j]*b.m[i][j];
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

const int maxn=1000010;
int p[maxn],phi[maxn],pc;
bool isp[maxn];

void gen(){
	memset(isp,1,sizeof(isp));
	isp[1]=0;
	for (int i=2;i<maxn;i++){
		if (isp[i]) p[pc++]=i,phi[i]=i-1;
		for (int j=0;j<pc && i*p[j]<maxn;j++){
			isp[i*p[j]]=0;
			if (i%p[j]==0){
				phi[i*p[j]]=phi[i]*p[j];
				break;
			}
			phi[i*p[j]]=phi[i]*(p[j]-1);
		}
	}
}

int inv(int x, int p){
	return qpow(x,p-2,p);
}

int invt[maxn];
void invTable(int maxl, int p){
	invt[1]=1;
	for (int i=2;i<=maxl;i++)
		invt[i]=invt[p%i]*(p-p/i)%p;
}

//ax+by=gcd(a,b)
ll exgcd(ll a, ll b, ll &x, ll &y){
	if (b==0){
		x=1;y=0;
		return a;
	}
	ll t=exgcd(b,a%b,y,x);
	y-=a/b*x;
	return t;
}
ll inv_euclid(ll v, ll p){
	ll x,y;
	if (exgcd(v,p,x,y)==1)
		return (x+p)%p;
	else
		return -1;
}
//CRT
//x=a1(mod p1)
//x=a2(mod p2)
//...
ll china(int n, ll a[], ll p[]){
	ll M=1,x=0;
	for (int i=0;i<n;i++) M*=p[i];
	for (int i=0;i<n;i++)	{
		ll w=M/p[i],d,y; //x=pi*k1+a + w*k2
		exgcd(p[i],w,d,y);
		x=(x+w*y*a[i])%M; //get k1, pi*k1=a (Mod w)
	}
	return (x+M)%M;
}

//EXTCRT
//x=a1(mod p1)
//x=a2(mod p2)
//...
ll china1(int n, ll a[], ll p[]){
	ll n1=p[0],a1=a[0],n2,a2,k1,k2,K,gcd,c,t;
	for (int i=1;i<n;i++){//依次合并方程
		n2=p[i],a2=a[i]; 
		c=a2-a1;
		gcd=exgcd(n1,n2,k1,k2); //n1*k1+n2*k2=gcd(n1,n2)
		if (c%gcd) return -1;
		K=c/gcd*k1;//n1*K+n2*(c/gcd*k2)=c
		t=n2/gcd; K=(K+t)%t; //K>=0
		a1+=n1*K;
		n1*=n2/gcd;
	}
	return a1;
}

//discrete logarithm
//a^x=b(mod p)
ll BSGS(ll a, ll b, ll p){
	int m,v,e=1;
	m=(int)sqrt(p+0.5);
	v=inv(qpow(a,m,p),p);
	map<int,int> x; //hash_map -> O(sqrt(N))
	x[1]=0;
	for (int i=1;i<m;i++){
		e=e*a%p;
		if (!x.count(e))
			x[e]=i;
	}
	for (int i=0;i<m;i++){
		if (x.count(b))
			return i*m+x[b];
		b=b*v%p;
	}
	return -1;
}
const ll p0[]={2,3,5,7,11,13,17,19,23,29,31};

//a^(p-1)=1 (mod p) , x^2=1 (mod p) while x=1 or p-1
bool witness(ll a,ll n,ll r,ll s){
	ll x=qpow(a,r,n),pre=x;
	for (int i=0;i<s;i++){
		x=qmul(x,x,n);
		if (x==1 && pre!=1 && pre!=n-1) return 0;
		pre=x;
	}
	if (x!=1) return 0;
	return 1;
}

bool MillerRabin(ll n){
	if (n<=1) return 0;
	if (n==2) return 1;
	if (n%2==0) return 0;
	ll r=n-1,s=0;
	while (!(r&1)) r>>=1,s++;
	for (int i=0;i<10;i++){
		if (p0[i]==n) return 1;
		if (!witness(p0[i],n,r,s)) return 0;
	}
	return 1;
}

ll pol_rho(ll n,ll c){
	ll k=2,x=rand()%n,y=x,p=1;
	for (ll i=1;p==1;i++){
		x=(qmul(x,x,n)+c)%n;
		p=y>x?y-x:x-y;
		p=gcd(n,p);
		if (i==k)
			y=x,k+=k;
	}
	return p;
}

vector<int> primes;
void spiltprime(ll n){
	if (n==1) return;
	if (MillerRabin(n)) {primes.push_back(n); return;} //n is prime factor
	ll t=n;
	while (t==n) t=pol_rho(n,rand()%(n-1));
	spiltprime(t); spiltprime(n/t);
}

struct Q{
	ll p,q;
	Q(ll x){p=x;q=1;}
	void operator=(ll x){p=x;q=1;}
	void simp(){ll t=gcd(p,q); if (t!=1) p/=t,q/=t; if (q<0) p=-p,q=-q;}
	void operator+=(const Q &v){p=p*v.q+v.p*q;q*=v.q;simp();}
	void operator-=(const Q &v){p=p*v.q*v.p*q;q*=v.q;simp();}
	void operator*=(const Q &v){p*=v.p;q*=v.q;simp();}
	void operator/=(const Q &v){p*=v.q;q*=v.p;simp();}
	Q operator+(const Q &y){Q x(*this);x+=y;return x;}
	Q operator-(const Q &y){Q x(*this);x-=y;return x;}
	Q operator*(const Q &y){Q x(*this);x*=y;return x;}
	Q operator/(const Q &y){Q x(*this);x/=y;return x;}
	bool operator<(const Q &v){return p*v.q<v.p*q;}
	double d(){return (double)p/q;}
};
//calc C(n,m), means select m object from n object
namespace LUCAS{
const ll p=10007;
ll fact[p],vfact[p];
ll comb(ll n,ll m){
	if (n<m) return 0;
	return fact[n]*vfact[n-m]%p*vfact[m]%p;
}
ll lucas(ll n,ll m){
	if (m==0) return 1;
	return lucas(n/p,m/p)*comb(n%p,m%p)%p;
}
void pre(){
	fact[0]=1;
	for (int i=1;i<p;i++) fact[i]=fact[i-1]*i%p;
	for (int i=0;i<p;i++) vfact[i]=qpow(fact[i], p-2, p);
}
}
namespace NumericalMethod{
double eps=1e-8;
double f(double x){
	return x;
}
//Three division method, require a convex function
double fargmax(double l, double r){
	while (r-l>eps){
		double d1=(l+l+r)/3,d2=(l+r+r)/3;
		if (f(d1)>f(d2)) r=d2;
		else l=d1;
	}
	return r;
}

//---simpson_intergrate---
double simpson(double l,double r){
	return (r-l)*(f(l)+4*f((l+r)/2)+f(r))/6;	
}
double asr(double l, double r, double ans){
	double mid=(l+r)/2;
	double left=simpson(l,mid),right=simpson(mid,r);
	if (fabs(left+right-ans)<eps) return left+right;
	else return asr(l,mid,left)+asr(mid,r,right);
}
//use simpson method
//warning: avoid odd point
double intergrate(double l, double r){return asr(l,r,simpson(l,r));}

//---SA----
const int maxn=10010;
struct Point{
	double x,y;
}a[maxn];
//Energy function demo
double w[maxn]; int n; 
double E(Point p){
	double ans=0;
	inc(i,n)
		ans+=sqrt((p.x-a[i].x)*(p.x-a[i].x)+(p.y-a[i].y)*(p.y-a[i].y)) * w[i];
	return ans;
}
/*
argmin_SimulateAnneal(): get argmin E(x), while E is not a convex function.
To speed up, the energy function should be nearly smooth and partial convex.
Point: n-d vector, the dimension cannot be too large.
t0:start temprature
tend: end temprature
delta: temprature reduce factor
*/
double rand01() {return (rand()+0.5)/RAND_MAX;}
Point ans; double anse=1e12;
void argmin_SimulateAnneal(double t0=5000, double tend=1e-6, double delta=0.99){
	double t=t0, ne=1e12; //current state energy
	Point p((Point){0,0});
	while (t>=tend){
		Point p1((Point){p.x+(rand01()*t-t/2), p.y+(rand01()*t-t/2)});
		double te=E(p1);
		//cout<<te-ne<<' '<<ne<<' '<<t<<' '<<exp((ne-te)/t)<<' '<<ans.x<<'\n';
		if (te<ne || 0 && exp((ne-te)/t)>rand01()) //disabled jumpout
			p=p1, ne=te; //update
		if (ne<anse)
			ans=p, anse=ne;//cout<<ans.x<<' '<<ans.y<<' '<<anse<<'\n';
		t*=delta;
	}
}
}

namespace Cantor{
int fac[]={1,1,2,6,24,120,720,5040,40320,362880,3628800};
bool vis[20];
//get rank of permutation
//output range: [0,n!) 
int cantor(int n, int a[]){
	int ret=0;
	for (int i=0;i<n;i++){
		int t=0;
		for (int j=i+1;j<n;j++)
			if (a[i]>a[j]) t++;
		ret+=t*fac[n-i-1];
	}
	return ret;
}
//get kth permutation of {1..n}
//input range: [0,n!) 
void decantor(int n, int k, int ans[]){
	memset(vis,0,sizeof(vis));
	for (int i=0,j;i<n;i++){
		int t=k/fac[n-i-1];
		for (j=1;j<=n;j++)
			if (!vis[j])
				if (t==0) break;
				else t--;
		ans[i]=j;
		vis[j]=1;
		k%=fac[n-i-1];
	}
}
}

namespace UFSet{
const int maxn=100010;
int fa[maxn];
void clear(){
	for (int i=0;i<maxn;i++) fa[i]=i;
}
int fi(int x){
	if (fa[x]!=x)
		fa[x]=fi(fa[x]);
	return fa[x];
}
void un(int a, int b){
	int ta=fi(a),tb=fi(b);
	if (ta!=tb) fa[ta]=tb;
}
}

namespace Graph{

const int maxn=10010,maxm=100010,inf=0x3f3f3f3f;
int head[maxn],nxt[maxm],to[maxm],co[maxm],ec;
int n;
bool vis[maxn];
int dis[maxn],c[maxn];

void added(int x, int y, int c){
	ec++;
	nxt[ec]=head[x];
	head[x]=ec;
	to[ec]=y;
	co[ec]=c;
}

//wrost O(n^3), but as fast as dijkstra in random data.
int spfa(int s){
	queue<int> q;
	memset(dis,0x3f,sizeof(dis));
	dis[s]=0;
	memset(c,0,sizeof(c)); //judge nagetive loop
	memset(vis,0,sizeof(vis));
	q.push(s); vis[s]=1; c[s]=1;
	while (!q.empty())	{
		int u=q.front(); q.pop();
		vis[u]=0;
		for (int e=head[u];e;e=nxt[e]){
			int v=to[e];
			if (dis[u]+co[e]<dis[v]){
				dis[v]=dis[u]+co[e];
				if (!vis[v]){
					vis[v]=1;
					c[v]++;
					q.push(v);
					if (c[v]>n) return 0; //has nagetive
				}
			}
		}
	}
	return 1;
}
/*
judge negative circle
!-- Discarded, some reasons show it's time complexity is unreliable,
thought it runs fast in random data.
*/
bool spfa_dfsjudge(int u){
	vis[u]=1;
	for (int e=head[u];e;e=nxt[e]){
		int v=to[e];
		if (dis[u]+co[e]<dis[v]){
			dis[v]=dis[u]+co[e];
			if (vis[v] || spfa_dfsjudge(v)) return true;
		}
	}
	vis[u]=0;
	return false;
}

void dijk(int s){
	memset(dis,0x3f,sizeof(dis));
	memset(vis,0,sizeof(vis));
	dis[s]=0;
	priority_queue<pair<int,int> > qu;
	qu.push(make_pair(0,s));
	while (qu.size()){
		int u=qu.top().second, mc=-qu.top().first;
		qu.pop();
		if (vis[u]) continue;
		vis[u]=1;
		for (int e=head[u];e;e=nxt[e])
			if (!vis[to[e]] && mc+co[e]<dis[to[e]]){
				dis[to[e]]=mc+co[e];
				qu.push(make_pair(-dis[to[e]],to[e]));
			}
	}
}
int mp[maxn][maxn];
void dijk_original(int s){
	memset(dis,0x3f,sizeof(dis));
	memset(vis,0,sizeof(vis));
	dis[s]=0;
	for(int i=0;i<n;i++){
		int u=0,md=0x3f3f3f3f;
		for (int j=0;j<n;j++)
			if (!vis[j] && dis[j]<md)
				md=dis[j], u=j;
		vis[u]=1;
		for (int j=0;j<n;j++)
			if (!vis[j])
				dis[j]=min(dis[j],md+mp[u][j]);
	}
}
int d[maxn][maxn];
void floyd(){
	for (int k=0;k<n;k++)
		for (int i=0;i<n;i++)
			for (int j=0;j<n;j++)
				if (d[i][j]>d[i][k]+d[k][j])
					d[i][j]=d[i][k]+d[k][j];
}

//For undirected graph min loop
//!-- In directed graph, use floyd() and d[i][i].
int floyd_minc(){
	int minc=inf;
	for (int k=0;k<n;k++){
		for (int i=0;i<k;i++)
			for (int j=i+1;j<k;j++)
				minc=min(minc,d[i][j]+mp[i][k]+mp[k][j]);
		for (int i=0;i<n;i++)
			for (int j=0;j<n;j++)
				if (d[i][j]>d[i][k]+d[k][j])
					d[i][j]=d[i][k]+d[k][j];
	}
	return minc;
}

vector<int> ed[maxn];
bool ins[maxn];
int st[maxn],stn,dfn[maxn],low[maxn],from[maxn],idx,scn;
vector<int> scc[maxn];

void tarjan(int u){
	st[stn++]=u;
	ins[u]=1;
	dfn[u]=low[u]=++idx;
	for (int i=0;i<ed[u].size();i++)
		if (!dfn[ed[u][i]]){
			tarjan(ed[u][i]);
			low[u]=min(low[u],low[ed[u][i]]);
		}
		else if (ins[ed[u][i]])
			low[u]=min(low[u],low[ed[u][i]]); //either low or dfn are right
	if (low[u]==dfn[u]){
		int v;
		do{
			v=st[--stn];
			scc[scn].push_back(v);
			from[v]=scn;
			ins[v]=0;
		}while (u!=v);
		scn++;
	}
}
int qu[maxn],a[maxn],ind[maxn],sum[maxn],ans[maxn];
vector<int> ed2[maxn];

int circle_dp(){
	int n,m; scanf("%d%d",&n,&m);
	for (int i=0;i<n;i++) scanf("%d",a+i);
	for (int i=0;i<m;i++){
		int a,b; a--; b--;
		scanf("%d%d",&a,&b);
		ed[a].push_back(b);
	}
	inc(i,n)
		if (!dfn[i]) tarjan(i);
	inc(i,n)  //rebuild DAG
		for (int j=0;j<ed[i].size();j++)
			if (from[i]!=from[ed[i][j]])
				ed2[from[i]].push_back(from[ed[i][j]]),
				ind[from[ed[i][j]]]++;
	//for (int i=0;i<scn;i++,cout<<'\n') for (auto u:scc[i]) cout<<u<<' ';
	int head=0,tail=1;
	int tans=-1000000;
	for (int i=0;i<scn;i++) if (!ind[i]) qu[tail++]=i,ans[i]=sum[i],tans=max(tans,ans[i]);
	while (head<tail){
		int u=qu[head];
		for (int i=0;i<ed2[u].size();i++){
			int v=ed2[u][i];
			ind[v]--;
			ans[v]=max(ans[v],ans[u]+sum[v]),tans=max(tans,ans[v]);
			if (ind[v]==0) qu[tail++]=v;
		}
		head++;
	}
	cout<<tans<<'\n';
	return 0;
}

//mark dcc cut point
bool iscut[maxn];
void tarjan_point(int u, int fa){
	int ch=0; //sum of subtree link by this point
	low[u]=dfn[u]=++idx;
	for (int i=0;i<ed[u].size();i++){
		int v=ed[u][i];
		if (!dfn[v]){
			ch++;
			tarjan_point(v,u); //we can use siz[u] to record each size of subtree
			low[u]=min(low[u],low[v]);
			if (low[v]>=dfn[u]) iscut[u]=1;
		}
		else if (v!=fa)
			low[u]=min(low[u],dfn[v]); //dfn
	}
	if (fa<0 && ch==1) iscut[u]=0;
}
//dfs dcc block
int cnt,cucnt;
void dfs_dcc(int u, int dcn){
	vis[u]=dcn; 
	cnt++;
	for (int i=0;i<ed[u].size();i++){
		int v=ed[u][i];
		if (iscut[v] && vis[v]!=dcn) cucnt++,vis[v]=dcn; 
		if (!vis[v] && !iscut[i]) dfs_dcc(v, dcn);
	}
}
//cnt: inner point of current dcc block, cucnt: cut point in cur dcc block
void dcc_caller(){
	int dcn=0;
	icc(i,n) if (!vis[i] && !iscut[i]){
		dcn++; cnt=cucnt=0;
		dfs_dcc(i, dcn);
		//cnt, cucnt, ...
	}
}

int ansx[maxn],ansy[maxn],ansc;
void tarjan_ed(int u, int fa){
	low[u]=dfn[u]=++idx;
	for (int i=0;i<ed[u].size();i++){
		int v=ed[u][i];
		if (!dfn[v]){
			tarjan_ed(v,u);
			low[u]=min(low[u],low[v]);
			if (low[v]>dfn[u])
				ansx[ansc]=u,ansy[ansc++]=v;
		}
		else if (v!=fa)
			low[u]=min(low[u],dfn[v]);
	}
}

#ifdef NO_COMPILE
int kruskal(){
	using namespace UFSet;
	int n,m; scanf("%d%d",&n,&m);
	for (int i=1;i<=n;i++) fa[i]=i;
	for (int i=0;i<m;i++) scanf("%d%d%d",&ed[i].x,&ed[i].y,&ed[i].c);
	sort(ed,ed+m);
	int ans=0;
	for (int i=0;i<m;i++){
		int ta=fi(ed[i].x), tb=fi(ed[i].y);
		if (ta!=tb)
			ans+=ed[i].c,
			fa[ta]=tb;
	}
	cout<<ans<<'\n';
	return ans;
}
#endif
//heap opt prim, O((n+m)log(m))
int prim(){
	memset(dis,0x3f,sizeof(dis));
	memset(vis,0,sizeof(vis));
	dis[1]=0;
	priority_queue<pair<int,int> > qu;
	qu.push(make_pair(0,1));
	int ans=0;
	while (qu.size()){
		int u=qu.top().second,c=qu.top().first;
		qu.pop();
		if (vis[u]) continue;
		ans-=c;
		vis[u]=1;
		for (int e=head[u];e;e=nxt[e])
			if (!vis[to[e]]){
				dis[to[e]]=co[e];
				qu.push(make_pair(-co[e],to[e]));
			}
	}
	return ans;
}
//O(n^2)
int prim_original(){
	memset(dis,0x3f,sizeof(dis));
	memset(vis,0,sizeof(vis));
	dis[1]=0; int ans=0;
	for(int i=0;i<n;i++){
		int u=0,md=0x3f3f3f3f;
		for (int j=0;j<n;j++)
			if (!vis[j] && dis[j]<md)
				md=dis[j], u=j;
		vis[u]=1; ans+=md;
		for (int j=0;j<n;j++)
			if (!vis[j])
				dis[j]=min(dis[j],mp[u][j]);
	}
	return ans;
}
#ifdef NO_COMPILE
int deg[maxn],ansp[maxm],al,anse[maxm<<1],el;
//O(n+m), euler cycle
//the graph MUST BE only 0 or 2 odd node, and if there is 2 odd node, u must be odd node
void euler(int u){
	for (int e=head[u];e;e=ed[e].nxt){
		int v=ed[e].to;
		if (!ed[e].vis && !ed[e^1].vis){
			ed[e].vis=ed[e^1].vis=1;
			euler(v);
			anse[++el]=e;//ed
		}
	}
	ansp[++al]=u;
}
#endif
}

namespace Polynomial{
namespace FFT
{
typedef complex<double> cd;
const int maxl=(1<<20)+1;
const double pi=3.14159265358979;
int rev[maxl];
void get_rev(int bit){
	for (int i=0;i<(1<<bit);i++)
		rev[i]=(rev[i>>1]>>1)|((i&1)<<(bit-1));
}
void fft(cd a[], int n, int dft){
	for(int i=0;i<n;i++) if(i<rev[i]) swap(a[i],a[rev[i]]);
	for (int s=1;s<n;s<<=1){
		cd wn=exp(cd(0,pi*dft/s));
		for (int j=0;j<n;j+=s<<1){
			cd wnk(1,0);
			for (int k=j;k<j+s;k++){
				cd x=a[k],y=wnk*a[k+s];
				a[k]=x+y;
				a[k+s]=x-y;
				wnk*=wn;
			}
		}
	}
	if (dft==-1) for (int i=0;i<n;i++) a[i]/=n;
}
ll G=3,P=1004535809;
void ntt(ll *a, int n, int dft){
	for(int i=0;i<n;i++) if(i<rev[i]) swap(a[i],a[rev[i]]);
	for (int s=1;s<n;s<<=1){
		ll wn=qpow(G,dft==1?(P-1)/s/2:P-1-(P-1)/s/2,P);
		for (int j=0;j<n;j+=s<<1){
			ll wnk=1;
			for (int k=j;k<j+s;k++){
				ll x=a[k],y=wnk*a[k+s]%P;
				a[k]=(x+y)%P; //merge
				a[k+s]=(x-y+P)%P;
				wnk=wnk*wn%P;
			}
		}
	}
	if (dft==-1) {
		ll inv=qpow(n,P-2,P);
		for (int i=0;i<n;i++) a[i]=a[i]*inv%P;
	}
}
void conv(cd *fa, cd *fb, int s, cd *ret){
	static cd a[maxl],b[maxl];
	memcpy(a,fa,sizeof(ll)*s); memcpy(b,fb,sizeof(ll)*s);
	fft(a,s,1); fft(b,s,1);
	for (int i=0;i<s;i++) a[i]*=b[i];
	fft(a,s,-1);
	memcpy(ret,a,sizeof(ll)*s);
}
void conv(ll *fa, ll *fb, int s, ll *ret){
	static ll a[maxl],b[maxl];
	memcpy(a,fa,sizeof(ll)*s); memcpy(b,fb,sizeof(ll)*s);
	ntt(a,s,1); ntt(b,s,1);
	for (int i=0;i<s;i++) a[i]*=b[i];
	ntt(a,s,-1);
	memcpy(ret,a,sizeof(ll)*s);
}
int ans[maxl],_;
char s1[100010],s2[100010];
//fast mul
void mul(){
	static cd a[maxl],b[maxl];
	scanf("%s%s",s1,s2);
	int l1=strlen(s1),l2=strlen(s2);
	int s=2,bit=1;
	for (bit=1;(1<<bit)<l1+l2-1;bit++)s<<=1;
	for (int i=0;i<l1;i++) a[i]=s1[l1-i-1]-'0';
	for (int i=0;i<l2;i++) b[i]=s2[l2-i-1]-'0';
	conv(a,b,s,a);
	for (int i=0;i<s;i++) cout<<a[i]<<' '; cout<<'\n';
	for (int i=0;i<s;i++){
		ans[i]+=a[i].real();
		ans[i+1]+=ans[i]/10;
		ans[i]%=10;
	}
	int i;
	for (i=l1+l2;!ans[i]&&i>=0;i--);
	if (i==-1) printf("0");
	for (;i>=0;i--) printf("%d",ans[i]);
	putchar('\n');
}
ll P1=1004535809,P2=998244353,P3=469762049;
ll res[3][maxl];
//conv a sequence with mod p, while p<P1*P2*P3
void conv_mod(){
	static ll a[maxl],b[maxl];
	int l1,l2; ll p;
    rd(l1); rd(l2); l1++; l2++;
    int s=2,bit=1;
    for (bit=1;(1<<bit)<l1+l2-1;bit++)s<<=1;
	get_rev(bit);
    int r; rd(r); p=r;
    for (int i=0;i<l1;i++) rd(r),a[i]=r;
    for (int i=0;i<l2;i++) rd(r),b[i]=r;
    G=3,P=P1; conv(a,b,s,res[0]);
    G=3,P=P2; conv(a,b,s,res[1]);
    G=3,P=P3; conv(a,b,s,res[2]);
    ll M=P1*P2;
    for (int i=0;i<l1+l2-1;i++){
    	//printf("%lld %lld %lld \n",res[0][i],res[1][i],res[2][i]);
    	ll A=(qmul(res[0][i]*P2%M,inv(P2%P1,P1),M)+
			qmul(res[1][i]*P1%M,inv(P1%P2,P2),M))%M;
		ll K=((res[2][i]-A)%P3+P3)%P3*inv(M%P3,P3)%P3;
		//cout<<A<<' '<<K<<' ';
		printf("%lld ", (K%p*(M%p)+A)%p);
    }
}
}

const int maxn=2010;
ll x[maxn],y[maxn];
int n;
//O(n^2) get single point value
//if xi between 1~n, we can optimize it to O(n)
//if xi not in 1~n, we can still preprocess PIj (ki-x[j]+p)%p, 
//  then get multi point value in O(max(n^2,nm))
ll LangrangeInter(ll k, ll p){
    ll sum=0;
    for (int i=0;i<n;i++){
        ll s0=1;
        for (int j=0;j<n;j++)
            if (i!=j) s0=s0*(x[i]-x[j]+p)%p;
        s0=qpow(s0,p-2,p);
        for (int j=0;j<n;j++)
            if (i!=j) s0=s0*(k-x[j]+p)%p;
        sum=(sum+y[i]*s0)%p;
    }
	return sum;
}
}
namespace Expr{
//Easy experission, calc +-*/^()
#define CP cin.peek()
#define CG cin.get()
#define CS while (CP==' ') CG;

int S();
int V(){CS
	int ans=0;
	if (CP=='('){
		CG;
		ans=S();
		CS;CG;
	}
	else cin>>ans;
	return ans;
}
int U(){
	int ans=V(); CS;
	while (CP=='^'){
		CG;
		int v=V(),d=ans;
		if (v==0) ans=1;
		for (int i=1;i<v;i++)
			ans*=d;
	}
	return ans;
}
int T(){
	int ans=U(); CS;
	while (CP=='*' || CP=='/'){
		if (CG=='*') ans*=U();
		else ans/=U();
	}
	return ans;
}
int S(){
	int ans=0; CS;
	if (CP=='-'){
		CG; ans=-T();
	}
	else ans=T();
	CS;
	while (CP=='+' || CP=='-'){
		if (CG=='+') ans+=T();
		else ans-=T();
	}
	return ans;
}

#undef CG
#undef CP
#undef CS
}

namespace TreeArr{

const int maxn=100010;
int tr[maxn]; int n;
void add(int p, int x){for(;p<=n;p+=p&-p) tr[p]+=x;}
ll sum(int p){ll ret=0;for(;p;p-=p&-p) ret+=tr[p];return ret;}

//section add and section sum version 
template <typename X>    
struct tree_array{    
    struct tree_array_single{    
        X arr[maxn];    
        void add(int x,X n){while(x<=N)arr[x]+=n,x+=x&-x;}    
        X sum(int x){X sum=0;while(x)sum+=arr[x],x-=x&-x;return sum;}    
    }T1,T2;    
    void add(int x,X n){T1.add(x,n);T2.add(x,x*n);}      
    X sum(int x){return (x+1)*T1.sum(x)-T2.sum(x);}
public:
    void update(int L,int R,int n){add(L,n);add(R+1,-n);}  
    X query(int L,int R){return sum(R)-sum(L-1);}    
};
}

namespace BipartiteGraph{

const int maxn=500;
//Info: d[][] 2-d array is O(n^3), forward star is O(ne). 
//d[][]: n->m edge  ;  to[]: set m->n match index
int d[maxn][maxn],to[maxn],n,m;
bool vis[maxn];

//judge whether a graph is BipartiteGraph
bool judge(int u, int col){
	vis[u]=col;
	for (int i=0;i<n;i++)
		if (d[u][i] && (vis[i]==col || !vis[i] && !judge(i,-col)))
			return 0;
	return 1;
}

//index between 0..n-1, so must set to[] -1 before
bool xiong(int u){
	for (int i=0;i<m;i++)
		if (d[u][i] && !vis[i]){
			vis[i]=1;
			if (to[i]==-1 || xiong(to[i])){
				to[i]=u;
				return 1;
			}
		}
	return 0;
}
int match(){
	int ans=0;
	memset(to,-1,sizeof(to));
	for (int i=0;i<n;i++){
		memset(vis,0,sizeof(vis));
		if (xiong(i)) ans++;
	}
	return ans;
}
}

namespace SEGT{
const int MAXN=100010;

ll sum[MAXN<<2], tadd[MAXN<<2], tmul[MAXN<<2], a[MAXN];
ll n,m,p;
#define lc u+u+1
#define rc u+u+2
void build(int u, int l, int r){
	tmul[u]=1;
	if (l==r-1){
		sum[u]=a[l];
		return;
	}
	int mid=l+r>>1;
	build(lc,l,mid); build(rc,mid,r);
	sum[u]=(sum[lc]+sum[rc])%p;
}
void upd(int u, int l, int r){
	int mid=l+r>>1;
	sum[lc]*=tmul[u]; sum[lc]+=(mid-l)*tadd[u]; sum[lc]%=p;
	sum[rc]*=tmul[u]; sum[rc]+=(r-mid)*tadd[u]; sum[rc]%=p;
	tadd[lc]*=tmul[u]; tadd[lc]+=tadd[u]; tadd[lc]%=p;
	tmul[lc]*=tmul[u]; tmul[lc]%=p;
	tadd[rc]*=tmul[u]; tadd[rc]+=tadd[u]; tadd[rc]%=p;
	tmul[rc]*=tmul[u]; tmul[rc]%=p;
	tadd[u]=0; tmul[u]=1;
}
void mul(int u, int l, int r, int cl, int cr, ll c){
	if (cl<=l && cr>=r){
		tadd[u]*=c; tadd[u]%=p;
		tmul[u]*=c; tmul[u]%=p;
		sum[u]*=c; sum[u]%=p;
		return;
	}
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	if (cl<mid) mul(lc,l,mid,cl,cr,c);
	if (cr>mid) mul(rc,mid,r,cl,cr,c);
	sum[u]=(sum[lc]+sum[rc])%p;
}
void add(int u, int l, int r, int cl, int cr, ll c){
	if (cl<=l && cr>=r){
		tadd[u]+=c; tadd[u]%=p;
		sum[u]+=c*(r-l)%p; sum[u]%=p;
		return;
	}
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	if (cl<mid) add(lc,l,mid,cl,cr,c);
	if (cr>mid) add(rc,mid,r,cl,cr,c);
	sum[u]=(sum[lc]+sum[rc])%p;
}
ll ask(int u, int l, int r, int cl, int cr){
	if (cl<=l && cr>=r) return sum[u];
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	ll ret=0;
	if (cl<mid) ret+=ask(lc,l,mid,cl,cr);
	if (cr>mid) ret+=ask(rc,mid,r,cl,cr);
	return ret%p;
}
ll pointask(int u, int l, int r, int q){
	if (l==r-1) return sum[u];
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	if (l<mid) return pointask(lc,l,mid,q);
	return pointask(u,mid,r,q);
}

#undef lc
#undef rc

}


namespace FSEGT{
const int maxn=200010;
int sum[maxn<<5], root[maxn], lc[maxn<<5], rc[maxn<<5],trcnt;
int a[maxn],b[maxn];

void build(int &u, int l, int r){
	u=trcnt++;
	if (l==r-1) return;
	int mid=l+r>>1;
	build(lc[u],l,mid); build(rc[u],mid,r);
}
int mod(int u, int l, int r, int c){
	int v=trcnt++;
	lc[v]=lc[u]; rc[v]=rc[u]; sum[v]=sum[u]+1;
	if (l==r-1) return v;
	int mid=l+r>>1;
	if (c<mid) lc[v]=mod(lc[v],l,mid,c);
	else rc[v]=mod(rc[v],mid,r,c);
	return v;
}
int query(int u, int v, int l, int r, int q){
	int mid=l+r>>1, x=sum[lc[v]]-sum[lc[u]];
	if (l==r-1) return l;
	if (x>=q) return query(lc[u],lc[v],l,mid,q);
	return query(rc[u],rc[v],mid,r,q-x);
}
//ask: [l,r) kth number
int main(){
	int n,m;
	cin>>n>>m;
	for (int i=0;i<n;i++)
		scanf("%d", a+i),b[i]=a[i];
	sort(b,b+n);
	int n1=unique(b,b+n)-b;
	build(root[0],0,n1);
	for (int i=0;i<n;i++){
		int q=lower_bound(b,b+n1,a[i])-b;
		root[i+1]=mod(root[i],0,n1,q);
	}
	for (int i=0;i<m;i++){
		int l,r,q;
		scanf("%d%d%d",&l,&r,&q);
		printf("%d\n",b[query(root[l-1],root[r],0,n1,q)]);
	}
	return 0;
}
}

namespace NetFlow{
#define INF 0x3f3f3f3f
const int maxn=1003,maxm=10003<<4;
struct Edge{
	int to,nxt,cap,flow,cost;
}ed[maxm];
int head[maxn],ecnt=1,n,m;
void added(int a, int b, int cap){
	ed[++ecnt]=(Edge){b,head[a],cap,0,0};
	head[a]=ecnt;
	ed[++ecnt]=(Edge){a,head[b],0,0,0};
	head[b]=ecnt;
}
int s,t,a[maxn],fr[maxn],fp[maxn];
bool vis[maxn];
//deleted O(n^5)
int MF_FF(){
	int ans=0;
	while (1){
		memset(vis,0,sizeof(vis));
		memset(a,0,sizeof(a));
		a[s]=INF;
		queue<int> qu;
		qu.push(s);
		vis[s]=1;
		while (qu.size()){
			int u=qu.front(); qu.pop();
			if (u==t) break;
			for (int i=head[u];i;i=ed[i].nxt){
				int v=ed[i].to;
				if (!vis[v] && ed[i].cap>ed[i].flow){
					vis[v]=1;
					a[v]=min(a[u],ed[i].cap-ed[i].flow);
					fp[v]=u;
					fr[v]=i;
					qu.push(v);
				}
			}
		}
		if (!a[t]) break;
		ans+=a[t];
		for (int i=t;i!=s;i=fp[i]){
			ed[fr[i]].flow+=a[t];
			ed[fr[i]^1].flow-=a[t];
		}
	}
	return ans;
}
int now[maxn],num[maxn];
int isap_aug(int u, int f){
	if (u==t) return f;
	int ans=0;
	for (int i=now[u],v=ed[i].to;i;i=ed[i].nxt,v=ed[i].to)
		if (a[u]==a[v]+1){
			int w=isap_aug(v,min(f,ed[i].cap-ed[i].flow));
			ans+=w; f-=w; ed[i].flow+=w; ed[i^1].flow-=w;
			if (!f) return ans;
			now[u]=i;
		}
	if (!(--num[a[u]])) a[s]=n+1;
	++num[++a[u]]; now[u]=head[u];
	return ans;
}
int MF_isap(){
	memset(num,0,sizeof(num));
	memset(a,0,sizeof(a));
	for (int i=1;i<=n;i++) now[i]=head[i];
	static int qu[maxn];
	int ql,qr=1; qu[ql=0]=t;
	++num[a[t]=1];
	while (ql<qr){
		int u=qu[ql++];
		for (int i=head[u],v=ed[i].to;i;i=ed[i].nxt,v=ed[i].to)
			if (!a[v]) ++num[a[v]=a[u]+1],qu[++qr]=v;
	}
	int ret=isap_aug(s,INF);
	while (a[s]<=n) ret+=isap_aug(s,INF);
	return ret;
}

int dinic_dfs(int u, int f){
	int ans=0,w;
	if (u==t) return f;
	for (int i=now[u];i;i=ed[i].nxt){
		int v=ed[i].to;
		if (a[v]==a[u]+1 && ed[i].cap-ed[i].flow && (w=dinic_dfs(v,min(ed[i].cap-ed[i].flow,f)))){
			ans+=w;
			ed[i].flow+=w; ed[i^1].flow-=w;
			f-=w; if (f==0) return ans;
			now[u]=i;
		}
	}
	if (!ans) a[u]=-1;
	return ans;
}
int MF_dinic(){
	int ans=0;
	while (1){
		memset(vis,0,sizeof(vis));
		memset(a,0,sizeof(a)); //a: level
		queue<int> qu; qu.push(s); 
		vis[s]=1;
		while (qu.size()){ //BFS
			int u=qu.front(); qu.pop();
			if (u==t) break;
			for (int i=head[u];i;i=ed[i].nxt){
				int v=ed[i].to;
				if (!vis[v] && ed[i].cap>ed[i].flow){
					qu.push(v);
					a[v]=a[u]+1;
					fr[v]=i; fp[v]=u;
					vis[v]=1;
				}
			}
		}
		if (!vis[t]) break;
		for (int i=1;i<=n;i++) now[i]=head[i];
		ans+=dinic_dfs(s,INF);
	}
	return ans;
}

void added(int a, int b, int cap, int cost){
	ed[++ecnt]=(Edge){b,head[a],cap,0,cost};
	head[a]=ecnt;
	ed[++ecnt]=(Edge){a,head[b],0,0,-cost};
	head[b]=ecnt;
}
int dis[maxn];
int MCMF(){
	int ans=0;
	while (1){
		memset(vis,0,sizeof(vis));
		memset(dis,0x3f,sizeof(dis));
		queue<int> qu; qu.push(s);
		dis[s]=0; vis[s]=1;
		while (qu.size()){ //spfa
			int u=qu.front(); qu.pop(); vis[u]=0;
			for (int i=head[u];i;i=ed[i].nxt){
				int v=ed[i].to;
				if (ed[i].flow<ed[i].cap && dis[v]>dis[u]+ed[i].cost){
					dis[v]=dis[u]+ed[i].cost;
					fr[v]=i; fp[v]=u;
					if (!vis[v]){
						vis[v]=1;
						qu.push(v);
					}
				}
			}
		}
		if (dis[t]==INF) break;
		int mc=INF;
		for (int i=t;i!=s;i=fp[i]) mc=min(mc,ed[fr[i]].cap-ed[fr[i]].flow);
		for (int i=t;i!=s;i=fp[i]){
			ed[fr[i]].flow+=mc;
			ed[fr[i]^1].flow-=mc;
			ans+=mc*ed[fr[i]].cost;
		}
	}
	return ans;
}
//dijkstra version, but seems slower than before?
int h[maxn];
int MCMF_dijk(){
	memset(h,0,sizeof(h)); //set h[all vertex] to 0
	int ans=0;
	while (1){
		priority_queue<pair<int,int>> qu;
		memset(dis,0x3f,sizeof(dis));
		dis[s]=0; qu.push({0,s});
		while (!qu.empty()){
			int du=-qu.top().first, u=qu.top().second;
			qu.pop();
			if (dis[u]<du) continue;
			for (int i=head[u],v=ed[i].to;i;i=ed[i].nxt,v=ed[i].to)
				if (ed[i].flow<ed[i].cap && dis[v]>dis[u]+ed[i].cost+h[u]-h[v]){
					dis[v]=dis[u]+ed[i].cost+h[u]-h[v];
					fp[v]=u; fr[v]=i;
					qu.push({-dis[v],v});
				}
		}
		if (dis[t]>INF/3) break;
		for (int i=0;i<=n;i++) h[i]+=dis[i];
		int mc=INF;
		for (int i=t;i!=s;i=fp[i]) mc=min(mc,ed[fr[i]].cap-ed[fr[i]].flow);
		for (int i=t;i!=s;i=fp[i]){
			ed[fr[i]].flow+=mc;
			ed[fr[i]^1].flow-=mc;
			ans+=mc*ed[fr[i]].cost;
		}
	}
	return ans;
}

#undef INF
}

namespace StringHash{
//double module hash
typedef unsigned long long ll;
const ll m1=1000000007;
const int maxn=1000010;
ll h1[maxn],h2[maxn],b1[maxn],b2[maxn];
void pre(){
	b1[0]=b2[0]=1;
	inc(i,maxn-1)
		b1[i+1]=b1[i]*131%m1,
		b2[i+1]=b2[i]*137;
}
void gethash(char *s, int l){
	h1[l]=h2[l]=0;
	dec(i,l){
		h1[i]=(h1[i+1]*131+s[i])%m1;
		h2[i]=h2[i+1]*137+s[i];
		//cout<<h1[i]<<' '<<b1[i]<<'\n';
	}
}
//get substring [l,r) hash value
pair<ll,ll> substr(int l, int r){
	ll r1=h1[l]+m1-h1[r]*b1[r-l]%m1; if (r1>=m1) r1-=m1;
	ll r2=h2[l]-h2[r]*b2[r-l];
	return {r1,r2};
}
}

namespace KMP{
const int maxn=1000010;

int kmp[maxn];
//s is a short partten string
char s[maxn]; int sl; 
void getkmp(){
	int j=0,k=-1;
	kmp[0]=-1;
	while (j<sl)
		if (k==-1 || s[j]==s[k])
			kmp[++j]=++k;
		else
			k=kmp[k];
}
int kmp_idx(char *t, int tl){
	int i=0, j=0;
	while (i<sl && j<tl)
		if (i==-1 || s[i]==t[j])
			i++,j++;
		else
			i=kmp[i];
	if (i==sl) return j-sl;
	else return -1;
}
int kmp_cnt(char *t, int tl){
	int i=0, j=0, cnt=0;
	while (j<tl){
		if (i==-1 || s[i]==t[j])
			i++,j++;
		else
			i=kmp[i];
		if (i==sl) cnt++;
	}
	return cnt;
}
}

namespace ACAM{
const int maxn=100000,alpha=26; //maxn >= sigma len(si)
int ch[maxn][alpha],val[maxn],fail[maxn],lbl[maxn],len[maxn],pc=0;
int cnt[1000]; //str appear times, first element is 1
int strc=0;
void clear(){
	pc=0; strc=0;
	memset(ch,0,sizeof(ch));
	memset(fail,0,sizeof(fail));
	memset(val,0,sizeof(val));
	memset(lbl,0,sizeof(lbl));
}
//Trie construct
void ins(char *s){
	int l=strlen(s), cur=0;
	for (int i=0;i<l;i++){
		int v=s[i]-'a';
		if (!ch[cur][v]) ch[cur][v]=++pc;
		cur=ch[cur][v];
		len[cur]=i+1;
	}
	strc++;
	lbl[cur]=strc;
	val[cur]++;
}
int qu[maxn];
//fail edge add
void build(){
	int qh=0,qt=0;
	for (int i=0;i<alpha;i++)
		if (ch[0][i]) fail[ch[0][i]]=0,qu[qt++]=ch[0][i];
	while (qh<qt){
		int u=qu[qh];qh++;
		for (int i=0;i<alpha;i++)
			if (ch[u][i])
				fail[ch[u][i]]=ch[fail[u]][i],qu[qt++]=ch[u][i];
			else
				ch[u][i]=ch[fail[u]][i]; //opt, move to fail auto. Attention: the multi fail jump will be emitted
	}
}
//count how many mode str appeared in s as substr
int appear(char *s){
	int l=strlen(s),cur=0,ans=0;
	for (int i=0;i<l;i++){
		cur=ch[cur][s[i]-'a'];
		for (int t=cur;t && ~val[t];t=fail[t]) //the opt trans emitted fail jump chain, do it when necessary
			ans+=val[t],val[t]=-1;
	}
	return ans;
}
//count each mode str in s
void cntall(char *s){
	int l=strlen(s),cur=0;
	memset(cnt,0,sizeof(cnt));
	for (int i=0;i<l;i++){
		cur=ch[cur][s[i]-'a'];
		for (int t=cur;t;t=fail[t]) //the opt trans emitted fail jump chain, do it when necessary
			cnt[lbl[t]]++;
	}
}
}

namespace SA{
//sa: pos of ith rk suf, rk: rk of i pos suf, a: s0-'a', h: height(adj LCP)
//t1,t2,c: temp array
int t1[N],t2[N],sa[N],h[N],rk[N],c[N],a[N];
int n,m;
void calcsa(){
	int *x=t1,*y=t2,p=0,f=0;
	icc(i,m) c[i]=0;        
	icc(i,n) c[x[i]=a[i]]++;  //first char sort
	icc(i,m) c[i]+=c[i-1];
	dcc(i,n) sa[c[x[i]]--]=i; //pos of ith first char
	for (int i=1;i<=n && p<=n;i<<=1){
		p=0;
		rpp(j,n-i+1,n) y[++p]=j;  //remain part
		icc(j,n) if (sa[j]>i) y[++p]=sa[j]-i; //main part
		icc(j,m) c[j]=0;
		icc(j,n) c[x[y[j]]]++;
		icc(i,m) c[i]+=c[i-1];
		dcc(j,n) sa[c[x[y[j]]]--]=y[j]; //sort, use dcc because sort should be stable
		swap(x,y);x[sa[1]]=p=1; 
		rpp(j,2,n) x[sa[j]]=y[sa[j]]==y[sa[j-1]]&&y[sa[j]+i]==y[sa[j-1]+i]?p:++p; //refill key
		m=p;
	}
	icc(i,n) rk[sa[i]]=i;
	icc(i,n){
		int j=sa[rk[i]-1];
		if (f) f--; while (a[i+f]==a[j+f]) f++;
		h[rk[i]]=f;
	}
}

char s0[N];
int main(){
	scanf("%s",s0); int l=strlen(s0);
	inc(i,l) a[++n]=s0[i]-' ';
	m=200;
	calcsa();
	icc(i,n) printf("%d ",sa[i]);
	return 0;
}
}

namespace SAM{
const int maxn=100010,alpha=26;

//max state cnt: 2*strlen-1
//max transfer cnt: 3*strlen-4
struct Node{
	int l,num; bool vis;
	Node *p, *tr[alpha];
	//vector<Node *> ch;
	void set(int _l){l=_l;memset(tr,0,sizeof(tr));p=0;num=1;vis=0;/*ch.clear();*/}
}nodes[maxn<<1];
int nodec;
Node *root;
Node *open(int l){
	nodes[nodec++].set(l);
	return nodes+nodec-1;
}
void build(char *s, int l){
	Node *cur;
	cur=root=open(0);
	for (int i=0;i<l;i++){
		int x=s[i]-'a';
		Node *p=cur;
		cur=open(i+1);
		for (;p && !p->tr[x];p=p->p)
			p->tr[x]=cur;
		if (!p) cur->p=root;
		else{
			Node *q=p->tr[x];
			if (p->l+1==q->l) cur->p=q;
			else{
				Node *r=open(-1); r[0]=q[0]; r->l=p->l+1;
				q->p=r; cur->p=r; r->num=0;
				for (;p && p->tr[x]==q;p=p->p) p->tr[x]=r;
			}
		}
	}
}
//get substr last position
int pos(Node *u, char *s){
	if (*s==0) return u->l;
	if (!u->tr[*s-'a']) return -1;
	return pos(u->tr[*s-'a'],s+1);
}
//count substr
int cnt(Node *u, char *s){
	if (*s==0) return u->num;
	if (!u->tr[*s-'a']) return 0;
	return cnt(u->tr[*s-'a'],s+1);
}

int t[maxn],r[maxn], s0l; //t:temp, r:rank(ith element pos)
//init |right(s)| before cnt
void initnum(){
	inc(i,nodec) t[nodes[i].l]++;
	rep(i,1,s0l+1) t[i]+=t[i-1];
	inc(i,nodec) r[--t[nodes[i].l]]=i; //sort by count
	per(i,nodec,1) nodes[r[i]].p->num+=nodes[r[i]].num; //dp
}
int lcs(char *x1){
	int lcs=0, ans=0, xl=strlen(x1);
	Node *p=root;
	inc(i,xl){
		int x=x1[i]-'a';
		if (p->tr[x]){
			lcs++;
			p=p->tr[x];
			ans=max(ans,lcs);
			continue;
		}
		for (;p && !p->tr[x];p=p->p);
		if (!p) p=root,lcs=0;
		else{
			lcs=p->l+1;
			p=p->tr[x];
		}
		ans=max(ans,lcs);
	}
	return ans;
}
}

//mulit-str SAM
namespace GSAM{
struct Node{
	int l, num, las, vis;
	Node *p;
	map<int,Node*> tr; //more time, less memory
	//int tr[26];
}nodes[maxn<<1];
int nodec;
Node *open(int l){
	nodes[nodec++].l=l;
	return nodes+nodec-1;
}
Node *root=open(0);
void build(int *s, int l){
	Node *cur=root;
	for (int i=0;i<l;i++){
		int x=s[i];
		if (cur->tr.count(x)){  //transfer existed
			cur=cur->tr[x];
			continue;
		}
		Node *p=cur;
		cur=open(i+1);
		for (;p && !p->tr.count(x);p=p->p)
			p->tr[x]=cur;
		if (!p) cur->p=root;
		else{
			Node *q=p->tr[x];
			if (p->l+1==q->l) cur->p=q;
			else{
				Node *r=open(-1); r[0]=q[0]; r->l=p->l+1;
				q->p=r; cur->p=r; r->num=0;
				for (;p && p->tr[x]==q;p=p->p) p->tr[x]=r;
			}
		}
	}
}
int len[200010],tot;
vector<int> str[200010];
int ts[200010];
int ans[200010];
//calc how many mode str appear in each query
void upd1(Node *u, int col){ 
	for (;u->las!=col && u!=root;u=u->p)
		u->las=col, u->num++;
}
//calc ecah mode str appear how many query
void upd2(Node *u, int col){ 
	for (;u->las!=col && u!=root;u=u->p)
		u->las=col,ans[col]+=u->vis;
}
//n: ptn str, m: query str
int main(){
	int n,m; cin>>n>>m;
	for (int i=0;i<n;i++){
		++tot;
		scanf("%d", len+tot);
		for (int j=0;j<len[tot];j++){
			scanf("%d",ts+j);
			str[tot].push_back(ts[j]);
		}
		build(ts,len[tot]);
	}
	for (int i=1;i<=tot;i++){
		Node *cur=root;
		for (int j=0;j<len[i];j++)
			cur=cur->tr[str[i][j]],
			upd1(cur,i);
	}
	for (int i=0;i<m;i++){
		int l,x; bool flag=1;
		scanf("%d",&l);
		Node *cur=root;
		for (int j=0;j<l;j++){
			scanf("%d",&x);
			if (flag)
				if (cur->tr.count(x))
					cur=cur->tr[x];
				else //no transfer
					flag=0;
		}
		if (flag)
			printf("%d\n",cur->num),
			cur->vis++;
		else
			printf("0\n");
	}
	for (int i=0;i<nodec;i++) nodes[i].las=0; //!-- clear
	for (int i=1;i<=tot;i++){
		Node *cur=root;
		for (int j=0;j<len[i];j++)
			cur=cur->tr[str[i][j]],
			upd2(cur,i);
	}
	for (int i=1;i<=tot;i++)
		printf("%d ",ans[i]);
	return 0;
}
}

namespace Manacher{
const int maxn=10000000;
//p[]: max palindrome len at pos i
int p[maxn<<1];char s[maxn<<1],s0[maxn];
int sl,s0l;
int manacher(){
    s0l=strlen(s0);
    sl=1; s[0]='$'; s[1]='#';
    inc(i,s0l) s[++sl]=s0[i],s[++sl]='#';
    s[++sl]=0;
    int mx=0,mi=0,ans=0; //mx: max cur pstr right pos, mi: max cur pstr center pos
    rep(i,1,sl){
        p[i]=i<mx?min(p[mi*2-i], mx-i):1;
        while (s[i-p[i]]==s[i+p[i]]) p[i]++;
        if (mx<i+p[i]) mi=i,mx=i+p[i];
        ans=max(ans,p[i]-1);
    }
    return ans;
}
}

namespace PAM{
const int maxn=2000500;

//ch[x]: if cur pstr is a, the ch is xax.  len: len of cur pstr
//fail: longest pstr suffix of cur point.  cnt: count of this pstr.
struct Node{
    int ch[10],fail,len;
	int cnt;
}node[maxn];
int nodec,cur, len[maxn];
char s[maxn];

void pre(){
    node[10].fail=1; node[1].len=-1;
    nodec=2;cur=0;
}
void insert(int p){
    int j, x=s[p]-'0';
    while(s[p-node[cur].len-1]!=s[p])cur=node[cur].fail; //find ch
    if(!node[cur].ch[x]){
        node[nodec].len=node[cur].len+2;
        j=node[cur].fail;
        while(s[p-node[j].len-1]!=s[p])j=node[j].fail; //find fail
        node[nodec].fail=node[j].ch[x];
        node[cur].ch[x]=nodec;
        cur=nodec;
		nodec++;
    }
    else cur=node[cur].ch[x];
    len[p]=node[cur].len;
	node[cur].cnt++;
}
char ts[maxn];
void dfs1(int u, int deep){
	cout<<ts<<' '<<node[u].len<<'\n'; //cur node
	for (int i=0;i<10;i++)
		if (node[u].ch[i]){
			ts[deep]=i+'0';
			dfs1(node[u].ch[i],deep+1);
		}
}
int main(){
	pre();
	scanf("%s",s); int l=strlen(s);
	for (int i=0;i<l;i++) insert(i);
	for (int i=nodec-1;i>0;i--) 
		node[node[i].fail].cnt+=node[i].cnt;
	dfs1(0,0); //even pstr
	dfs1(1,0); //odd pstr
	return 0;
}
}

namespace Heap{
//Alorithm heap
//Run Fast
const int maxn=1000001;
int heap[maxn+1],hc;
int demo(){
    int n; rd(n);
    for (int i=0;i<n;i++){
        int c; rd(c);
        if (c==1){     //insert
            int x; rd(x);
            heap[hc++]=-x;
            push_heap(heap,heap+hc);
        }
        else if (c==2) //min element
            printf("%d\n",-heap[0]);
        else           //delete
            pop_heap(heap,heap+hc),hc--;
    }
    return 0;
}
}

namespace Treap{
//TT: an ordered struct
typedef int TT;
const int maxn=100001;
struct Node{
	//x: number, s: sum size of cur and subtree, cnt: cnt of cur num
	Node *c[2];
	TT x;
	int s,r,cnt;
	Node(TT _x){c[0]=c[1]=0;s=cnt=1;x=_x;r=rand();}
	Node(){};
}tree[maxn<<1];
#define lc u->c[0]
#define rc u->c[1]
#define lcs (lc?lc->s:0)
#define rcs (rc?rc->s:0)
int trcnt=0;
Node *open(TT x){
	tree[trcnt++]=Node(x);
	return tree+trcnt-1;
}
void upd(Node *u){
	u->s=lcs+rcs+u->cnt;
	//more updates...
}
//rt: set lc to root
void rot(Node* &u, int d){ //0 lt, 1 rt
	Node *t=u->c[d^1]; u->c[d^1]=t->c[d]; t->c[d]=u;
	t->s=u->s; upd(u); u=t;
}
void ins(Node* &u, TT x){
	if (!u){u=open(x);return;}
	if (x==u->x) {u->cnt++;u->s++; return;}
	int d=x>u->x; u->s++;
	ins(u->c[d],x);
	if (u->c[d]->r>u->r) rot(u,d^1);
}
void delx(Node* &u, TT x){
	if (!u) return;
	if (x==u->x){
		if (u->cnt>1) u->cnt--, u->s--;
		else if (!lc || !rc) u=max(lc,rc);
		else{
			rot(u,lc->r>rc->r);
			u->s--,delx(u->c[u->x<x],x);
		}
	}
	else u->s--,delx(u->c[u->x<x],x);
}
int rk(Node *u, TT x){
	if (!u) return 0;
	if (u->x==x) return lcs + 1;
	if (u->x<x) return lcs + u->cnt + rk(rc,x);
	else return rk(lc, x);
}
//get point by element
Node* findx(Node *u, TT x){
	if (!u) return 0;
	if (x==u->x) return u;
	return findx(u->c[u->x<x],x);
}
//get point by rank
//r=(1~tree_size)
Node* findr(Node *u, int r){
	if (!u) return 0;
	if (r<=lcs) return findr(lc,r);
	r-=lcs;
	if (r<=u->cnt) return u;
	r-=u->cnt;
	return findr(rc,r);
}
TT pred(Node *u, TT x){
	if (!u) return -0x3f3f3f3f;
	if (u->x<x) return max(u->x,pred(rc,x));
	else return pred(lc,x);
}
TT succ(Node *u, TT x){
	if (!u) return 0x3f3f3f3f;
	if (x<u->x) return min(u->x,succ(lc,x));
	else return succ(rc,x);
}
void dfs(Node *u, int deep=0){
	if (lc) dfs(lc,deep+1);
	for (int i=0;i<deep;i++) cout<<"   ";
	cout<<u->x<<' '<<u->s<<'\n';
	if (rc) dfs(rc,deep+1);
}
void caller(){
	Node *root=0;
	int T;cin>>T;
	while (T--)	{
		int c,x; scanf("%d%d",&c,&x);
		if (c==1) ins(root,x);
		if (c==2) delx(root,x);
		if (c==3) cout<<rk(root,x)<<'\n';
		if (c==4) cout<<findr(root,x)->x<<'\n';
		if (c==5) cout<<pred(root,x)<<'\n';
		if (c==6) cout<<succ(root,x)<<'\n';
		//dfs(root),cout<<'\n';
	}
}
#undef lc
#undef rc
#undef lcs
#undef rcs
}
namespace Splay{
const int maxn=100010;

int val[maxn],siz[maxn],ch[maxn][2],pa[maxn],cnt[maxn];
bool rev[maxn];
int root,trcnt;
#define lc ch[u][0]
#define rc ch[u][1]
//pushup
void upd(int u){
	siz[u]=cnt[u]+siz[lc]+siz[rc];
}
//lazy tags
void pushdown(int u){
	if (rev[u]){
		rev[lc]^=1;rev[rc]^=1;
		swap(lc,rc);
		rev[u]=0;
	}
}
void rot(int u, int c){
	int p=pa[u];
	ch[p][!c]=ch[u][c];
	pa[ch[u][c]]=p; pa[u]=pa[p];
	if (pa[u]) ch[pa[p]][ch[pa[p]][1]==p]=u;
	ch[u][c]=p; pa[p]=u;
	upd(p); upd(u);
}
//u->under s
void splay(int u, int s){
	while (pa[u]!=s){
		int p=pa[u],pp=pa[p];
		if (pp==s) rot(u,ch[p][0]==u);
		else{
			int c=(ch[pp][0]==p);
			if (ch[p][c]==u) rot(u,!c); else rot(p,c);
			rot(u,c);
		}
	}
	if (s==0) root=u;
}
//rank k->under s
void rk(int k, int s=0){
	int u=root;
	assert(k>=1 && k<=siz[root]);
	while (1){
		pushdown(u);
		if (k<=siz[lc]) u=lc;
		else if (k>siz[lc]+cnt[u]) k-=siz[lc]+cnt[u],u=rc;
		else break;
	}
	splay(u,s);
}
//x->under s
void fi(int x, int s=0){
	int u=root,p;
	while (x!=val[u] && u)
		p=u,u=ch[u][x>val[u]];
	if (u && x==val[u]) splay(u,s);
	else if (!u) splay(p,s);
}

#ifdef NO_COMPILE
//memory restricted open
int avail[maxn],avac;
void open(int &u, int x){
	u=avail[--avac];
	lc=rc=pa[u]=0;
	siz[u]=cnt[u]=1;
	val[u]=x;
}
void pre(){
	for (int i=1;i<maxn;i++) 
		avail[avac++]=maxn-i;
	open(root, -10086); // in section problem, add virtual point is convenient
	int r; open(r, -10086);
	ch[root][1]=r; pa[r]=root;
	upd(root);
}
void release(int u){
	if (!u) return;
	release(lc);
	release(rc);
	avail[avac++]=u;
}
#endif
void open(int &u, int x){
	u=++trcnt;
	lc=rc=pa[u]=0;
	siz[u]=cnt[u]=1;
	val[u]=x;
}
//root, value, parent
void ins(int &u, int x, int p){
	if (!u){
		open(u,x); pa[u]=p;
		splay(u,0);
		return;
	}
	if (val[u]==x){
		cnt[u]++,siz[u]++;
		splay(u,0);
		return;
	}
	else ins(ch[u][val[u]<x],x,u);
	upd(u);
}
//delete root
void del_(){
	int u=root;
	if (rc){
		root=rc; rk(1,0); //right, though it's hard to understand
		ch[root][0]=lc;
		if (ch[root][0]) pa[ch[root][0]]=root;
	}
	else root=lc;
	pa[root]=0;
	upd(root);
}
void del(int x){
	fi(x,0);
	if (val[root]==x)
		if (cnt[root]>1) cnt[root]--,siz[root]--;
		else del_();
}
int pred(int u, int x){
	if (!u) return -0x3f3f3f3f;
	if (val[u]<x) return max(val[u],pred(rc,x));
	return pred(lc,x);
}
int succ(int u, int x){
	if (!u) return 0x3f3f3f3f;
	if (x<val[u]) return min(val[u],succ(lc,x));
	return succ(rc,x);
}
//90 degree rotate debug print
void debug(int u=root, int deep=0){
	if (!u) return;
	debug(rc, deep+1);
	for (int i=0;i<deep;i++) cout<<"  ";
	cout<<val[u]<<' '<<siz[u]<<'\n';
	debug(lc, deep+1);
}
int n,m;
void dfs(int u){
	if (!u) return;
	pushdown(u);
	dfs(lc);
	if (val[u]>0 && val[u]<=n) cout<<val[u]<<' ';
	dfs(rc);
}
void mian(){
	int T; cin>>T;
	while (T--){
		int c,x; scanf("%d%d",&c,&x);
		if (c==1)
			ins(root,x,0);
		else if (c==2)
			del(x);
		else if (c==3){ //get rk of x
			fi(x,0); 
			cout<<siz[ch[root][0]]+1<<'\n';
		}
		else if (c==4){ //get k th
			rk(x,0);
			cout<<val[root]<<'\n';
		}
		else if (c==5){ //pred
			ins(root,x,0);
			rk(siz[ch[root][0]],0);
			cout<<val[root]<<'\n';
			del(x);
		}
		else if (c==6){ //succ
			ins(root,x,0);
			rk(siz[ch[root][0]]+cnt[root]+1,0);
			cout<<val[root]<<'\n';
			del(x);
		}
		//debug(root,0);
	}
}
int main(){ //reverse
	cin>>n>>m;
	for (int i=0;i<=n+1;i++) ins(root,i,0);
	for (int i=0;i<m;i++){
		int l,r; scanf("%d%d",&l,&r);
		rk(l,0); rk(r+2,root);
		rev[ch[ch[root][1]][0]]^=1;
		//debug(root,0);
	}
	dfs(root); putchar('\n');
	return 0;
}
#undef lc
#undef rc
}
namespace NRTreap{
const int maxn=100010;
typedef int TT;
struct Node{
	Node *c[2];
	TT x;
	int s, r;
	bool rev;
}tree[maxn<<1];
typedef pair<Node *,Node *> PD;
int trcnt;
Node *root;
Node *open(int x){
	tree[trcnt++]=(Node){0,0,x,1,rand(),0};
	return tree+trcnt-1;
}
#define lc u->c[0]
#define rc u->c[1]
#define lcs (lc?lc->s:0)
#define rcs (rc?rc->s:0)
void upd(Node *u){
	u->s=lcs+rcs+1;
}
void pushdown(Node *u){
	if (u->rev){
		if (lc) lc->rev^=1;
		if (rc) rc->rev^=1;
		swap(lc,rc);
		u->rev=0;
	}
}
Node *merge(Node *u, Node *v){
	if (!u || !v) return max(u,v);
	pushdown(u); pushdown(v);
	if (u->r<v->r) {rc=merge(rc,v);upd(u);return u;}
	else {v->c[0]=merge(u,v->c[0]);upd(v);return v;} 
}
PD split(Node *u, int k){
	if (!u) return MP((Node *)0,(Node *)0);
	pushdown(u);
	PD t;
	if (k<=lcs){
		t=split(lc,k);
		lc=t.second;
		upd(u);
		t.second=u;
	}
	else{
		t=split(rc,k-lcs-1);
		rc=t.first;
		upd(u);
		t.first=u;
	}
	return t;
}
int rk(Node *u, TT x){
	if (!u) return 0;
	if (u->x<x) return lcs + 1 + rk(rc,x);
	else return rk(lc, x);
}
int findr(Node *u, int r){
	if (!u) return 0;
	if (r<=lcs) return findr(lc,r);	r-=lcs;
	if (r==1) return u->x; r--;
	return findr(rc,r);
}
void ins(TT x){
	int k=rk(root,x);
	PD t=split(root,k);
	Node *u=open(x);
    root=merge(t.first,merge(u,t.second));
}
//t1.second is deleted
void del(TT x){
	int k=rk(root,x);
	PD t1=split(root,k),t2=split(t1.second,1);
	root=merge(t1.first,t2.second);
}
void debug(Node *u, int deep=0){
	if (lc) debug(lc,deep+1);
	for (int i=0;i<deep;i++) cout<<"   ";
	cout<<u->x<<' '<<u->s<<' '<<u->rev<<'\n';
	if (rc) debug(rc,deep+1);
}
int n;
void dfs(Node *u){
	if (!u) return;
	pushdown(u);
	dfs(lc);
	if (u->x>0 && u->x<=n) cout<<u->x<<' ';
	dfs(rc);
}
int mian(){
	int T;cin>>T;
	while (T--)	{
		int c,x; scanf("%d%d",&c,&x);
		if (c==1) ins(x);
		if (c==2) del(x);
		if (c==3) cout<<rk(root,x)+1<<'\n';
		if (c==4) cout<<findr(root,x)<<'\n';
		if (c==5) cout<<findr(root,rk(root,x))<<'\n';
		if (c==6) cout<<findr(root,rk(root,x+1)+1)<<'\n';
		//dfs(root),cout<<'\n';
	}
	return 0;
}
int main(){ //reverse
	int m;cin>>n>>m;
	for (int i=0;i<=n+1;i++) ins(i);
	for (int i=0;i<m;i++){
		int l,r; scanf("%d%d",&l,&r);
		PD x=split(root,l);
		PD y=split(x.second,r-l+1);
		y.first->rev^=1;
		root=merge(x.first,merge(y.first,y.second));
		//dfs(root); putchar('\n');
		//debug(root);
	}
	dfs(root); putchar('\n');
	return 0;
}
#undef lc
#undef rc
}
namespace ST{
const int maxn=100010;
int st[30][maxn],a[maxn];

int run(){
	int n,m; rd(n); rd(m);
	for (int i=1;i<=n;i++) rd(a[i]),st[0][i]=a[i];
	for (int i=1;i<30;i++)
		for (int j=1;j+(1<<(i-1))<=n;j++)
			st[i][j]=max(st[i-1][j],st[i-1][j+(1<<(i-1))]); //make
	for (int i=1;i<=m;i++){ //query
		int l,r; rd(l); rd(r);
		int x=log(r-l+1)/log(2)+0.00001;
		cout<<max(st[x][l],st[x][r+1-(1<<x)])<<'\n';
	}
	return 0;
}
};

namespace LinAlg{
const int maxn=1010,maxm=1010;
double a[maxn][maxm],b[maxn][maxn],ans[maxn];
int n,m;
const int eps=1e-7;
//require m=n+1
bool gauss_solve(){
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (maxl!=i) swap(a[i],a[maxl]);
		if (fabs(a[i][i])<eps) return 0; //no solution or infinity solution 
		for (int j=i+1;j<n;j++){
			double r=a[j][i]/a[i][i];
			for (int k=i;k<m;k++)
				a[j][k]-=r*a[i][k];
		}
		double r=a[i][i];
		for (int k=i;k<m;k++) a[i][k]/=r;
	}
	for (int i=n-1;i>=0;i--){
		ans[i]=a[i][n];
		for (int j=i+1;j<n;j++)
			ans[i]-=a[i][j]*ans[j];
	}
	return 1;
}
//n*n matrix
bool matinv(){
	memset(b,0,sizeof(b));
	for (int i=0;i<n;i++) b[i][i]=1;	
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (i!=maxl) swap(a[i],a[maxl]),swap(b[i],b[maxl]);
		if (fabs(a[i][i])<eps) return 0; //No trivil
		double r=a[i][i];
		for (int k=0;k<n;k++) a[i][k]/=r,b[i][k]/=r; //k start from 0
		for (int j=i+1;j<n;j++){
			double r=a[j][i]/a[i][i];
			for (int k=0;k<n;k++) //k start from 0
				a[j][k]-=r*a[i][k], b[j][k]-=r*b[i][k];
		}
	}
	return 1;
}
double det(){
	double ans=1;
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (i!=maxl) swap(a[i],a[maxl]),ans=-ans;
		if (fabs(a[i][i])<eps) return 0;
		for (int j=i+1;j<n;j++){
			double r=a[j][i]/a[i][i];
			for (int k=i;k<n;k++)
				a[j][k]-=r*a[i][k];
		}
	}
	for (int i=0;i<n;i++) ans*=a[i][i];
	return ans;
}
int matrank(){
	int l=0; //real line
	for (int i=0;i<m;i++){ //i: start pos
		int maxl=l;
		for (int j=l+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (l!=maxl) swap(a[l],a[maxl]);
		if (fabs(a[l][i])<eps) continue;
		for (int j=l+1;j<n;j++){
			double r=a[j][i]/a[l][i];
			for (int k=i;k<m;k++)
				a[j][k]-=r*a[i][k];
		}
		l++;
	}
	return l;
}
const ll p=19260817; //const is faster than normal variable
//int det with abs,mod
//used by Matrix-Tree theorem
//M-T theo: a[i][i]=-deg i, a[i][j]=cnt(i->j), n=|u|-1
//!--
ll detint_abs(ll **a){
	ll ans=1;
	for (int i=0;i<n;i++) for (int j=0;j<n;j++) if (a[i][j]<0) a[i][j]+=p;
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i;j<n;j++)
			if (a[j][i]) {maxl=j;break;}
		if (i!=maxl) swap(a[i],a[maxl]);
		if (a[i][i]==0) return 0;
		ans=ans*a[i][i]%p;
		int v=inv(a[i][i],p);
		for (int j=i;j<m;j++) a[i][j]=a[i][j]*v%p;
		for (int j=i+1;j<n;j++){
			if (!a[j][i]) continue;
			ll r1=a[j][i];
			for (int k=i;k<n;k++)
				a[j][k]=(a[j][k]-r1*a[i][k]%p+p)%p;
				//a[j][k]=(a[j][k]*a[i][i]-a[j][i]*a[i][k]%p+p)%p; //not good
		}
	}
	return ans; //not nagetive
}
//matinv with mod
//require m=2*n, result is a[i][(0..n-1)+n]
bool matinv_int(ll **a){
	m=2*n;
	//a[i][(0..n-1)+n]=0; //set to 0 
	for (int i=0;i<n;i++) a[i][i+n]=1;	
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i;j<n;j++)
			if (a[j][i]) {maxl=j;break;}
		if (i!=maxl) swap(a[i],a[maxl]);
		if (a[i][i]==0) return 0;
		int v=inv(a[i][i],p);
		for (int j=i;j<m;j++) a[i][j]=a[i][j]*v%p;
		for (int j=0;j<n;j++){
			if (!a[j][i] || j==i) continue;
			ll r1=a[j][i];
			for (int k=i;k<m;k++)
				a[j][k]=(a[j][k]-r1*a[i][k]%p+p)%p;
		}
	}
	return 1;
}
}

namespace LCA{
const int maxn=500010;
struct Edge{
	int to,nxt;
	//int w;
}ed[maxn<<1];
int head[maxn],ecnt;
void added(int x, int y){
	ed[++ecnt].to=y;
	ed[ecnt].nxt=head[x];
	head[x]=ecnt;
}
bool vis[maxn];
//online query, sum, minimax
namespace TreeMultiply{
int dep[maxn];
int pa[24][maxn];
//minn[24][maxn], sumv[24][maxn];
int lca(int u, int v){
	//int tu=u,tv=v,sum=0;
	if (dep[u]<dep[v]) swap(u,v);
	for (int k=23;k>=0;k--) 
		if (dep[pa[k][u]]>=dep[v]) u=pa[k][u]; //,sum+=sumv[k][u];
	if (u!=v){
		for (int k=23;k>=0;k--) 
			if (pa[k][u]!=pa[k][v]) u=pa[k][u],v=pa[k][v];//,sum+=sumv[k][u]+sum[k][v];
		u=pa[0][u];//sum+=sumv[0][u]+sumv[0][v];
	}
	//int lenth=dep[tu]+dep[tv]-2*dep[u];
	return u;
}
bool vis[maxn];
void dfs_deep(int u){
	vis[u]=1;
	for (int e=head[u];e;e=ed[e].nxt){
		int v=ed[e].to;
		if (!vis[v]){
			dep[v]=dep[u]+1; pa[0][v]=u;
			for (int k=1;pa[k-1][pa[k-1][v]];k++)
				pa[k][v]=pa[k-1][pa[k-1][v]];
			//	sumv[0][u]=minn[0][u]=maxn[0][u]=ed[e].w;
			//	for (int k=1;pa[k-1][pa[k-1][u]];k++) 
			//		sumv[k][u]=sumv[k-1][u]+sumv[k-1][pa[k-1][u]];
			dfs_deep(v);
		}
	}
}
//no stackoverflow
int qu[maxn];
void bfs_deep(int s){
	int qh=0,qt=1;
	qu[0]=s;dep[s]=1;vis[s]=1;
	while (qh<qt){
		int u=qu[qh];
		for (int e=head[u];e;e=ed[e].nxt){
			int v=ed[e].to;
			if (!vis[v]){
				dep[v]=dep[u]+1;
				vis[v]=1; pa[0][v]=u;
				for (int k=1;pa[k-1][pa[k-1][v]];k++)
					pa[k][v]=pa[k-1][pa[k-1][v]];
			//	sumv[0][u]=minn[0][u]=maxn[0][u]=ed[e].w;
			//	for (int k=1;pa[k-1][pa[k-1][u]];k++) 
			//		sumv[k][u]=sumv[k-1][u]+sumv[k-1][pa[k-1][u]];
				qu[qt++]=v;
			}
		}
		qh++;
	}
}
//n: node, m: query, s: root node
void process(){
	int n,m,s,a,b; cin>>n>>m>>s;
	//for (int i=1;i<=n;i++) rd(w[i]);
	for (int i=0;i<n-1;i++){
		rd(a); rd(b);
		added(a,b);
		added(b,a);
	}
	dep[s]=1;dfs_deep(s);
	//bfs_deep(s);
	for (int i=0;i<m;i++){
		rd(a); rd(b);
		printf("%d\n",lca(a,b));
	}
}
}
//offline lca
namespace tarjan{
using namespace UFSet;
int ans[maxn]; //lca point
struct QEdge{
	int to,nxt,s;
}qc[maxn<<1];
int quh[maxn],qcnt;
void addqu(int i,int a,int b){
	qc[++qcnt]=(QEdge){b,quh[a],i};
	quh[a]=qcnt;
	qc[++qcnt]=(QEdge){a,quh[b],i};
	quh[b]=qcnt;
}
//dfs, notify system stack
void tarjan(int u, int f){
	vis[u]=1;
	for (int e=head[u];e;e=ed[e].nxt){
		int v=ed[e].to;
		if (!vis[v])
			tarjan(v,u);
	}
	for (int i=quh[u];i;i=qc[i].nxt)
		if (vis[qc[i].to])
			ans[qc[i].s]=fi(qc[i].to);
	un(u,f);
}
//n: node, m: query, s: root node
void process(){
	int n,m,s,a,b; cin>>n>>m>>s;
	for (int i=0;i<=n;i++) fa[i]=i;
	for (int i=0;i<n-1;i++){
		rd(a); rd(b);
		added(a,b);
		added(b,a);
	}
	for (int i=0;i<m;i++){
		rd(a); rd(b);
		addqu(i,a,b);
	}
	tarjan(s,0);
	for (int i=0;i<m;i++)
		printf("%d\n",ans[i]);
}
}
}
namespace SplitTree{
const int maxn=100010;
struct Edge{
	int to,nxt;
}ed[maxn<<1];
int head[maxn],ecnt;
void added(int a, int b){
	ed[++ecnt]=(Edge){b,head[a]};
	head[a]=ecnt;
}
int sum[maxn<<2],tadd[maxn<<2],a[maxn],n,P,ucnt;
//son: heavy son, top: chain top, rk: segnode->treenode, id: treenode->segnode
int w[maxn],dep[maxn],fa[maxn],son[maxn],
	siz[maxn],rk[maxn],top[maxn],id[maxn];
#define lc u+u+1
#define rc u+u+2
void build(int u, int l, int r){
	if (l==r-1){
		sum[u]=a[rk[l]];
		return;
	}
	int mid=l+r>>1;
	build(lc,l,mid); build(rc,mid,r);
	sum[u]=(sum[lc]+sum[rc])%P;
}
void upd(int u, int l, int r){
	int mid=l+r>>1;
	sum[lc]+=(mid-l)*tadd[u]; sum[rc]+=(r-mid)*tadd[u];
	tadd[lc]+=tadd[u]; tadd[rc]+=tadd[u];
	sum[lc]%=P; sum[rc]%=P; tadd[lc]%=P; tadd[rc]%=P;
	tadd[u]=0;
}
void add(int u, int l, int r, int cl, int cr, int c){
	if (cl<=l && cr>=r){
		tadd[u]+=c; tadd[u]%=P;
		sum[u]+=c*(r-l)%P; sum[u]%=P;
		return;
	}
	if (tadd[u]) upd(u,l,r);
	int mid=l+r>>1;
	if (cl<mid) add(lc,l,mid,cl,cr,c);
	if (cr>mid) add(rc,mid,r,cl,cr,c);
	sum[u]=(sum[lc]+sum[rc])%P;
}
int ask(int u, int l, int r, int cl, int cr){
	if (cl<=l && cr>=r) return sum[u];
	if (tadd[u]) upd(u,l,r);
	int mid=l+r>>1;
	int ret=0;
	if (cl<mid) ret+=ask(lc,l,mid,cl,cr);
	if (cr>mid) ret+=ask(rc,mid,r,cl,cr);
	return ret%P;
}
void dfs1(int u, int f, int deep){
	fa[u]=f; dep[u]=deep; siz[u]=1;
	for (int i=head[u];i;i=ed[i].nxt){
		int v=ed[i].to; 
		if (v==f) continue;
		dfs1(v,u,deep+1);
		siz[u]+=siz[v];
		if (siz[v]>siz[son[u]]) son[u]=v;
	}
}
void dfs2(int u, int t){
	top[u]=t; id[u]=++ucnt; rk[ucnt]=u; 
	if (son[u]) dfs2(son[u],t);
	for (int i=head[u];i;i=ed[i].nxt){
		int v=ed[i].to;
		if (v!=son[u] && v!=fa[u]) dfs2(v,v);
	}
}
int askt(int x, int y){
	int ans=0;
	int fx=top[x],fy=top[y];
	while (fx!=fy)
		if (dep[fx]>=dep[fy]){
			ans=(ans+ask(0,0,n+1,id[fx],id[x]+1))%P;
			x=fa[fx],fx=top[x];
		}
		else{
			ans=(ans+ask(0,0,n+1,id[fy],id[y]+1))%P;
			y=fa[fy],fy=top[y];
		}
	if (id[x]>id[y]) swap(x,y);
	return (ans+ask(0,0,n+1,id[x],id[y]+1))%P;
}
void addt(int x, int y, int c){
	int fx=top[x],fy=top[y];
	while (fx!=fy)
		if (dep[fx]>=dep[fy]){
			add(0,0,n+1,id[fx],id[x]+1,c);
			x=fa[fx],fx=top[x];
		}
		else{
			add(0,0,n+1,id[fy],id[y]+1,c);
			y=fa[fy],fy=top[y];
		}
	if (id[x]>id[y]) swap(x,y);
	add(0,0,n+1,id[x],id[y]+1,c);
}
//r: root, c: 1-add chain, 2-sum chain, 3-add subtree, 4-sum subtree
void process(){
	int m,r,x,y;
	scanf("%d%d%d%d",&n,&m,&r,&P);
	for (int i=1;i<=n;i++) scanf("%d",a+i);
	for (int i=1;i<n;i++){
		scanf("%d%d",&x,&y);
		added(x,y); added(y,x);
	}
	dfs1(r,0,1);
	dfs2(r,r);
	build(0,0,n+1);
	for (int i=0;i<m;i++){
		int c,z; scanf("%d%d",&c,&x);
		if (c==1){
			scanf("%d%d",&y,&z);
			addt(x,y,z);
		}else if(c==2){
			scanf("%d",&y);
			printf("%d\n",askt(x,y));
		}
		else if (c==3){
			scanf("%d",&y);
			add(0,0,n+1,id[x],id[x]+siz[x],y);
		}
		else
			printf("%d\n",ask(0,0,n+1,id[x],id[x]+siz[x]));
	}
}
}
//data structure of xor sum
namespace XorBase{
//we may need <bitset> sometimes
typedef unsigned long long ll;
ll base[64];
void add(ll x){
	for (int i=63;i>=0;i--)
		if (x&1ull<<i)
			if (!base[i]){
				base[i]=x;
				return;
			}
			else x^=base[i];
}
//test if x can perform by xor sum
bool test(ll x){
	for (int i=63;i>=0;i--)
		if (x&1ull<<i)
			if (!base[i]) return 0;
			else x^=base[i];
	return 1;
}
//max xor sum
ll maxc(){
	ll ans=0;
	for (int i=63;i>=0;i--)
		if ((ans^base[i])>ans)
			ans^=base[i];
	return ans;
}
//min xor sum
ll minc(){for (int i=0;i<64;i++) if (base[i]) return base[i];}
//query kth max number
//k should not larger than 2^(dim linspan(x))
ll kth(ll k){
	ll ans=0,tmp[64],cnt=0;
    for(T i=0;i<64;i++){ //set matrix to simplest form
        for(int j=i-1;j>=0;j--)
			if(base[i]&1ull<<j) base[i]^=base[j];
        if(base[i])tmp[cnt++]=base[i];
    }
	for (int i=63;i>=0;i--)
		if (k&1ull<<i)
			ans^=tmp[i];
	return ans;
}
}

namespace CalcGeo{

typedef double db;
const db PI=acos(-1);

const db eps=1e-10;

int dcmp(db x){
	if (x<=-eps) return -1;
	return x>=eps;
}
bool eq(db x, db y){
	return fabs(x-y)<eps;
}
bool eq0(db x){
	return fabs(x)<eps;
}
#define Vec const vec &
#define Point const point &
struct vec{
	db x,y;
	vec():x(0),y(0){}
	vec(db x, db y):x(x),y(y){}
	vec(db theta):x(cos(theta)),y(sin(theta)){}
	bool operator==(Vec v) const{
		return eq(x,v.x) && eq(y,v.y);
	}
	db angle() const{
		return atan2(y,x);
	}
	bool operator<(Vec v) const{return x==v.x?y<v.y:x<v.x;}
	vec operator+(Vec v) const{return vec(x+v.x,y+v.y);}
	vec operator-(Vec v) const{return vec(x-v.x,y-v.y);}
	vec operator*(db a) const{return vec(x*a,y*a);}
	vec operator/(db a) const{return vec(x/a,y/a);}
	
	db operator^(Vec v) const{ //dot plus, note priority
		return x*v.x+y*v.y;
	}
	db operator*(Vec v) const{ //cross plus
		return x*v.y-y*v.x;
	}
	db operator!() const{
		return x*x+y*y;
	}
	db len() const{
		return sqrt(x*x+y*y);
	}
	vec rotate(db rad) const{
		return vec(x*cos(rad)-y*sin(rad), x*sin(rad)+y*cos(rad));
	}
	vec vert() const{ //��λ����
		db L=(*this).len();
		return vec(-y/L,x/L);
	}
	friend ostream& operator<<(ostream &o, Vec v){
		o<<v.x<<' '<<v.y;
		return o;
	}
};
typedef vec point;

db dis(Point a, Point b){
	return (a-b).len();
}
db angle(Vec a, Vec b){
	return acos((a^b)/a.len()/b.len());
}
db area2(Point a, Point b, Point c){
	return (b-a)*(c-a);
}
/*
Line: P=P0+t*vp
Segment: 0<=t<=1.
*/
//cross point of line P and Q
point lineCross(Point p, Vec vp, Point q, Vec vq){
	db t=(vq*(p-q))/(vp*vq);
	return p+vp*t;
}
db lineDis(Point p, Point a, Point b){
	vec v1=b-a,v2=p-a;
	return fabs(v1*v2/v1.len());
}
db segDis(Point p, Point a, Point b){
	if (a==b) return dis(a,p);
	vec v1=b-a,v2=p-a,v3=p-b;
	if ((v1^v2)<0) return v2.len();
	else if ((v1^v3)>0) return v3.len();
	else return fabs(v1*v2/v1.len());
}
point lineProj(Point p, Point a, Point b){
	vec v=b-a;
	return a+v*((v^(p-a))/(v^v));
}
//point is on line
bool onLine(Point p, Point a, Point b){
	return eq0((p-a)*(b-a));
}
//point on seg [a,b]
bool onSeg(Point p, Point a, Point b){
	return onLine(p,a,b) && dcmp((a-p)^(b-p))<=0;
}
//fast test before line cross, 0 indicate the line are not cross 
bool rectCross(Point a1, Point a2, Point b1, Point b2){return 
	min(a1.x,a2.x)<=max(b1.x,b2.x)+eps &&
	min(b1.x,b2.x)<=max(a1.x,a2.x)+eps &&
	min(a1.y,a2.y)<=max(b1.y,b2.y)+eps &&
	min(b1.y,b2.y)<=max(a1.y,a2.y)+eps;
}
int segCross(Point a1, Point a2, Point b1, Point b2){
	if (!rectCross(a1,a2,b1,b2)) return 0;
	db c1=dcmp((a2-a1)*(b1-a1)), c2=dcmp((a2-a1)*(b2-a1));
	db c3=dcmp((b2-b1)*(a1-b1)), c4=dcmp((b2-b1)*(a2-b1));
	if (c1*c2>0 || c3*c4>0) //no cross
		return 0; 
	if (c1==0 && c2==0||c3==0 && c4==0) //segment on same line
		return -1; 
	if (c1*c2<0 && c3*c4<0) return 1; //normal cross
	return 2; //a point on line
}
struct circle{
	point c;
	double r;
	circle(Point c, db r):c(c),r(r){}
	circle(Point p1, Point p2):c((p1+p2)/2),r(dis(p1,p2)/2){}
	circle(Point p1, Point p2, Point p3){
		c=(p1+lineCross(p2,(p2-p1).vert(),p3,(p3-p1).vert()))/2;
		r=(p1-c).len();
	}
	bool operator==(circle v) const{
		return c==v.c && r==v.r;
	}
	point angle(db theta){
		return c+point(theta)*r;
	}
};

bool inCir(point p, circle c){
	return dcmp(dis(c.c,p)-c.r)<=0;
}
//return -1,0,1,2, ans[2]
//!--
int cirCross(circle A, circle B, point *ans){
	db d=dis(A.c,B.c);
	if (eq0(d)){
		if (eq(A.r,B.r)) return -1;
		return 0;
	}
	if (dcmp(A.r+B.r-d)<0) return 0;
	db a=(B.c-A.c).angle();
	db da=acos((A.r*A.r+d*d-B.r*B.r)/(2*A.r*d));
	ans[0]=A.angle(a-da),ans[1]=A.angle(a+da);
	if (ans[0]==ans[1]) return 1;
	return 2;
}

//make tangent line from p
//return tan point
int cirTang(Point p, circle c, point *ans){
	db d=(c.c-p).len();
	if (dcmp(d-c.r)<0) return 0;
	if (eq(d,c.r)){
		ans[0] = p;
		return 1;
	}
	db base=(p-c.c).angle();
	db ang=acos(c.r/d);
	ans[0]=c.angle(base-ang);
	ans[1]=c.angle(base+ang);
	return 2;
}
//point a[4],b[4], tangent point on circle
//cnt maybe -1(same), 0(in), 1(intang), 2(cross), 3(outtang), 4(out) 
int cirTang(circle A, circle B, point *a, point *b){
	int cnt=0;
	if (A==B) return -1;
	if (A.r<B.r) swap(A,B),swap(a,b);
	db d=dis(A.c,B.c);
	db diff=A.r-B.r, sum=A.r+B.r;
	if (dcmp(d-diff)<0) return 0;
	db base=(B.c-A.c).angle();
	if (eq(d,diff)){
		a[0] = A.angle(base);
		b[0] = a[0];
		return 1;
	}
	db ang=acos((A.r-B.r)/d);
	a[cnt]=A.angle(base+ang); b[cnt]=B.angle(base+ang); cnt++;
	a[cnt]=A.angle(base-ang); b[cnt]=B.angle(base-ang); cnt++;
	if (eq(d,sum)){
		a[cnt] = A.angle(base);
		b[cnt] = a[cnt];
		cnt++;
	} else if (dcmp(d-sum)>0){
		ang=acos((A.r+B.r)/d);
		a[cnt]=A.angle(base+ang); b[cnt]=B.angle(PI+base+ang); cnt++;
		a[cnt]=A.angle(base-ang); b[cnt]=B.angle(PI+base-ang); cnt++;
	}
	return cnt;
}
//!-- test
//line AB cross circle c
int cirCross(Point a, Point b, circle c, point *ans){
	vec v=b-a, u=a-c.c;
	db e=!v, f=2*(v^u), g=!u-c.r*c.r;
	db delta=f*f-4*e*g;
	if (delta<0) return 0;
	if (eq0(delta)){
		ans[0]=a-v*(f/2/e);
		return 1;
	}
	db t1=(-f-sqrt(delta))/(2*e);
	db t2=(-f+sqrt(delta))/(2*e);
	ans[0]=a+v*t1;
	ans[1]=a+v*t2;
	return 2;
}

int seg_cirCross(Point a, Point b, circle c, point *ans){
	vec v=b-a, u=a-c.c;
	db e=!v, f=2*(v^u), g=!u-c.r*c.r;
	db delta=f*f-4*e*g;
	if (delta<0) return 0;
	if (eq0(delta)){
		ans[0]=a-v*(f/2/e);
		return 1;
	}
	db t1=(-f-sqrt(delta))/(2*e);
	db t2=(-f+sqrt(delta))/(2*e);
	point a1=a+v*t1, a2=a+v*t2;
	int cnt=0;
	if (dcmp(t1)>=0 && dcmp(t1-1)<=0) ans[cnt++]=a1;
	if (dcmp(t2)>=0 && dcmp(t2-1)<=0) ans[cnt++]=a2;
	return cnt;
}
//1 in, 0 out, -1 border
int inPoly(point p, point *poly, int n){
	int w=0;
	for (int i=0;i<n;i++){
		if (onSeg(p,poly[i],poly[(i+1)%n])) 
			return -1;
		int k=dcmp((poly[(i+1)%n]-poly[i])*(p-poly[i]));
		int d1=dcmp(poly[i].y-p.y);
		int d2=dcmp(poly[(i+1)%n].y-p.y);
		if (k>0 && d1<=0 && d2>0) w++;
		if (k<0 && d2<=0 && d1>0) w--;
	}
	return w!=0;
}
//seg in poly, 0 out/border, 1 in
//if point at border regard as in poly, 
//the condition is (any segCross(...)==1) && (online<2 || the line short an epsilon still in poly)   
bool inPoly(point p1, point p2, point *poly, int n){
	if (!inPoly(p1,poly,n) || !inPoly(p2,poly,n))
		return 0;
	for (int i=0;i<n;i++)
		if (segCross(p1,p2,poly[i],poly[(i+1)%n]))
			return 0;
	return 1;
}
//-- if the poly is not simple, the result will be strange
db polyArea(point *p, int n){
	db sum=0;
	for (int i=1;i<n-1;i++)
		sum+=area2(p[0],p[i+1],p[i]);
	return fabs(sum)/2;
}
//Andrew algo, faster than Graham Scan
int convex(point *p, int n, point *ans){
	sort(p,p+n);
	int m=0;
	for (int i=0;i<n;i++){
		while (m>1 && (ans[m-1]-ans[m-2])*(p[i]-ans[m-2])<=0) m--;
		ans[m++]=p[i];
	}
	int k=m;
	for (int i=n-2;i>=0;i--){
		while (m>k && (ans[m-1]-ans[m-2])*(p[i]-ans[m-2])<=0) m--;
		ans[m++]=p[i];
	}
	if (n>1) m--;
	return m;
}

struct Line{
	point p; vec v;
	db ang;
	Line(){}
	Line(Point p, Vec v):p(p),v(v){}
	bool operator<(const Line &L) const{
		return ang<L.ang;
	}
};

bool onleft(Line &l, point p){
	return dcmp(l.v*(p-l.p))>0;
}
const int maxp=1001;
Line Q[maxp<<1]; //deque
point T[maxp<<1]; //temp ans
//The result area can't be unlimited.
//You can add 'inf' edges to make sure that. Then
//if a result point is 'inf' then the real result is unlimited.
int halfplaneInt(Line *l, int n, point *ans){
	for (int i=0;i<n;i++) l[i].ang=l[i].v.angle();
	sort(l,l+n);
	int head=0,tail=0;
	Q[0]=l[0];
	for (int i=1;i<n;i++){
		while (head<tail && !onleft(l[i],T[tail-1])) tail--;
		while (head<tail && !onleft(l[i],T[head])) head++;
		Q[++tail]=l[i];
		if (eq0(Q[tail].v*Q[tail-1].v)){
			--tail;
			if (onleft(Q[tail],l[i].p)) Q[tail]=l[i];
		}
		if (head<tail) 
			T[tail-1]=lineCross(Q[tail-1].p,Q[tail-1].v,Q[tail].p,Q[tail].v);		
	}
	while (head<tail && !onleft(Q[head],T[tail])) tail--; 
	if (head>=tail-1) return 0;  //m<3, no available area
	T[tail]=lineCross(Q[head].p,Q[head].v,Q[tail].p,Q[tail].v); //head cross tail
	int m=0;
	for (int i=head;i<=tail;i++) ans[m++]=T[i];
	return m;
}

//---complex---

//sector a->b, the cicle center is (0,0).
db secArea(point a, point b, db r){
	db ang=a.angle()-b.angle();
	while (dcmp(ang)<=0) ang+=2*PI;
	while (dcmp(ang-2*PI)>0) ang-=2*PI;
	ang=min(ang, 2*PI-ang);
	return r*r*ang/2;
}
db triArea(point p1, point p2){
	return fabs(p1*p2)/2;
}
db tri_cirArea(point p1, point p2, circle c){
	db r=c.r;
	p1=p1-c.c; p2=p2-c.c;
	c.c.x=c.c.y=0;
	point p[2];
	if (dcmp(p1.len()-r)<0){
		if (dcmp(p2.len()-r)<0) return triArea(p1,p2);
		seg_cirCross(p1,p2,c,p);
		return triArea(p1,p[0]) + secArea(p[0],p2,r);
	}
	if (dcmp(p2.len()-r)<0){
		seg_cirCross(p1,p2,c,p);
		return secArea(p1,p[0],r) + triArea(p[0],p2);
	}
	int pc=seg_cirCross(p1,p2,c,p);
	if (pc==2) 
		return secArea(p1,p[0],r)+triArea(p[0],p[1])+secArea(p[1],p2,r);
	return secArea(p1,p2,r);	
}
db poly_cirArea(point *p, int n, circle c){
	db ans=0;
	for (int i=0;i<n;i++){
		db d=dcmp((p[i]-c.c)*(p[(i+1)%n]-c.c));
		ans+=d*tri_cirArea(p[i],p[(i+1)%n],c);
	}
	return fabs(ans);
}

//average O(n)
circle mincirCover(point *p, int n){
    random_shuffle(p,p+n);
    circle c(p[0],0);
    for (int i=1;i<n;i++)
        if (dcmp(dis(c.c,p[i])-c.r)>0)
        {
            c=circle(p[i],0);
            for (int j=0;j<i;j++)
                if (dcmp(dis(c.c,p[j])-c.r)>0)
                {
                    c=circle(p[i],p[j]);
                    for (int k=0;k<j;k++)
                        if (dcmp(dis(c.c,p[k])-c.r)>0)
                            c=circle(p[i],p[j],p[k]);
                }
        }
    return c;
}

double polyDiam(point *p0, int n0){
	static point p[maxn];
	int n=convex(p0,n0,p);
	p[n]=p[0];
	int opp=1; db ans=dis(p[0],p[1]);
	for (int i=0;i<n;i++){
		while (area2(p[i],p[i+1],p[opp+1])>area2(p[i],p[i+1],p[opp])) opp=(opp+1)%n;
		ans=max(ans, max(dis(p[opp],p[i]),dis(p[opp],p[i+1])));
	}
	return ans;
}
//+?
db polyWidth(point *p0, int n0){
	static point p[maxn];
	int n=convex(p0,n0,p);
	p[n]=p[0];
	int opp=1; db ans=1e10;
	for (int i=0;i<n;i++){
		while (area2(p[i],p[i+1],p[opp+1])>area2(p[i],p[i+1],p[opp])) opp=(opp+1)%n;
		ans=min(ans, lineDis(p[opp],p[i],p[i+1]));
	}
	return ans;
}

void test(){
	vec a(1.2,2.5);
	vec b(1.4,1.3);
	vec c(1,2),vc(0,1);
	vec d(3,1),vd(-3,1.5);
	vec ep(eps/2,-eps/2);
	cout<<a+b<<" expect 2.6 3.8\n";
	cout<<a-b<<" expect -0.2 1.2\n";
	cout<<a*2<<" expect 2.4 5\n";
	cout<<b/2<<" expect 0.7 0.65\n";
	cout<<(a^b)<<" expect 4.93\n";
	cout<<a*b<<" expect -1.94\n";
	cout<<b*a<<" expect 1.94\n";
	cout<<(a==b)<<" expect 0\n";
	cout<<(a==a+ep)<<" expect 1\n";
	cout<<a.len()<<" expect 2.77308\n";
	cout<<!a<<" expect 7.69\n";
	cout<<(c.angle())<<" expect 1.10715\n";
	cout<<(c.rotate(PI/2))<<" expect -2 1\n";
	cout<<(c.rotate(-PI/2))<<" expect 2 -1\n";
	cout<<c.vert()<<" expect -0.8944 0.4472\n";
	cout<<angle(c,d)<<" expect "<<c.angle()-d.angle()<<'\n';
	cout<<lineCross(c,vc,d,vd)<<" expect 1 2\n";
	cout<<lineCross(d,vd,c,vc)<<" expect 1 2\n";
	cout<<lineDis(point(0,0),d,vec(0,2.5))<<" expect 2.23607\n";
	cout<<segDis(point(0,0),d,vec(0,2.5))<<" expect 2.23607\n";
	cout<<segDis(point(0,5),d,vec(0,2.5))<<" expect 2.5\n";
	cout<<lineProj(point(0,0),d,vec(4,0))<<" expect 2 2\n";
	
	cout<<onLine(point(2,2),d,vec(4,0))<<" expect 1\n";
	cout<<onSeg(point(2,2),d,vec(4,0))<<" expect 0\n";
	cout<<onSeg(point(3.5,0.5),d,vec(4,0))<<" expect 1\n";
	cout<<onSeg(point(4,0),d,vec(4,0))<<" expect 1\n";
	
	cout<<segCross(point(2,2),point(0,0),d,vec(0,4))<<" expect 2\n";
	cout<<segCross(point(3,3),point(0,0),d,vec(0,4))<<" expect 1\n";
	cout<<segCross(point(0,4),point(0,0),d,vec(0,4))<<" expect 2\n";
	cout<<segCross(point(1,1),point(0,0),d,vec(0,4))<<" expect 0\n";
	cout<<segCross(point(2,2),point(-1,5),d,vec(0,4))<<" expect -1\n";
	cout<<segCross(point(0,4),point(-1,5),d,vec(0,4))<<" expect 2\n";
	
	point ans[2];
	circle c1(point(0,1),1),c2(point(0,0),1);
	cout<<cirCross(c1,c2,ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect -0.866 0.5 0.866 0.5\n";
	
	c1=circle(point(0,1),1),c2=c1;
	cout<<cirCross(c1,c2,ans)<<" expect -1\n";
	
	c1=circle(point(0,1),1),c2=circle(point(4,4),1);
	cout<<cirCross(c1,c2,ans)<<" expect 0\n";
	
	c1=circle(point(0,1),1),c2=circle(point(0,0),2);
	cout<<cirCross(c1,c2,ans)<<" expect 1\n";
	cout<<ans[0]<<" expect 0 2\n";
	
	cout<<cirTang(vec(0,0),c1,ans)<<" expect 1\n";
	cout<<ans[0]<<" expect 0 0\n";
	
	cout<<cirTang(vec(1,0),c1,ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect 1 1 0 0 or 0 0 1 1\n";
	
	c1=circle(point(0,0),2);
	cout<<cirTang(vec(-4,0),c1,ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect -1 1.73205 -1 -1.73205\n";
	
	cout<<cirCross(vec(-4,4),vec(4,-4),c1, ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect -1.414 1.414 1.414 -1.414\n";
	
	//cout<<seg_cirCross(vec(0,0),vec(4,0),c1)<<" expect 2 0\n";
	//cout<<seg_cirCross(vec(4,0),vec(0,0),c1)<<" expect 2 0\n";
	
	c2=circle(point(0,-1),1);
	point xa[4],xb[4];
	cout<<cirTang(c1,c2,xa,xb)<<" expect 1\n";
	cout<<xa[0]<<' '<<xb[0]<<" expect 0 -2 0 -2\n";
	
	c2=circle(point(2,2),2);
	cout<<cirTang(c1,c2,xa,xb)<<" expect 2\n";
	cout<<xa[0]<<' '<<xb[0]<<' '<<xa[1]<<' '<<xb[1]<<" expect -1.414 1.414 0.586 3.414 1.414 -1.414 3.414 0.586\n";
	
	c2=circle(point(4,0),2);
	cout<<cirTang(c1,c2,xa,xb)<<" expect 3\n";
	cout<<xa[0]<<' '<<xb[0]<<' '<<xa[1]<<' '<<xb[1]<<' '<<xa[2]<<' '<<xb[2]<<
		" expect 0 2 4 2 0 -2 4 -2 2 0\n";
	
	c1=circle(point(-2,0),sqrt(2));c2=circle(point(2,0),sqrt(2));
	cout<<cirTang(c1,c2,xa,xb)<<" expect 4\n";
	cout<<xa[2]<<' '<<xb[2]<<' '<<xa[3]<<' '<<xb[3]<<" expect -1 1 1 -1 -1 -1 1 1\n";
	
	a=vec(PI*0.75);
	cout<<a<<" expect -0.707 0.707\n";
	
	c1=circle(point(0,0),point(1,2));
	cout<<c1.c<<' '<<c1.r<<" expect 0.5 1 1.118\n";

	c1=circle(point(0,2),point(0,0),point(1,1));
	cout<<c1.c<<' '<<c1.r<<" expect 0 1 1\n";
	c1=circle(point(0,2),point(1,sqrt(3)),point(-sqrt(3),-1));
	cout<<c1.c<<' '<<c1.r<<" expect 0 0 2\n";
	
	point poly[4]={{-1,0},{2,1},{1,0},{2,-1}};
	cout<<inPoly({0,0},poly,4)<<' '<<inPoly({-2,0},poly,4)<<' '<<inPoly({1,0},poly,4)<<" expect 1 0 -1\n";
	cout<<inPoly({0,-0.5},poly,4)<<' '<<inPoly({1,0.2},poly,4)<<' '<<inPoly({1.5,0.2},poly,4)<<" expect 0 1 0\n";
	cout<<inPoly({1.5,0.5},poly,4)<<' '<<polyArea(poly,4)<<" expect -1 2\n";
	
	point aa[4];
	point polyt[4]={{-1,0},{2,1},{1,0},{2,-1}};
	cout<<convex(polyt,4,aa)<<" expect 3\n";
	
	cout<<mincirCover(polyt,4).c<<" expect "<<circle(poly[0],poly[1],poly[3]).c<<'\n';
	cout<<mincirCover(polyt,4).r<<" expect "<<circle(poly[0],poly[1],poly[3]).r<<'\n';
	
	cout<<poly_cirArea(poly, 4, {{0,0},1})<<" expect ???\n";
}

//cdq func for minDisPoint
point tp[200010],use[200010];
db cdq(point *p,int l, int r){
	if (l==r-1) return 1e12;
	if (l==r-2) {
		if (p[l].y>p[l+1].y) swap(p[l],p[l+1]);
		return dis(p[l],p[l+1]);
	}
	int mid=l+r+1>>1;
	int uc=0; Point pmid=p[mid];
	db d=min(cdq(p,l,mid),cdq(p,mid,r));
	for (int cl=l,cr=mid,cc=l;cc<r;cc++){
		if (cr>=r || cl<mid && p[cl].y<=p[cr].y)
			tp[cc]=p[cl++];
		else
			tp[cc]=p[cr++];
		if (fabs(tp[cc].x-pmid.x)<=d+eps)
			use[uc++]=tp[cc];
	}
	inc(i,uc)
		rep(j,i+1,uc){
			if (use[j].y>use[i].y+d+eps) break;
			d=min(dis(use[i],use[j]),d);
		}
	rep(i,l,r) p[i]=tp[i];
	return d;
}
db minDisPoint(point *p, int n){
	sort(p,p+n);
	return cdq(p,0,n);
}

namespace scannerLine{
const int maxn=100010;
struct Line{
	double l,r,h; int c;
	bool operator<(const Line &v) const{
		return h<v.h;
	}
}li[maxn];
int lic;

#define lc u+u+1
#define rc u+u+2
double len[maxn<<2]; int cnt[maxn<<2];
double x[maxn<<1]; int xc;

void calc(int u, int l, int r){
	if (cnt[u])
		len[u]=x[r]-x[l];
	else if (l==r-1)
		len[u]=0;
	else
		len[u]=len[lc]+len[rc];
}
void add(int u, int l, int r, int cl, int cr, int c){
	if (cl<=l && cr>=r){
		cnt[u]+=c;
		calc(u,l,r);
		return;
	}
	int mid=l+r>>1;
	if (cl<mid) add(lc,l,mid,cl,cr,c);
	if (cr>mid) add(rc,mid,r,cl,cr,c);
	calc(u,l,r);
}

double x0[maxn],y0[maxn],x1[maxn],y1[maxn];
void rectInt(int n){
	xc=lic=0;
	memset(len,0,sizeof(len));
	memset(cnt,0,sizeof(cnt));
	for (int i=0;i<n;i++){
		double x1,y1,x2,y2;
		scanf("%lf%lf%lf%lf",&x1,&y1,&x2,&y2);
		x[xc++]=x1; x[xc++]=x2;
		li[lic++]=(Line){x1,x2,y1,1};
		li[lic++]=(Line){x1,x2,y2,-1};
	}
	sort(li,li+lic);
	sort(x,x+xc);
	double ans=0,last=0;
	for (int i=0;i<lic;i++){
		int l=lower_bound(x,x+xc,li[i].l)-x;
		int r=lower_bound(x,x+xc,li[i].r)-x;
		add(0,0,xc,l,r,li[i].c);
		ans+=len[0]*(li[i+1].h-li[i].h);
		//sum of lenth on sx
		//ans+=fabs(len[0]-last); last=len[0];
	}
	printf("%.2f\n",ans);
}
#undef lc
#undef rc
}
}

namespace DLX{
const int maxl=10000;
//row,col: the original pos   H:row head  S:col size
int L[maxl],R[maxl],U[maxl],D[maxl],H[maxl],S[maxl],col[maxl],row[maxl],ans[maxl];
int siz,m;
void pre(){
	for (int i=0;i<=m;i++){
		L[i]=i-1; R[i]=i+1;
		col[i]=i;
		U[i]=D[i]=i;
		row[i]=-1;
	}
	R[m]=0; L[0]=m;
	siz=m+1;
	memset(H,0,sizeof(H));
	memset(S,0,sizeof(S));
	S[0]=maxl+1;
}
//!-- insert by row order first, col order second
//!-- the start coord is (1,1), not (0,0)
void insert(int r, int c){
	U[siz]=U[c];
	D[siz]=c;
	U[D[siz]]=D[U[siz]]=siz;
	if (H[r]){
		L[siz]=L[H[r]];
		R[siz]=H[r];
		L[R[siz]]=R[L[siz]]=siz;
	}
	else H[r]=L[siz]=R[siz]=siz;
	row[siz]=r; col[siz]=c;
	S[c]++;
	siz++;
}
//remove a col affected rows
void del(int c){
	L[R[c]]=L[c];
	R[L[c]]=R[c];
	for (int i=D[c];i!=c;i=D[i])
		for (int j=R[i];j!=i;j=R[j]){
			U[D[j]]=U[j];
			D[U[j]]=D[j];
			S[col[j]]--;
		}
}
void back(int c){
	for (int i=D[c];i!=c;i=D[i])
		for (int j=R[i];j!=i;j=R[j]){
			U[D[j]]=D[U[j]]=j;
			S[col[j]]++;
		}
	R[L[c]]=L[R[c]]=c;
}
//ans[k]: selected row;  H[ans[k]]: selected line head
bool dfs(int k){
	if (R[0]==0) 
		return 1;
	int mins=1e8, c=0;
	for (int t=R[0];t;t=R[t])
		if (S[t]<mins)
			mins=S[t],c=t;
	if (!c) return 0;
	del(c);
	for (int i=D[c];i!=c;i=D[i]){
		ans[k]=row[i];
		for (int j=R[i];j!=i;j=R[j]) del(col[j]);
		if (dfs(k+1)) return 1;
		for (int j=L[i];j!=i;j=L[j]) back(col[j]);
	}
	back(c);
	return 0;
}
//9x9 sudoku solver
//first 81: a pos is filled; next 81: a row filled 1~9; next 81: col filled; last 81:square filled
int out[9][9];
void solve(int a[9][9]){
	m=324;
	pre();
	int n=1;
	for (int i=0;i<9;i++)
		for (int j=0;j<9;j++)
			if (a[i][j]){
				insert(n,i*9+j+1); 
				insert(n,81+i*9+a[i][j]); 
				insert(n,162+j*9+a[i][j]); 
				insert(n,243+(i/3*3+j/3)*9+a[i][j]); 
				n++;
			}
			else{
				for (int k=1;k<=9;k++){
					insert(n,i*9+j+1); 
					insert(n,81+i*9+k); 
					insert(n,162+j*9+k); 
					insert(n,243+(i/3*3+j/3)*9+k); 
					n++;
				}
			}
	dfs(0);
	for (int i=0;i<81;i++){
		int p=col[H[ans[i]]]-1, x=(col[R[H[ans[i]]]]-1)%9+1;
		out[p/9][p%9]=x;
	}
	for (int i=0;i<9;i++,cout<<'\n')
		for (int j=0;j<9;j++)
			cout<<out[i][j]<<' ';
}

int n0,sum;
void dfs_nqueen(int k){
	if (R[0]>n0){ //slashs don't require filled 
		sum++;
		return;
	}
	int mins=1e8, c=0;
	for (int t=R[0];t<=n0*2;t=R[t])
		if (S[t]<mins)
			mins=S[t],c=t;
	if (!c) return;
	del(c);
	for (int i=D[c];i!=c;i=D[i]){
		for (int j=R[i];j!=i;j=R[j]) del(col[j]);
		dfs_nqueen(k+1);
		for (int j=L[i];j!=i;j=L[j]) back(col[j]);
	}
	back(c);
}
//only for demo, this algo is not faster than brute force
//bit aglo is fastest 
void nqueens(int n){
	int l=1; n0=n; m=n*6-2; sum=0;
	pre();
	for (int i=0;i<n;i++)
		for (int j=0;j<n;j++){
			insert(l,i+1);
			insert(l,n+j+1);
			insert(l,n*2+i+j+1);
			insert(l,n*5+i-j-1);
			l++;
		}
	dfs_nqueen(0);
	cout<<sum<<'\n';
}
}

//O(nlogn)
namespace HFMT{
const int maxn=30;

//finally tn is the root of tree
int a[maxn],ch[maxn<<1][2],n,tn; //idx from 1..n
int sum[maxn<<1]; //not very necessary
//input  a[1..n]:frequency of each character, n: |character|
//result ch[maxn<<1][2], the path to leaf node is the encoding of input char
void build(){
	priority_queue<PII> qu;
	for (int i=1;i<=n;i++) qu.emplace(-a[i],i),sum[i]=a[i];
	tn=n;
	while (qu.size()>1){
		int x1=qu.top().first, p1=qu.top().second;
		qu.pop();
		int x2=qu.top().first, p2=qu.top().second;
		qu.pop();
		ch[++tn][0]=p1; ch[tn][1]=p2;
		sum[tn]=-x1-x2;
		qu.emplace(x1+x2, tn);
	}
}
int len[maxn];
//dfs: debug, and label lenth of encode after
void dfs(int u=tn, int deep=0){
	if (!u) return;
	if (u<=n) len[u]=deep;
	dfs(ch[u][1],deep+1);
	//for (int i=0;i<deep;i++) printf("  "); printf("%d\n",sum[u]);
	dfs(ch[u][0],deep+1);
}
};

namespace KDT{
const int N=1000010, inf=0x3f3f3f3f;
int n,m,K,rt,ans;

//s[]:tree node  p[2]:2-d coord of leaf node  x[2]:min(LB) coord of a subspace  y[2]:max(RT) coord
struct Node{
	int p[2],x[2],y[2];
	bool operator<(const Node &v)const{
		return p[K]<v.p[K];
	}
}a[N],s[N],q;
int ch[N][2];
#define lc ch[u][0]
#define rc ch[u][1]
void upd(int u){
	inc(i,2){
		if (lc) s[u].x[i]=min(s[u].x[i],s[lc].x[i]),
				s[u].y[i]=max(s[u].y[i],s[lc].y[i]);
		if (rc) s[u].x[i]=min(s[u].x[i],s[rc].x[i]),
				s[u].y[i]=max(s[u].y[i],s[rc].y[i]);
	}
}
void add(int u, Node &t){
	inc(i,2) s[u].x[i]=s[u].y[i]=s[u].p[i]=t.p[i];
}
int disL1Min(int u, Node &t){ //min L1 dis to a Rect of in_tree node
	int ret=0;
	inc(i,2) 
		if (t.p[i]>s[u].y[i]) ret+=t.p[i]-s[u].y[i];
		else if (t.p[i]<s[u].x[i]) ret+=s[u].x[i]-t.p[i];
	return ret;
}
int disL1Max(int u, Node &t){
	int ret=0;
	inc(i,2) ret+=max(abs(t.p[i]-s[u].x[i]),abs(t.p[i]-s[u].y[i]));
	return ret;
}
int sqr(int a){
	return a*a;
}
int disL2Min(int u, Node &t){
	int ret=0;
	inc(i,2) 
		if (t.p[i]>s[u].y[i]) ret+=sqr(t.p[i]-s[u].y[i]);
		else if (t.p[i]<s[u].x[i]) ret+=sqr(t.p[i]-s[u].x[i]);
	return ret;
}
int disL2Max(int u, Node &t){ //max coord dis
	int ret=0;
	inc(i,2) ret+=max(sqr(t.p[i]-s[u].x[i]),sqr(t.p[i]-s[u].y[i]));
	return ret;
}
void build(int &u, int l, int r, int cur){ //O(nlogn)
	u=l+r>>1; K=cur;
	nth_element(a+l,a+u,a+r+1);
	add(u,a[u]);
	if (l<u) build(lc,l,u-1,cur^1);
	if (r>u) build(rc,u+1,r,cur^1);
	upd(u);
}
//Maybe we need to rebuild the tree after unbalanced insert
void ins(int u, int cur){  
	if (q.p[cur]<s[u].p[cur])
		if (lc) ins(lc,cur^1);
		else lc=++n,add(n,q);
	else
		if (rc) ins(rc,cur^1);
		else rc=++n,add(n,q);
	upd(u);
}
void ask(int u){
	ans=min(ans,abs(s[u].p[0]-q.p[0])+abs(s[u].p[1]-q.p[1])); //L1 dis
	int dl=lc?disL1Min(lc,q):inf, dr=rc?disL1Min(rc,q):inf;
	//int dl=lc?disL1Max(lc,q):0, dr=rc?disL1Max(rc,q):0;
	if (dl<dr){ //trim branch, swap > < when search max dis point
		if (dl<ans) ask(lc);
		if (dr<ans) ask(rc);
	}
	else{
		if (dr<ans) ask(rc);
		if (dl<ans) ask(lc);
	}
}
//minDisPoint (L1 dis) with ins operate
//each query asks one nearest point of a giving coord
int main(){
	scanf("%d%d",&n,&m);
	for (int i=1;i<=n;i++) scanf("%d%d",&a[i].p[0],&a[i].p[1]);
	build(rt,1,n,0);
	while (m--){
		int k; scanf("%d%d%d",&k,&q.p[0],&q.p[1]);
		if (k==1) ins(rt,0);
		else{
			ans=inf; ask(rt);
			printf("%d\n",ans);
		}
	}
	return 0;
}
#undef lc
#undef rc
}

namespace SquareTransform{
const int N=100;
typedef int Arr[N][N];int n;
void cp(Arr to,Arr from){inc(i,n)inc(j,n) to[i][j]=from[i][j];}
Arr _t;
//clockwise 90 deg
void rot(Arr a){
	inc(i,n)inc(j,n) _t[j][n-i-1]=a[i][j];
	cp(a,_t);
}
//LR flip
void flip(Arr a){
	inc(i,n)inc(j,n) _t[i][n-j-1]=a[i][j];
	cp(a,_t);
}
bool same(Arr a, Arr b){
	inc(i,n) inc(j,n) if (a[i][j]!=b[i][j]) return 0;
	return 1;
}
}

namespace DividePoint{
const int maxn=20010,maxm=40010;

struct Edge{
	int to,nxt,c;
}e[maxm];
int ec,n,head[maxn];

void added(int a, int b, int c){
	e[++ec]={b,head[a],c};
	head[a]=ec;
	e[++ec]={a,head[b],c};
	head[b]=ec;
}

int query[maxn],q,siz[maxn],ms[maxn];
int MS,root,tn;
bool vis[maxn];

void dfs(int u,int fa, int len){
	;//counter
	for (int i=head[u],v=e[i].to;i;i=e[i].nxt,v=e[i].to)
		if (v!=fa && !vis[v])
			dfs(v,u,len+e[i].c);
}
int calc(int u, int x0){
	dfs(u,u,x0);
	return 0; //return count
}
void getrt(int u, int fa){
	siz[u]=1; ms[u]=0;
	for (int i=head[u],v=e[i].to;i;i=e[i].nxt,v=e[i].to)
		if (v!=fa && !vis[v])
			getrt(v,u),
			siz[u]+=siz[v],ms[u]=max(ms[u],siz[v]);
	ms[u]=max(ms[u],tn-siz[u]);
	if (ms[u]<MS) root=u,MS=ms[u];
}
int ans=0;
void divide(int u){
	vis[u]=1;
	ans+=calc(u,0);
	for (int i=head[u],v=e[i].to;i;i=e[i].nxt,v=e[i].to)
		if (!vis[v]){
			ans-=calc(v,e[i].c); //sub invalid path
			tn=siz[u]; root=0;
			MS=0x3f3f3f3f; getrt(v,u);
			divide(root);
		}
}
int main(){
	scanf("%d",&n);
	for (int i=0;i<n-1;i++){
		int a,b,c; scanf("%d%d%d",&a,&b,&c);
		added(a,b,c);
	}
	tn=n; root=0; MS=0x3f3f3f3f; getrt(1,1); //first point divide
	divide(root);
	cout<<ans<<'\n';
	return 0;
}
}

int main(){
	return 0;
}
