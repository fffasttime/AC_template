#include "base.cpp"

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

//----exlucas----
//return C(n,m) mod any number
//time: O(max(p^k)*polylog)
ll calc(ll n, ll x, ll P){ //solve n! mod p^k
	if (!n) return 1;       //x:p ,P:p^k
	ll s=1;
	for (int i=1;i<=P;i++) //main cycle part
		if (i%x) s=s*i%P;
	s=qpow(s,n/P,P);
	for (ll i=1;i<=n%P;i++) //remain part
		if (i%x) s=s*i%P;
	return s*calc(n/x,x,P)%P; //mod p==0 part
}
ll multilucas(ll n, ll m, ll x, ll P) { //solve C(n,m) mod p^k
	ll cnt=0,s1=calc(n,x,P),s2=calc(m,x,P),s3=calc(n-m,x,P);
	for (ll i=n;i;i/=x) cnt+=i/x;
	for (ll i=m;i;i/=x) cnt-=i/x;
	for (ll i=n-m;i;i/=x) cnt-=i/x;
	return qpow(x,cnt,P)%P*s1%P*inv_euclid(s2,P)%P*inv_euclid(s3,P)%P;
}
ll exlucas(ll n, ll m, ll P){
	int cnt=0;
	ll p[20],a[20]; //no more 20 diff prime facter in int64
	for (ll i=2;i*i<=P;i++) //O(sqrt P), use pol_rho when p is large
		if (P%i==0){
			p[cnt]=1;
			while (P%i==0) p[cnt]=p[cnt]*i,P/=i;
			a[cnt]=multilucas(n,m,i,p[cnt]); //solve mod p^k
			cnt++;
		}
	if (P>1) a[cnt]=multilucas(n,m,P,P),p[cnt]=P,++cnt;
	return CRT(cnt,a,p);
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

namespace Berlekamp_Massey{
const int maxn=2010;

//Berlekamp-Massey alg, O(n^2)
//a[i]=a[i-1]*p[1]+a[i-2]*p[2]+...
//x[]: input,  ps[pn][]: result
db x[maxn],delta[maxn];
vector<db> ps[maxn]; //if memory is limited, use rolling array
int n, cnt, fail[maxn], pn;
void BM(){
	int best=0;
	for(int i=1;i<=n;i++){
		db dt=-x[i];
		for (int j=0;j<ps[pn].size();j++)
			dt+=x[i-j-1]*ps[pn][j];
		delta[i]=dt;
		if (fabs(dt)<=1e-7) continue;
		fail[pn]=i; if (!pn) {ps[++pn].resize(i);continue;}
		vector<db> &ls=ps[best]; db k=-dt/delta[fail[best]]; //get coeff
		vector<db> cur; cur.resize(i-fail[best]-1); //tail 0
		cur.push_back(-k); 
		for(int j=0;j<ls.size();j++) cur.push_back(ls[j]*k); //get k*[last fail]
		if (cur.size()<ps[pn].size()) cur.resize(ps[pn].size());
		for(int j=0;j<ps[pn].size();j++) cur[j]+=ps[pn][j];  //add ps[pn]
        if(i-fail[best]+(int)ps[best].size()>=ps[pn].size()) best=pn;
        ps[++pn]=cur;
	}
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

