#include "base.cpp"

namespace NumTheory{

const int maxn=1000010;
int p[maxn],phi[maxn],mu[maxn],pc;
bool isp[maxn];
void genprime(){ //gen prime in range [2,maxn)
	memset(isp,1,sizeof(isp));
	isp[1]=0;
	for (int i=2;i<maxn;i++){
		if (isp[i]) p[pc++]=i;
		for (int j=0;j<pc && i*p[j]<maxn;j++){
			isp[i*p[j]]=0;
			if (i%p[j]==0) break;
		}
	}
}
int d[maxn], c0[maxn]; //d:count of frac,  c0: temp array, i=p1^c0[i] * p2^(...) * ...
void gennumfunc(){
	memset(isp,1,sizeof(isp));
	isp[1]=0;  phi[1]=mu[1]=d[1]=1;
	for (int i=2;i<maxn;i++){
		if (isp[i]) p[pc++]=i,phi[i]=i-1,mu[i]=-1,d[i]=2,c0[i]=1;
		for (int j=0;j<pc && i*p[j]<maxn;j++){
			isp[i*p[j]]=0;
			if (i%p[j]==0){
				phi[i*p[j]]=phi[i]*p[j];
				mu[i*p[j]]=0;
				c0[i*p[j]]=c0[i]+1;
				d[i*p[j]]=d[i]/(c0[i]+1)*(c0[i]+2);
				break;
			}
			phi[i*p[j]]=phi[i]*(p[j]-1); //f(ab)=f(a)f(b), when (a,b)=1
			mu[i*p[j]]=-mu[i];
			c0[i*p[j]]=c0[p[j]];
			d[i*p[j]]=d[i]*2;
		}
	}
}

//sum_i([n/i]) , O(sqrt(n)) 
ll sum_floor(ll n){
	ll ans=0;
	for(int l=1,r;l<=n;l=r){
	    r=n/(n/l)+1; //in section [l,r), floor(n/i) has same value
	    ans+=(r-l)*(n/l); //*(sphi[r]-sphi[l]); //sum([n/i]*phi[i])
	}
	return ans;
}
//another algo of sum_floor: sum(k=1, sqrtint(n), n\k)*2-sqrtint(n)^2

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
//not require p is prime, but (v,p) should be 1
ll inv_euclid(ll v, ll p){
	ll x,y; exgcd(v,p,x,y); //exgcd(v,p,x,y)==1 required
	return (x+p)%p;
}
//CRT, require (p1,p2,...)=1
//x=a1(mod p1)
//x=a2(mod p2)
//...
//result=sum(bi*Mi*Mi'), MiMi'=1(mod pi)
ll CRT(int n, ll a[], ll p[]){
	ll M=1,x=0;
	for (int i=0;i<n;i++) M*=p[i]; //[!] notice if M>int32, a*b%M may overflow
	for (int i=0;i<n;i++){
		ll w=M/p[i]; //x=pi*k1+a + w*k2
		x=(x+w*inv_euclid(w,p[i])%M*a[i])%M; //get k1, pi*k1=a (Mod w)
		//use inv_euclid() instead qpow() when p[] is not prime 
	}
	return (x+M)%M;
}

//CRT2 equ version
//x=a1(mod m1), x=a2(mod m2)
//result: x(mod p1p2)
int CRT2(int a1, int m1, int a2, int m2){
	int m=m1*m2;    //[!] notice if M>int32
	return (a1*m2%m*inv_euclid(m2,m1)+a2*m1%m*inv_euclid(m1,m2))%m;
}

//EXTCRT
//x=a1(mod p1)
//x=a2(mod p2)
//...
ll EXCRT(int n, ll a[], ll p[]){
	ll n1=p[0],a1=a[0],n2,a2,k1,k2,K,gcd,c,t;
	for (int i=1;i<n;i++){ //merge equs by order
		n2=p[i],a2=a[i]; 
		c=(a2-a1%n2+n2)%n2;
		gcd=exgcd(n1,n2,k1,k2); //n1*k1+n2*k2=gcd(n1,n2)
		if (c%gcd) return -1;
		t=n2/gcd; //n1*K+n2*(c/gcd*k2)=c
		K=c/gcd*k1%t; //K=qmul(c/gcd,k1,t); //if t too large
		a1+=n1*K; n1*=t;
		a1=(a1+n1)%n1;
	}
	return a1; //all answers are a1+LCM(p1,p2,..)
}

//get prime fact, x=mul(pi[i]^pa[i])
int pi[30],pa[30]; //no more 20 prime factor in range 2^64
int getfactor(int x){ //O(sqrt(n)), when x is a prime
	int c=0,m=sqrt(x)+1;
	for (int d=2;x>1 && d<=m;d++) 
	//for (int d=2,pc=0;x>1 && d<m;pc++,d=p[pc]) //faster, O(sqrt(n)/log(n))
		if (x%d==0){
			while (x%d==0) pa[c]++,x/=d;
			pi[c]=d; c++;
		}
	if (x>1) pi[c]=x, pa[c]=1, c++; //x is prime
	return c;
}
//single number phi, O(sqrt(n))
int getphi(int n){
	int ans=n;
	for (int i=2;i*i<=n;i++)
		if (n%i==0){
			ans=ans/i*(i-1);
			while (n%i==0) n/=i;
		}
	if (n>1) ans=ans/n*(n-1);
	return ans;
}

//be sure p=p^k,2p^k
//primitive_root(2)=1, primitive_root(4)=3, special judge
int primitive_root(int p){
	int phi=p-1; //int phi=getphi(p); //when p is not prime
	int pc=getfactor(phi);
	for (int g=2,j;;g++){ //g ~ p^0.25 in average
		for (j=0;j<pc;j++)
			if (qpow(g,phi/pi[j],p)==1)
				break;
		if (j==pc) return g;
	}
	//other solution of g: {g0^k | 0<k<phi, gcd(k, phi)=1}
}
//discrete logarithm
//solve a^x=b(mod p), require gcd(a,p)=1
//if a is primitive root and gcd(b,p)=1, the answer always exists
ll BSGS(ll a, ll b, ll p){
	int m,v,e=1;
	m=(int)sqrt(p+0.5);
	v=inv(qpow(a,m,p),p); //[!] use inv_euclid
	map<int,int> x; //unordered_map -> O(sqrt(N))
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
//find minimum x of a^x=b(mod m)
ll EXBSGS(ll a, ll b, ll m){
	if (b==1 || m==1) return 0;
	ll d,ca=1,k=0;
	while ((d=__gcd(a,m))>1){
		if (b%d) return -1;
		m/=d,b/=d; ca=ca*(a/d)%m; k++;
		if (ca==b) return k; //spj x<k
	}
	ll ret=BSGS(a,b*inv(ca,m)%m,m);
	if (ret==-1) return -1;
	return ret+k;
}

//judge if x^2=n (mod p) has solution
//qpow(n,(p-1)/2,p)=[1 nRp | p-2 n!Rp | 0 n==0]
bool isSquareRemain(int n, int p){
	return qpow(n,(p-1)/2,p)==1;
}

//in uint32, p0={2,7,61} is correct
//p0={2,3,7,61,24251}, only 46856248255981 will wrong
const ll p0[]={2,3,5,7,11,13,17,19,61,2333,24251};
//1. a^(p-1)=1 (mod p) 2. if x^2=1 (mod p) then x={1,p-1}
bool witness(ll a,ll n,ll r,ll s){
	ll x=qpow(a,r,n),pre=x;
	for (int i=0;i<s;i++){
		x=qmul(x,x,n);
		if (x==1 && pre!=1 && pre!=n-1) return 0;
		pre=x;
	}
	return x==1;
}
bool MillerRabin(ll n){
	if (n<=1) return 0;
	if (n==2 || n==3 || n==5 || n==7) return 1;
	if (n%2==0 || n%3==0 || n%5==0 || n%7==0) return 0;
	ll r=n-1,s=0;
	while (!(r&1)) r>>=1,s++;
	for (int i=0;i<10;i++){
		if (p0[i]==n) return 1;
		if (!witness(p0[i],n,r,s)) return 0;
	}
	return 1;
}

//pollard_rho factorization, O(sqrt(sqrt(n))) in expection
ll pol_rho(ll n,ll c){
	if (n%2==0) return 2; if (n%3==0) return 3;
	ll k=2,x=rand()%(n-1)+1,y=x,p=1,val=1;
	for (ll i=1;p==1;i++){
		x=(qmul(x,x,n)+c)%n;
		val=qmul(val,abs(x-y),n); //gcd(ab%n,n)>=gcd(a,n)
		if (!val) return n; //if fail, return before i reach k
		if (!(i&127) || i==k) p=__gcd(val,n);
		if (i==k) y=x,k+=k;
	}
	return p;
}
vector<int> primes;
void fastfactor(ll n){
	if (n==1) return;
	if (MillerRabin(n)) {primes.push_back(n); return;} //n is prime factor
	ll t=n; //if n not always lagre, make a single factor table for int may faster 
	while (t==n) t=pol_rho(n,rand()%(n-1));
	fastfactor(t); fastfactor(n/t);
}

}
