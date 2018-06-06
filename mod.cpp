#include <iostream>
using namespace std;

#ifdef USE_ATTR
#define inc(i,n) for (int i=0;i<n;i++)
#define inc_(i,n) for (int i=1;i<=n;i++)
#define dec(i,n) for (int i=n-1;i>=0;i--)
#define fo(i,a,b) for (int i=a;i<b;i++)
#define forr(i,b,a) for (int i=b-1;i>=a;i--)
#define MP make_pair
#define PII pair<int,int>
#define MS(a,x) memset(a,x,sizeof(a))
#endif

typedef long long ll;
typedef double db;
struct T{};

int rc(){
	//return getchar(); //if use fread, input won't stop until EOF
	static char buf[10000],*p1=buf,*p2=buf;
	return p1==p2&&(p2=(p1=buf)+fread(buf,1,10000,stdin),p1==p2)?EOF:*p1++;
}
int rd(int &x){
	x=0; int f=1,c=rc(), fa=0;
	while (!isdigit(c)) c=='-'?f=-1:0,c=rc();
	while (isdigit(c)) x=x*10+c-'0', c=rc(), fa=1;
	x*=f; return fa;
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
ll qpow(ll a, int x){
	T ans=1;
	for (;x;a*=a,x>>=1)
		if (x&1)
			ans*=a;
	return ans;
}
ll qpow(ll a, int x, ll p){
	ll ans=1;
	for (;x;a=qmul(a,a,p),x>>=1)
		if (x&1)
			ans=qmul(ans,a,p);
	return ans;
}

const int N;
struct Mat{
	ll m[N][N];
	Mat(){memset(m,0,sizoef(m));}
	I(){for (int i=0;i<n;i++) m[i][i]=0;}
}
Mat mul(const &Mat a, const &Mat b){
	Mat c;
	for (int i=0;i<N;i++)
		for (int j=0;j<N;j++){
			for (int k=0;k<=N;k++)
				c.m[i][j]+=a.m[i][j]*b.m[i][j];
			//c.m[i][j]%=p;
		}
}
Mat qpow(Mat a, int x){
	Mat ans; ans.I();
	for (;x;a=mul(a,a),x>>=1)
		if (x&1)
			ans=mul(ans,a);
	return ans;
}

const int maxn;
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

//ax+by=gcd(a,b)
int exgcd(int a, int b, int &x, int &y){
	if (b==0){
		x=1;y=0;
		return a;
	}
	int t=exgcd(b,a%b,y,x);
	y-=a/b*x;
	return t;
}
int inv(int v, int p){
	int x,y;
	if (exgcd(v,p,x,y)==1)
		return (x+p)%p;
	else
		return -1;
}
//中国剩余定理
//x=a1(mod p1)
//x=a2(mod p2)
//...
ll china(int n, ll a[], ll p[]){
	ll M=1,x=0;
	for (int i=0;i<n;i++) M*=p[i];
	for (int i=0;i<n;i++)	{
		ll w=M/m[i]; //x=pi*k1+a + w*k2
		x=(x+w*inv(m[i],w)*a[i])%M; //k1 pi*k1=a (Mod w)
	}
	return (x+M)%M;
}

//中国剩余定理_非互质
//x=a1(mod m1)
//x=a2(mod m2)
//...
ll china1(int n, ll a[], ll p[]){
	ll n1=a[0],a1=a[0],n2,a2,k1,k2,K,gcd,c,t;
	for (int i=1;i<n;i++){//依次合并方程
		n2=n[i],a2=a[i]; 
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
	int m,v,e=1,i;
	m=(int)sqrt(p+0.5);
	v=inv(pow(a,m,p),p);
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
bool witness(ll a,ll b,ll r,ll s){
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
	ll r=n-1,s=0;
	while (!(r&1)) r>>=1,s++;
	for (int i=0;i<10;i++){
		if (p0[i]==n) return 1;
		if (!check(p0[i],n,r,s)) return 0;
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

void spiltprime(ll n)
{
	if (n==1) return;
	if (MillerRabin(n)) {maxs=max(maxs,n); return;} //n is prime factor
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

namespace Graph{

const int maxn=10010,maxm=100010,inf=0x3f3f3f3f;
int head[maxn],nxt[maxm],to[maxm],co[maxm],ec;
int n;
bool vis[maxn];
int ans[maxn][maxn],dis[maxn],c[maxn];

void added(int x, int y, int c){
	ec++;
	nxt[ec]=head[x];
	head[x]=ec;
	to[ec]=y;
	co[ec]=c;
}

int spfa(int s){
	queue<int> q;
	memset(dis,0x3f,sizeof(dis));
	dis[s]=0;
	memset(c,0,sizeof(c)); //判负环
	memset(vis,0,sizeof(vis));
	q.push(s); vis[s]=c[s]=1;
	while (!q.empty())	{
		int u=q.front(); q.pop();
		vis[x]=0;
		for (int e=head[x];e;e=nxt[e]){
			int v=to[k];
			if (dis[u]+co[k]<dis[v]){
				dis[v]=dis[u]+co[i];
				if (!vis[v]){
					vis[v]=1;
					c[v]++;
					q.push(v);
					if (c[v]]>n) return -0x3f3f3f3f;
				}
			}
		}
	}
}
//judge negative circle
//!-- Some reasons show it's unreliable
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
	priority_queue<pair<int,int>> qu;
	qu.push(make_pair(0,s))
	while (qu.size()){
		int u=qu.top().second, mc=-qu.top().first;
		qu.pop();
		if (vis[u]) continue;
		vis[u]=1;
		for (int e=head[u];e;e=nxt[e])
			if (!vis[to[e]] && mc+co[e]<dis[to[e]]){
				dis[to[e]]=mc+co[e];
				qu.push(make_pair(-dis[to[e]],to[e]))
			}
	}
}

void floyd(){
	for (int k=0;k<n;k++)
		for (int i=0;i<n;i++)
			for (int j=0;j<n;j++)
				if (d[i][j]>d[i][k]+d[k][j])
					d[i][j]=d[i][k]+d[k][j];
}

//mp为原图，求无向图最小环。有向图为d[i][i]。
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
int st[maxn],stn[maxn],low[maxn],idx,scn;
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
			low[u]=min(low[u],low[ed[u][i]]);
	if (low[u]==dfn[u]){
		int v;
		do{
			v=st[--stn];
			scc[scn].push_back(v);
			ins[v]=0;
		}while (u!=v);
		scn++;
	}
}
void tarjan_Caller(){
	for (int i=1;i<=n;i++)
		if (!dfn[i])
			tarjan(i);
}
bool iscut[maxn];
void tarjan_point(int u, int fa){
	int ch=0;
	low[u]=dfn[u]=++idx;
	for (int i=0;i<ed[u].size();i++){
		int v=ed[u][i];
		if (!dfn[v]){
			ch++;
			tarjan_point(v,u);
			low[u]=min(low[u],low[v]);
			if (low[v]>=dfn[u]) iscut[u]=1;
		}
		else if (dfn[v]<dfn[u] && v!=fa)
			low[u]=min(low[u],dfn[v]);
	}
	if (fa<0 && ch==1) iscut[u]=0;
}
void tarjan_ed(int u, int fa){
	low[u]=dfn[u]=++idx;
	for (int i=0;i<ed[u].size();i++){
		int v=vec[u][i];
		if (!dfn[v]){
			tarjan(v,u);
			low[u]=min(low[u],low[v]);
			if (low[v]>dfn[u])
				ansx[ansc]=x,ansy[ansc++]=y;
		}
		else if (dfn[v]<dfn[u] && v!=fa)
			low[u]=min(low[u],dfn[v]);
	}
}

int qu[maxn],vis[maxn],ans[maxn];

int circle_dp(){
	int n,m; scanf("%d%d",&n,&m);
	for (int i=0;i<n;i++) scanf("%d",a+i+1);
	for (int i=0;i<m;i++){
		int a,b;
		scanf("%d%d",&a,&b);
		ed[a].push_back(b);
	}
	for (int i=1;i<=n;i++)
		if (!dfn[i]) tarjan(i);
	for (int i=1;i<=n;i++)
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
		for (int i=0;i<ed2[u].size();i++)
		{
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
}

namespace FFT
{
typedef complex<double> cd;
const int maxl=(1<<20)+1,pi=3.14159265358979;
cd a[maxl],b[maxl];
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

char s1[maxl],s2[maxl];
int ans[maxl];
void mul(){
	scanf("%s%s",s1,s2);
	int l1=strlen(s1),l2=strlen(s2);
	int s=2,bit=1;
	for (bit=1;(1<<bit)<l1+l2-1;bit++)s<<=1;
	for (int i=0;i<l1;i++) a[i]=s1[l1-i-1]-'0';
	for (int i=0;i<l2;i++) b[i]=s2[l2-i-1]-'0';
	get_rev(bit);
	fft(a,s,1); fft(b,s,1);
	for (int i=0;i<s;i++) a[i]*=b[i];
	fft(a,s,-1);
	for (int i=0;i<s;i++){
		ans[i]+=(int)(a[i].real()+0.5);
		ans[i+1]+=output[i]/10;
		ans[i]%=10;
	}
	int i;
	for (i=l1+l2;!ans[i]&&i>=0;i--);
	if (i==-1) printf("0");
	for (;i>=0;i--) printf("%d",ans[i]);
	putchar('\n');
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

namespace TreeArr{
#define lowbit(x) (x&(-x))
const int maxn=100010;
ll tr[maxn]; int n;
ll sum(int x){
	ll ret=0;
	while (x){
		ret+=tr[x];
		x-=lowbit(x);
	}
	return ret;
}
void add(ll a, int x){
	while (x<=n){
		tr[x]+=a;
		x+=lowbit(x);
	}
}
}

namespace BipartiteGraph{
int vis[maxn]; //memset to 0 when start
//judge if a map is BipartiteGraph
bool judge(int u, int col){
	vis[u]=col;
	for (int i=0;i<n;i++)
		if (d[u][i] && (vis[i] && vis[i]!=-col || !vis[i] && !judge(i,-col))
			return 0;
	return 1;
}

const int maxn=500;
//to: m->n
int d[maxn][maxn],to[maxn],n,m;
bool vis[maxn];

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
		if (Xiong(i)) ans++;
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
	bulid(lc,l,mid); build(rc,mid,r);
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

#undef lc
#undef rc

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
queue<int> qu;
int s,t,a[maxn],fr[maxn],fp[maxn];
bool vis[maxn];
//deleted O(n^5)
int MF_FF(){
	int ans=0;
	while (1){
		memset(vis,0,sizeof(vis));
		memset(a,0,sizeof(a));
		a[s]=INF;
		while (qu.size()) qu.pop();
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
int MF_ISAP(){
	int ans=0,u=s;
	for (int i=1;i<=n;i++) now[i]=head[i],a[i]=1;
	a[t]=0; num[0]=1; num[1]=n-1;
	while (a[s]<n){
		bool ok=0;
		if (u==t){
			int mc=INF;
			for (int i=t;i!=s;i=fp[i])
				mc=min(mc,ed[fr[i]].cap-ed[fr[i]].flow);
			for (int i=t;i!=s;i=fp[i]){
				ed[fr[i]].flow+=mc;
				ed[fr[i]^1].flow-=mc;
			}
			ans+=mc; u=s;
		}
		for (int i=now[u];i;i=ed[i].nxt){
			int v=ed[i].to;
			if (a[u]==a[v]+1 && ed[i].cap>ed[i].flow){
				ok=1;
				fp[v]=u; fr[v]=i;
				now[u]=i; u=v;
				break;
			}
		}
		if (!ok){
			int c=n-1;
			for (int i=head[u];i;i=ed[i].nxt)
				if (ed[i].cap>ed[i].flow) c=min(c,a[ed[i].to]);
			if (--num[a[u]]==0) break; //gap opt
			num[a[u]=c+1]++;
			now[u]=head[u];
			if (u!=s) u=fp[u];
		}
	}
	return ans;
}

int dinic_dfs(int u, int f){
	int ans=0,w;
	if (u==t) return f;
	for (int i=now[u];i;i=ed[i].nxt){
		int v=ed[i].to;
		if (a[v]==a[u]+1 && (w=dinic_dfs(v,min(ed[i].cap-ed[i].flow,f)))>0){
			ans+=w;
			ed[i].flow+=w; ed[i^1].flow-=w;
			f-=w; if (f==0) return ans;
			now[u]=i;
		}
	}
	if (!ans) a[u]=-1;
	return ans;
}
int MF_Dinic(){
	int ans=0;
	while (1){
		memset(vis,0,sizeof(vis));
		memset(a,0,sizeof(a)); //a: level
		qu.clear(); qu.push(s); vis[s]=1;
		while (qu.size()){ //BFS
			int u=qu.fornt(); qu.pop();
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

int dis[maxn];

int MCMF(){
	int ans=0;
	while (1){
		memeset(vis,0,sizeof(vis));
		memeset(dis,0x3f,sizeof(dis));
		qu.clear(); qu.push(s);
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

#undef INF
}

namespace SAM{
const int maxn=100010,alpha=26;

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
void build(char *s){
	nodec=0;
	Node *cur;
	int sl=strlen(s);
	cur=root=open(0);
	for (int i=0;i<sl;i++){
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
//get count substr
int cnt(Node *u, char *s){
	if (*s==0) return u->num;
	if (!u->tr[*s-'a']) return 0;
	return cnt(u->tr[*s-'a'],s+1);
}
using ATTR;
int t[maxn],r[maxn]; //t:temp, r:rank
//init |right(s)| before cnt
void initnum(){
	inc(i,nodec) t[nodes[i].l]++;
	fo(i,1,s0l+1) t[i]+=t[i-1];
	inc(i,nodec) r[--t[nodes[i].l]]=i; //sort by count
	forr(i,nodec,1) nodes[r[i]].p->num+=nodes[r[i]].num; //dp
}
int lcs(char *x1){
	int lcs=0, ans=0, xl=strlen(x1);
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
void upd(int u){
	siz[u]=cnt[u]+siz[lc]+siz[rc];
}
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
	if (pa[u]) ch[pa[p]][ch[pa[u]][1]==p]=u;
	ch[u][c]=p; pa[p]=u;
	upd(p);
}
//u->under s
void splay(int u, int s){
	pushdown(u);
	while (pa[u]!=s)
		if (pa[pa[u]]==s) rot(u,ch[pa[u]][0]==u);
		else{
			int p=pa[u],pp=pa[p],c=(ch[pp][0]==p);
			if (ch[p][c]==u) rot(u,!c),rot(u,c);
			else rot(p,c),rot(u,c);
		}
	upd(u);
	if (s==0) root=u;
}
//rank k->under s
void rk(int k, int s){
	int u=root;
	k=max(k,1); k=min(k,siz[root]);
	while (1){
		pushdown(u);
		if (k<=siz[lc]) u=lc;
		else if (k>siz[lc]+cnt[u]) k-=siz[lc]+cnt[u],u=rc;
		else break;
	}
	splay(u,s);
}
//x->under s
void fi(int x, int s){
	int u=root,p;
	while (x!=val[u] && u)
		p=u,u=ch[u][x>val[u]];
	if (u && x==val[u]) splay(u,s);
	else if (!u) splay(p,s);
}
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
		root=rc; rk(1,0);
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
void debug(int u, int deep){
	if (!u) return;
	debug(lc, deep+1);
	for (int i=0;i<deep;i++) cout<<"  ";
	cout<<val[u]<<' '<<siz[u]<<'\n';
	debug(rc, deep+1);
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
double a[maxn][maxm],b[maxn][maxn],ans[maxn],n,m;
//require m=n+1
void gauss_solve(){
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (maxl!=i) swap(a[i],a[maxl]);
		double r=a[i][i];
		if (fabs(r)<eps) return 0; //No trivil
		for (int j=i+1;j<n;j++){
			r=a[j][i]/a[i][i];
			for (int k=i;k<m;k++)
				a[j][k]-=r*a[i][k];
		}
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
		double r=a[i][i];
		if (fabs(r)<eps) return 0; //No trivil
		for (int k=0;k<n;k++) a[i][k]/=r,b[i][k]/=r; //k start from 0
		for (int j=i+1;j<n;j++){
			r=a[j][i]/a[i][i];
			for (int k=0;k<n;k++)
				a[j][k]-=r*a[i][k],
				b[j][k]-=r*b[i][k];
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
		double r=a[i][i];
		if (fabs(r)<eps) return 0;
		for (int j=i+1;j<n;j++){
			r=a[j][i]/a[i][i];
			for (int k=i;k<n;k++)
				a[j][k]-=r*a[i][k];
		}
	}
	for (int i=0;i<n;i++) ans*=a[i][i];
	return ans;
}
int matrank(){
	int l=0;
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=l+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (i!=maxl) swap(a[i],a[maxl]),ans=-ans;
		double r=a[l][i];
		if (fabs(r)<eps) continue;
		for (int j=l+1;j<n;j++){
			r=a[j][i]/a[l][i];
			for (int k=i;k<m;k++)
				a[j][k]-=r*a[i][k];
		}
		l++;
	}
	return l;
}
ll p=19260817;
//int det with abs,mod
//used by Matrix-Tree theorem
//M-T theo: a[i][i]=-deg i, a[i][j]=cnt(i->j), n=|u|-1
//!--
ll detint_abs(){
	ll ans=1;
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (a[j][i]>0) {maxl=j;break;}
		if (i!=maxl) swap(a[i],a[maxl]);
		if (a[i][i]==0) return 0;
		for (int j=i+1;j<n;j++){
			if (!a[j][i]) continue;
			ans=ans*a[i][i]%p; //multi div op
			for (int k=i;k<n;k++)
				a[j][k]=(a[j][k]*a[i][i]-a[j][i]*a[i][k]+p)%p;
		}
	}
	ans=inv(ans,p);
	for (int i=0;i<n;i++) ans=ans*a[i][i]%p;
	return ans;
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
namespace multiply{
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
	return 0;
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
		if ((ans^base[j])>ans)
			ans^=base[i];
	return ans;
}
//min xor sum
ll minc(){for (int i=0;i<64;i++) if (base[i]) return base[i];}
//query kth max number
//k should not larger than 2^(dim linspan(x))
ll kth(ll k){
	ll ans=0,tmp[64],res=0,cnt=0;
    for(T i=0;i<64;i++){ //set matrix to simplest form
        for(int j=i-1;j>=0;j--)
			if(base[i]&1ull<<j) base[i]^=base[j];
        if(base[i])tmp[cnt++]=base[i];
    }
	for (int i=63;i>=0;i--)
		if (k&1ull<<i)
			ans^=base[i];
	return ans;
}
}

int main(){
	return 0;
}
