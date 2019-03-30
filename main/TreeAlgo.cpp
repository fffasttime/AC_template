#include "base.cpp"

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

