#include "base.cpp"

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
//KM alg, O(n^3), faster than NetworkFlow::MCMF
namespace KM{
const ll inf=0x3f3f3f3f3f3f3f3fll;
const int maxn=410;
ll d[maxn][maxn], to[maxn];
ll ux[maxn], uy[maxn], cx[maxn], cy[maxn], cc[maxn];
int n,m;
bool find(int u){ //Same as bit graph
	ux[u]=1;
	for (int i=1;i<=m;i++){
		if (uy[i]) continue;
		if (cx[u]+cy[i]==d[u][i]){
			uy[i]=1;
			if (!to[i]||find(to[i])) {
				to[i]=u;
				return 1;
			}
		}
		else cc[i]=min(cc[i],cx[u]+cy[i]-d[u][i]);
	}
	return 0;
}
ll km(){
	for (int i=1;i<=n;i++) for (int j=1;j<=m;j++) 
		cx[i]=max(cx[i],d[i][j]);
	for (int i=1;i<=n;i++){
		memset(ux,0,sizeof ux); memset(uy,0,sizeof uy);
		memset(cc,0x3f,sizeof cc);
		if (find(i)) continue;
		ll ms,u;
		while (1){
			ms=inf;
			for (int j=1;j<=n;j++) if (!uy[j]) ms=min(ms,cc[j]);
			for (int j=1;j<=n;j++) if (ux[j]) cx[j]-=ms;
			for (int j=1;j<=n;j++) if (uy[j]) cy[j]+=ms;
				else cc[j]-=ms,cc[j]==0?u=j:0;
			if (!to[u]) break;
			uy[u]=ux[to[u]]=1;
			u=to[u];
			for (int j=1;j<=m;j++) cc[j]=min(cc[j],cx[u]+cy[j]-d[u][j]);
		}
		memset(ux,0,sizeof ux); memset(uy,0,sizeof uy);
		find(i);
	}
	ll ans=0;
	for (int i=1;i<=m;i++) ans+=d[to[i]][i];
	return ans;
}
int fr[maxn];
int main(){
	int n0,m0,k; scanf("%d%d%d",&n0,&m0,&k);
	n=m=max(n0,m0);  //km require n=m
	for (int i=1;i<=k;i++){
		int a,b,x;
		scanf("%d%d%d",&a,&b,&x);
		d[a][b]=x;
	}
	cout<<km()<<'\n';
	for (int i=1;i<=m0;i++) if (d[to[i]][i]) fr[to[i]]=i; //ignore virtual edge
	for (int i=1;i<=n0;i++) printf("%d ",fr[i]); //all match
	return 0;
}
}

namespace MatchOnGraph{
//TreeWithFlower, O(n^3)
const int maxn=1010,maxm=150010;
struct Edge{
	int to,nxt;
}e[maxm<<1];
int head[maxn],ecnt=1;
void added(int a, int b){
	e[ecnt]={b,head[a]};
	head[a]=ecnt++;
}
//match[]:... . id[]:color of a point, -1 uncolored, 0 w, 1 b
//q[]:queue, pre[]: father in bfs tree
int match[maxn],id[maxn],q[maxn],pre[maxn];
int tim,tic[maxn],fa[maxn];
int find(int x){
	if (fa[x]!=x) fa[x]=find(fa[x]);
	return fa[x];
}
int lca(int x, int y){ //find lca without deep, only use pre[] and match[]
	tim++;
	for(tim++;;swap(x,y)) //cross jump up x,y and label road
		if (x){
			x=find(x); //flower point(flower root)
			if (tic[x]==tim) return x;
			else tic[x]=tim, x=find(pre[match[x]]); //jump up
		}
}
int st,ed;
void change(int x, int y, int k){ //circle: x<-->y, x&y as lca k
	while (find(x)!=k){
		pre[x]=y;
		int z=match[x]; id[z]=0; //recolor
		q[ed++]=z; if(ed>=maxn-1) ed=1; //try find new match on each node 
		if (find(z)==z) fa[z]=k; //shrink flower to point
		if (find(x)==x) fa[x]=k; //only find(x)==x is a shrinked point
		y=z;x=pre[y];
	}
}
int n;
bool check(int u){
	for (int i=0;i<=n;i++) fa[i]=i,id[i]=-1,pre[i]=0;
	st=1,ed=2;
	q[st]=u;id[u]=0;
	while (st!=ed){ //bfs argument road
		int x=q[st];
		for (int i=head[x],v=e[i].to;i;i=e[i].nxt,v=e[i].to){
			if (!match[v]&&v!=u){ //get a valid
				pre[v]=x;
				int last,t,now=v;
				while (now){ //cross road upd, same as bit graph
					t=pre[now];
					last=match[t];
					match[t]=now;match[now]=t;
					now=last;
				}
				return 1; //ok
			}
			if (id[v]==-1){ //not visted
				id[v]=1; pre[v]=x;
				id[match[v]]=0;  //cross color
				q[ed++]=match[v];
				if (ed>=maxn-1) ed=1;
			}
			else if(id[v]==0&&find(x)!=find(v)){ //odd circle
				int g=lca(x,v); //find lca in bfs tree
				change(x,v,g);  //shink x and its father
				change(v,x,g);  //shink v and its father
			}
			//even circle is the same as bit graph, so ignored
		}
		st++;
		if (st>=maxn-1) st=1;
	}
	return 0;
}
int main(){ //same as bit graph
	int m; 
	tim=0; memset(match,0,sizeof match);
	scanf("%d%d",&n,&m);
	for (int i=0;i<m;i++){
		int x,y;
		scanf("%d%d",&x,&y);
		added(x,y); added(y,x);
	}
	for (int i=1;i<=n;i++)
		if (!match[i])
			check(i);
	int ans=0;
	for (int i=1;i<=n;i++)
		if (match[i]) ans++;
	printf("%d\n",ans/2);
	for (int i=1;i<=n;i++)
		printf("%d ",match[i]);
	return 0;
}
}

