#include "base.cpp"

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
	//add edge...
    //tarjan_point(1,-1); //mark dcc point
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
int deg[maxn],ansp[maxm],al,anse[maxm<<1],el; //ansp has maxm point at most
//O(n+m), euler cycle
//the graph MUST BE only 0 or 2 odd node, and if there is 2 odd node, u must be odd node
//if more than 2 odd point, add virtual edge, and slice result by virtual edge
void euler(int u){
	for (int e=head[u];e;e=ed[e].nxt){
		int v=ed[e].to;
		if (!ed[e].vis && !ed[e^1].vis){
			ed[e].vis=ed[e^1].vis=1;
			euler(v);
			anse[++el]=e;//ed, the road and point will be reversed
		}
	}
	ansp[++al]=u;
}
#endif

#ifdef NO_COMPILE

//min directed tree, chu_liu's alg, O(VE)
const int maxn=1010,inf=0x3f3f3f3f;
struct Edge{
	int u,v,w;
}ed[maxn];
//in[]: min in edge weight, fa[]: min in vertex, id[]:scc id
int in[maxn],fa[maxn],vis[maxn],id[maxn];
int n,m,root;
ll chu_liu(){
	ll ans=0; int cnt,u,v;
	while (1){
		cnt=0; //circnt
		icc(i,n) in[i]=inf, vis[i]=id[i]=0;
		icc(i,m)
			if (ed[i].u!=ed[i].v&&ed[i].w<in[ed[i].v]) //min in edge
				fa[ed[i].v]=ed[i].u,in[ed[i].v]=ed[i].w;
		in[root]=0;
		icc(i,n){
			if (in[i]==inf) return -1;
			ans+=in[i];
			for (u=i;u!=root&&vis[u]!=i&&!id[u];u=fa[u]) //find circle
				vis[u]=i;
			if (u!=root&&!id[u]){
				id[u]=++cnt;
				for (v=fa[u];v!=u;v=fa[v]) id[v]=cnt; //label circle
			}
		}
		if (!cnt) return ans;
		icc(i,n) if(!id[i]) id[i]=++cnt; //single scc
		icc(i,m){ //build new graph on scc
			int laz=in[ed[i].v];
			if ((ed[i].u=id[ed[i].u])!=(ed[i].v=id[ed[i].v])) 
				ed[i].w-=laz; //new weight if exchange out cir edge
		}
		n=cnt; root=id[root];
	}
}
int chu_liu_caller(){
	scanf("%d%d%d",&n,&m,&root);
	icc(i,m) scanf("%d%d%d",&ed[i].u,&ed[i].v,&ed[i].w);
	cout<<chu_liu()<<'\n';
	return 0;
}
#endif
}

