#include "base.cpp"


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

