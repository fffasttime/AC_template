#include "base.cpp"


namespace NetFlow{
#define INF 0x3f3f3f3f
const int maxn=1003,maxm=10003<<4;
struct Edge{
	int to,nxt,cap,cost; //assert cap>=0
}ed[maxm];
int head[maxn],ecnt=1,n,m;
void added(int a, int b, int cap){
	ed[++ecnt]=(Edge){b,head[a],cap,0};
	head[a]=ecnt;
	ed[++ecnt]=(Edge){a,head[b],0,0};
	head[b]=ecnt;
}
int s,t,a[maxn],fr[maxn],fp[maxn];
bool vis[maxn];
//deleted O(VE^2)
#ifdef USE_DELETED
int MF_EK(){
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
				if (!vis[v] && ed[i].cap){
					vis[v]=1;
					a[v]=min(a[u],ed[i].cap);
					fp[v]=u; fr[v]=i;
					qu.push(v);
				}
			}
		}
		if (!a[t]) break;
		ans+=a[t];
		for (int i=t;i!=s;i=fp[i]){
			ed[fr[i]].cap-=a[t];
			ed[fr[i]^1].cap+=a[t];
		}
	}
	return ans;
}
#endif

//isap, worst O(V^2E), but fast enough on most meaningful graph
//on layered graph is O(VE), and on unit capicity graph is O(E^1.5)
int now[maxn],num[maxn];
int isap_aug(int u, int f){
	if (u==t) return f;
	int ans=0;
	for (int i=now[u],v=ed[i].to;i;i=ed[i].nxt,v=ed[i].to)
		if (a[u]==a[v]+1){
			int w=isap_aug(v,min(f,ed[i].cap));
			ans+=w; f-=w; ed[i].cap-=w; ed[i^1].cap+=w; //aug
			if (!f) return ans;
			now[u]=i;
		}
	if (!(--num[a[u]])) a[s]=n+1; //gap opt
	++num[++a[u]]; now[u]=head[u];
	return ans;
}
int MF_isap(){
	memset(num,0,sizeof(num)); //num: label cnt
	memset(a,0,sizeof(a)); //a: label
	for (int i=1;i<=n;i++) now[i]=head[i];
	static int qu[maxn];
	int ql,qr=1; qu[ql=0]=t;
	++num[a[t]=1];
	while (ql<qr){ //optimize, bfs label at first
		int u=qu[ql++];
		for (int i=head[u],v=ed[i].to;i;i=ed[i].nxt,v=ed[i].to)
			if (!a[v]) ++num[a[v]=a[u]+1],qu[qr++]=v;
	}
	ll ret=isap_aug(s,INF);
	while (a[s]<=n) ret+=isap_aug(s,INF);
	return ret;
}

//deleted, similar as MF_isap
int dinic_dfs(int u, int f){
	int ans=0,w;
	if (u==t) return f;
	for (int i=now[u];i;i=ed[i].nxt){
		int v=ed[i].to;
		if (a[v]==a[u]+1 && ed[i].cap && (w=dinic_dfs(v,min(ed[i].cap,f)))){
			ans+=w;
			ed[i].cap-=w; ed[i^1].cap+=w;
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
				if (!vis[v] && ed[i].cap){
					qu.push(v);
					a[v]=a[u]+1;
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
	ed[++ecnt]=(Edge){b,head[a],cap,cost};
	head[a]=ecnt;
	ed[++ecnt]=(Edge){a,head[b],0,-cost};
	head[b]=ecnt;
}
int dis[maxn];
int MCMF(){
	int ans=0,mf=0;
	while (1){
		memset(vis,0,sizeof(vis));
		memset(dis,0x3f,sizeof(dis));
		queue<int> qu; qu.push(s);
		dis[s]=0; vis[s]=1;
		while (qu.size()){ //spfa
			int u=qu.front(); qu.pop(); vis[u]=0;
			for (int i=head[u];i;i=ed[i].nxt){
				int v=ed[i].to;
				if (ed[i].cap && dis[v]>dis[u]+ed[i].cost){
					dis[v]=dis[u]+ed[i].cost;
					fr[v]=i; fp[v]=u;
					if (!vis[v]) vis[v]=1,qu.push(v);
				}
			}
		}
		if (dis[t]>INF/3) break;
		int mc=INF;
		for (int i=t;i!=s;i=fp[i]) mc=min(mc,ed[fr[i]].cap);
		for (int i=t;i!=s;i=fp[i]){
			ed[fr[i]].cap-=mc;
			ed[fr[i]^1].cap+=mc;
			ans+=mc*ed[fr[i]].cost;
		}
		mf+=mc;
	}
	cout<<mf<<' ';
	return ans;
}
//dijkstra version, more stable. 
//[!] The cost should be positive before first argument, or the
// complexity is not right. Run SPFA on first step is requied. 
int h[maxn];
int MCMF_dijk(){
	memset(h,0,sizeof(h)); //set h[all vertex] to 0
	int ans=0;
	while (1){
		priority_queue<pair<int,int>,vector<pair<int,int>>,greater<pair<int,int>>> qu;
		memset(dis,0x3f,sizeof(dis));
		dis[s]=0; qu.push({0,s});
		while (!qu.empty()){
			int du=qu.top().first, u=qu.top().second;
			qu.pop();
			if (dis[u]<du) continue;
			for (int i=head[u],v=ed[i].to;i;i=ed[i].nxt,v=ed[i].to)
				if (ed[i].cap && dis[v]>dis[u]+ed[i].cost+h[u]-h[v]){
					dis[v]=dis[u]+ed[i].cost+h[u]-h[v];
					fp[v]=u; fr[v]=i;
					qu.push({dis[v],v});
				}
		}
		if (dis[t]>INF/3) break;
		for (int i=0;i<=n;i++) h[i]+=dis[i];
		int mc=INF;
		for (int i=t;i!=s;i=fp[i]) mc=min(mc,ed[fr[i]].cap);
		for (int i=t;i!=s;i=fp[i]){
			ed[fr[i]].cap-=mc;
			ed[fr[i]^1].cap+=mc;
			ans+=mc*ed[fr[i]].cost;
		}
	}
	return ans;
}

//zkw cost flow, faster on wide and small capicity graph
int zkw_ans;
int dfs_aug(int u, int f){
	vis[u]=1;
	if (u==t) return f;
	int w,ad=0; 
	for (int i=head[u];i;i=ed[i].nxt){
		int v=ed[i].to;
		if (!vis[v] && ed[i].cap && dis[u]-ed[i].cost==dis[v] && (w=dfs_aug(v,min(f,ed[i].cap)))){
			zkw_ans+=w*ed[i].cost; ad+=w;
			ed[i].cap-=w; ed[i^1].cap+=w;
			if (f==0) break;
		}
	}
	return ad;
}
int MCMF_zkw(){
	int zkw_mf=0; zkw_ans=0;
	while (1){
		memset(vis,0,sizeof(vis));
		memset(dis,0x3f,sizeof(dis));
		queue<int> qu; qu.push(t);
		dis[t]=0; vis[t]=1;
		while (qu.size()){ //spfa on reverse path
			int u=qu.front(); qu.pop(); vis[u]=0;
			for (int i=head[u];i;i=ed[i].nxt){
				int v=ed[i].to;
				if (ed[i^1].cap && dis[v]>dis[u]-ed[i].cost){
					dis[v]=dis[u]-ed[i].cost;
					if (!vis[v]) vis[v]=1,qu.push(v);
				}
			}
		}
		if (dis[s]>INF/3) break;
		memset(vis,0,sizeof vis);
		zkw_mf+=dfs_aug(s, INF);
	}
	cout<<zkw_mf<<' ';
	return zkw_ans;
}

#undef INF
}

