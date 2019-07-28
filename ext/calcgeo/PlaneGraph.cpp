#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
#define inc(i,n) for (int i=0;i<n;i++)
const int N=100010;
typedef double db;
const db eps=1e-10;
bool eq(db x){return fabs(x)<eps;}
struct vec{
	db x,y;
	vec operator-(const vec &v)const{return {x-v.x,y-v.y};}
	bool operator<(const vec &v) const{return eq(x-v.x)?y<v.y:x<v.x;}
	db operator&(const vec &v)const{return x*v.y-y*v.x;}
	void rd(){scanf("%lf%lf",&x,&y);}
	db ang()const{return atan2(y,x);}
}p[N*3];//p[n..n+2q] used for question

const db pi=acos(-1);

struct Edge{ //main transfer structure
	db ang; int u,v,w; bool vis; //w: edge weight
	int rk, fr; //rk: angle rank,  fr: dual graph lable of left side
	Edge(){}
	Edge(int u, int v, int w):u(u),v(v),w(w){
		ang=(p[v]-p[u]).ang();
		vis=0;
		rk=fr=0;
	}
	bool operator<(const Edge &v)const{return ang<v.ang;}
}ed[N<<1];
int edc=1,gcnt=0;

vector<int> ed1[N];

struct Ed2{
	int x,y,w;
	bool operator<(const Ed2 &v)const{
		return w<v.w;
	}
}ed2[N<<1];
struct Ed3{
	int to,nxt,w;
}ed3[N<<1];

int h3[N],ed3c;

void add3(int x, int y, int w){
	ed3c++;
	ed3[ed3c]={y,h3[x],w};
	h3[x]=ed3c;
	ed3c++;
	ed3[ed3c]={x,h3[y],w};
	h3[y]=ed3c;
}
int pa[24][N],dep[N],maxn[24][N];

int lca(int u, int v){
	int maxx=0;
	if (dep[u]<dep[v]) swap(u,v);
	for (int k=23;k>=0;k--)
		if (dep[pa[k][u]]>=dep[v]) maxx=max(maxx,maxn[k][u]),u=pa[k][u];
	if (u^v){
		for (int k=23;k>=0;k--)
			if (pa[k][u]!=pa[k][v]){
				maxx=max(maxx,max(maxn[k][u],maxn[k][v]));
				u=pa[k][u],v=pa[k][v]; 			
			}
		maxx=max(maxx,max(maxn[0][u],maxn[0][v]));
		u=pa[0][u];
	}
	return maxx;
}
void dfs_deep(int u, int f){
	for (int e=h3[u];e;e=ed3[e].nxt){
		int v=ed3[e].to;
		if (v^f){
			dep[v]=dep[u]+1;pa[0][v]=u;
			maxn[0][v]=ed3[e].w;
			for (int k=1;pa[k-1][pa[k-1][v]];k++)
				pa[k][v]=pa[k-1][pa[k-1][v]];
			for (int k=1;pa[k-1][pa[k-1][v]];k++)
				maxn[k][v]=max(maxn[k-1][v],maxn[k-1][pa[k-1][v]]);
			dfs_deep(v,u);
		}
	}
}

db curx;
db liney(int li){
	int ea=ed[li].u, eb=ed[li].v;
	db rate=(curx-p[ea].x)/(p[eb].x-p[ea].x);
	return (1-rate)*p[ea].y+rate*p[eb].y;
}
struct DS{
	int x;
	bool operator<(const DS &v)const{
		if(x>edc) return p[x-edc-1].y-liney(v.x);
		if(v.x>edc) return liney(x)<p[v.x-edc-1].y;
		return liney(x)<liney(v.x);}
};
int qs[N*3],ansp[N*2];
int fa[N];
int fi(int x){
	if (x!=fa[x]) fa[x]=fi(fa[x]);
	return fa[x];
}
int main(){
	int n,m; scanf("%d%d",&n,&m);
	inc(i,n) p[i].rd(); //point
	inc(i,m){
		int x,y,w;
		scanf("%d%d%d",&x,&y,&w); //endpoints of line
		x--; y--;
		ed[++edc]=Edge(x,y,w);
		ed1[x].push_back(edc);
		ed[++edc]=Edge(y,x,w);
		ed1[y].push_back(edc);
	}
	inc(i,n){
		sort(ed1[i].begin(),ed1[i].end(),[&](int a, int b){return ed[a].ang<ed[b].ang;});
		inc(j,ed1[i].size())
			ed[ed1[i][j]].rk=j;
	}
	int gout;
	for (int i=2;i<=edc;i++) if(!ed[i].vis){ //new
		int u=ed[i].u; int cur=i;
		gcnt++;
		db area=0;
		while (!ed[cur].vis){ //face
			ed[cur].fr=gcnt;
			ed[cur].vis=1;
			area+=(p[ed[cur].u]-p[u])&(p[ed[cur].v]-p[u]);
			int sz=ed1[ed[cur].v].size();
			int rk1=(ed[cur^1].rk-1+sz)%sz;
			cur=ed1[ed[cur].v][rk1];
		}
		if (area<0) gout=gcnt;
	}
	//----------------
	int ed2c=0;
	for (int i=2;i<=edc;i++) if(ed[i].fr!=gout && ed[i^1].fr!=gout) ed2[ed2c++]={ed[i].fr,ed[i^1].fr,ed[i].w}; //kruskal edge
	sort(ed2,ed2+ed2c);
	for (int i=1;i<=gcnt;i++) fa[i]=i;
	for (int i=0;i<ed2c;i++){
		int ta=fi(ed2[i].x),tb=fi(ed2[i].y);
		if (ta^tb) add3(ed2[i].x,ed2[i].y,ed2[i].w),fa[ta]=tb;
	}
	dep[1]=1; dfs_deep(1,0);
	//---------------- scanner line ------------------
	int q; scanf("%d",&q);
	for (int i=0;i<q;i++){p[i*2+n].rd();p[i*2+1+n].rd();} 
	inc(i,n+q*2) qs[i]=i; //sort by x-axis
	sort(qs,qs+n+q*2,[&](int a, int b){return p[a]<p[b];});
	reverse(qs,qs+n+q*2); //right to left
	set<DS> se;
	inc(i,n+q*2){
		int u=qs[i];
		curx=p[u].x;
		if (u<n){ //graph point
			curx=p[u].x+0.1;
			for(auto e:ed1[u]){ 
				if (eq(ed[e].ang-pi/2) || eq(ed[e].ang+pi/2)) continue;
				if (ed[e].ang<pi/2 && ed[e].ang>-pi/2)
					se.erase((DS){e^1});
			}
			curx=p[u].x-0.1;
			for(auto e:ed1[u]){
				if (eq(ed[e].ang-pi/2) || eq(ed[e].ang+pi/2)) continue;
				if (ed[e].ang>pi/2 || ed[e].ang<-pi/2)
					se.insert((DS){e});
			}
		}
		else{  //question point
			int fr;
			auto it=se.lower_bound((DS){u+edc+1});
			if (se.empty() || it==se.end()) fr=gout;
			else fr=ed[it->x].fr;
			ansp[u-n]=fr;
		}
	}
	for(int i=0;i<q;i++){
		if (ansp[i*2]==gout || ansp[i*2+1]==gout) puts("-1");
		else printf("%d\n",lca(ansp[i*2],ansp[i*2+1]));
	}
	return 0;
}
