#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
using namespace std;

typedef long long ll;
const int maxn=510, maxm=2010;
#define INF 1e9

const int N=510;

int a[N][N];

int dis[N], node[N];
bool vis[N];
//O(V^3), and we can optimze to O(V(V+E)log(V))
//a[0..n-1][0..n-1] is graph weight
//dis[] indicates current cut size to close-list,
// the prim-like algo insert max dis[] node into close-list 
int StoerWangner(int n){
	for (int i=0;i<n;i++) node[i]=i;
	int ans=INF;
	while (n>1){ //iterations
		int maxx=1, prev=0;
		//prim-like algorithm
		memset(vis,0,sizeof vis);
		vis[node[0]]=1;
		for (int i=1;i<n;i++){ //first step of prim
			dis[node[i]]=a[node[0]][node[i]];
			if (dis[node[i]]>dis[node[maxx]])
				maxx=i;
		}
		for (int i=1;i<n;i++){
			if (i==n-1){ //iter end, merge s-t, here merge maxx to prev
				ans=min(ans, dis[node[maxx]]);
				for (int k=0;k<n;k++) //merge node without disjoint set
					a[node[k]][node[prev]]+=a[node[k]][node[maxx]],
					a[node[prev]][node[k]]+=a[node[k]][node[maxx]];
				node[maxx]=node[--n]; //delete maxx node
			}
			vis[node[maxx]]=1;
			prev=maxx;
			maxx=-1;
			for(int j=1;j<n;j++) if (!vis[node[j]]){
				dis[node[j]]+=a[node[prev]][node[j]]; //upd dis
				if (maxx==-1 || dis[node[j]]>dis[node[maxx]]) //upd maxx
					maxx=j;
			}
		}
	}
	return ans;
}

//poj 2914
int main(){
	int n,m;
	while (~scanf("%d%d",&n,&m)){
		memset(a,0,sizeof a);
		while(m--){
			int u,v,w;
			scanf("%d%d%d",&u,&v,&w);
			a[u][v]+=w;
			a[v][u]+=w;
		}
		printf("%d\n",StoerWangner(n));
	}
	return 0;
}

