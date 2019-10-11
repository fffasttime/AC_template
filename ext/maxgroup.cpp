#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <algorithm>
using namespace std;

const int maxn=105;

int w[maxn][maxn],n;

int ans,ansp[maxn],tp[maxn];

void dfs(int x, int c){
	if (x>n){
		if (c>ans) ans=c,copy(tp,tp+c,ansp);
		return;
	}
	for (int i=0;i<c;i++)
		if (!w[x][tp[i]]) goto next;
	tp[c]=x;
	dfs(x+1,c+1); //add to group	
next:
	if (c+n-x>ans) //purning: remain space > ans
	dfs(x+1,c);
}

int main(){
	int T; cin>>T;
	while (T--){
		int m; cin>>n>>m;
		memset(w,0,sizeof w);
		for (int i=0;i<m;i++){
			int a,b; scanf("%d%d",&a,&b);
			w[a][b]=w[b][a]=1;
		}
		for (int i=1;i<=n;i++)
			for (int j=1;j<=n;j++)
				if (i^j) w[i][j]=!w[i][j];
		ans=0;
		dfs(1,0);
		cout<<ans<<'\n';
		for (int i=0;i<ans;i++) cout<<ansp[i]<<' ';
		cout<<'\n';
	}
	return 0;
}


