#include <bits/stdc++.h>
using namespace std;

const int maxl=10000; //maxl: numbers of 1 + and numbers of col + 1
//Dancing link Node array:   row,col: the original pos   H:row head  S:col size
int L[maxl],R[maxl],U[maxl],D[maxl],H[maxl],S[maxl],col[maxl],row[maxl];
int siz,m; //m: cols, siz: cur insert node (aka nodec)
void pre(){
	for (int i=0;i<=m;i++){ //init column head node(first line)
		L[i]=i-1; R[i]=i+1;
		col[i]=i;
		U[i]=D[i]=i;
		row[i]=-1;
	}
	R[m]=0; L[0]=m; //node 0 is head of first line
	siz=m+1;
	memset(H,0,sizeof(H)); //H[first line]=0
	memset(S,0,sizeof(S));
	S[0]=maxl+1; //S[0] larger than any col head
}
//[!] insert should strictly by row order first, col order second
//[!] the start coord is (1,1), not (0,0)
void insert(int r, int c){
	U[siz]=U[c];
	D[siz]=c;
	U[D[siz]]=D[U[siz]]=siz;
	if (H[r]){
		L[siz]=L[H[r]];
		R[siz]=H[r];
		L[R[siz]]=R[L[siz]]=siz;
	}
	else H[r]=L[siz]=R[siz]=siz; //new line node
	row[siz]=r; col[siz]=c;
	S[c]++;
	siz++;
}
//remove a col affected rows
void del(int c){
	L[R[c]]=L[c];
	R[L[c]]=R[c];
	for (int i=D[c];i!=c;i=D[i]) //remove this loop statment in 
		for (int j=R[i];j!=i;j=R[j]){ // repeat coverage problem
			U[D[j]]=U[j];
			D[U[j]]=D[j];
			S[col[j]]--;
		}
}
void back(int c){
	for (int i=D[c];i!=c;i=D[i]) //remove this loop statment in 
		for (int j=R[i];j!=i;j=R[j]){ // repeat coverage problem
			U[D[j]]=D[U[j]]=j;
			S[col[j]]++;
		}
	R[L[c]]=L[R[c]]=c;
}
bool vis[maxl]; //here size m is enough
int leave(){ //how many lines should be removed at least
    int ans=0;
    memset(vis,0,sizeof(vis));
    for(int i=R[0];i;i=R[i])
        if(!vis[i]){
            vis[i]=1; ans++;
            for(int j=D[i];j!=i;j=D[j]){
                for(int k=R[j];k!=j;k=R[k])
                	vis[col[k]]=1;
            }
        }
    return ans;
}
int ans[maxl],ansc;
//ans[k]: selected row;  H[ans[k]]: selected line head
bool dfs(int k){ //X-algorithm, k: current row
	//if (k+leave()>=min_ans_k) return 0; //purning in repeat coverage prob 
	if (R[0]==0) //Success
		return ansc=k,1;
	int mins=1e8, c=0;
	for (int t=R[0];t;t=R[t]) //find minimum col size
		if (S[t]<mins)        // small branch early is better for purning
			mins=S[t],c=t;    // so search is not by col order
	if (!c) return 0;
	del(c);
	for (int i=D[c];i!=c;i=D[i]){ //enum which line to remove
		ans[k]=row[i];  //selected row
		for (int j=R[i];j!=i;j=R[j]) del(col[j]);
		if (dfs(k+1)) return 1; //return when only search one solution 
		for (int j=L[i];j!=i;j=L[j]) back(col[j]);
	}
	back(c);
	return 0;
}
//9x9 sudoku solver
//first 81: a pos is filled; next 81: a row filled 1~9; next 81: col filled; last 81:square filled
int out[9][9];
void solve(int a[9][9]){
	m=324;
	pre();
	int n=1;
	for (int i=0;i<9;i++)
		for (int j=0;j<9;j++)
			if (a[i][j]){
				insert(n,i*9+j+1); 
				insert(n,81+i*9+a[i][j]); 
				insert(n,162+j*9+a[i][j]); 
				insert(n,243+(i/3*3+j/3)*9+a[i][j]); 
				n++;
			}
			else{
				for (int k=1;k<=9;k++){
					insert(n,i*9+j+1); 
					insert(n,81+i*9+k); 
					insert(n,162+j*9+k); 
					insert(n,243+(i/3*3+j/3)*9+k); 
					n++;
				}
			}
	dfs(0);
	for (int i=0;i<81;i++){ //get selected pos and filled number
		int p=col[H[ans[i]]]-1, x=(col[R[H[ans[i]]]]-1)%9+1; 
		out[p/9][p%9]=x;
	}
	for (int i=0;i<9;i++,cout<<'\n')
		for (int j=0;j<9;j++)
			cout<<out[i][j]<<' ';
}

int n0,sum; //n0: initial size, sum: all available state
void dfs_nqueen(int k){
	if (R[0]>n0){ //slashs don't require filled 
		sum++;
		return;
	}
	int mins=1e8, c=0;
	for (int t=R[0];t<=n0*2;t=R[t]) //ignore slashs
		if (S[t]<mins)
			mins=S[t],c=t;
	if (!c) return;
	del(c);
	for (int i=D[c];i!=c;i=D[i]){
		for (int j=R[i];j!=i;j=R[j]) del(col[j]);
		dfs_nqueen(k+1);
		for (int j=L[i];j!=i;j=L[j]) back(col[j]);
	}
	back(c);
}
//[!] only for demo, this algo is not faster than brute force
//bitwise aglo is fastest 
void nqueens(int n){
	int l=1; n0=n; m=n*6-2; sum=0;
	pre();
	for (int i=0;i<n;i++)
		for (int j=0;j<n;j++){
			insert(l,i+1);
			insert(l,n+j+1);
			insert(l,n*2+i+j+1); //slash
			insert(l,n*5+i-j-1);
			l++;
		}
	dfs_nqueen(0);
	cout<<sum<<'\n';
}
int main(){
	int n; cin>>n>>m;
	pre(); //[!] do not forget init
	for (int i=1;i<=n;i++)
		for (int j=1;j<=m;j++){
			int t; scanf("%d",&t);
			if (t==1) insert(i,j);
		}
	if (!dfs(0)) return puts("No Solution!"),0;
	sort(ans,ans+ansc);
	for (int i=0;i<ansc;i++) printf("%d ",ans[i]);
	return 0;
}

