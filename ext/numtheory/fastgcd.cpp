#include <bits/stdc++.h>
using namespace std;

const int N=5000010, sn=sqrt(N);

bool isp[N];
int pre[N],p[N],pc,g[sn+2][sn+2],sp[N][3]; //pre: smallest prime factor
//O(n)-O(1) fast gcd algorithm
void init_gcd(){
	memset(isp,1,sizeof(isp));
    isp[1]=0;
    for(int i=2;i<N;i++){
        if(isp[i]) p[pc++]=pre[i]=i;
        for(int j=0;j<pc && i*p[j]<N;j++){
            isp[i*p[j]]=0;
            pre[i*p[j]]=p[j];
            if(i%p[j]==0) break; 
        }
    }
    sp[1][0]=sp[1][1]=sp[1][2]=1; //get 3 factor table
    for(int i=2;i<N;i++){
        memcpy(sp[i],sp[i/pre[i]],sizeof sp[i]);
        if(sp[i][0]*pre[i]<=sn) sp[i][0]*=pre[i];
        else if(sp[i][1]*pre[i]<=sn) sp[i][1]*=pre[i];
        else sp[i][2]*=pre[i]; //spilt[i][2] may > sqrt(N) when it's prime 
    }
    for(int i=0;i<=sn;i++) //get gcd table for x<=sqrt(N)
		for(int j=0;j<=i;j++){
	        if(!i||!j) g[i][j]=i|j;
	        else g[i][j]=g[j][i]=g[j][i%j];
	    }
}
int gcd(int x,int y){ //[!] x should not be 0
	//if (x<=sn && y<=sn) return x<y?g[y][x]:g[x][y];
    int ans,d=g[sp[x][0]][y%sp[x][0]];
    ans=d,y/=d;
	d=g[sp[x][1]][y%sp[x][1]];
    ans*=d,y/=d;
    if(sp[x][2]<=sn) d=g[sp[x][2]][y%sp[x][2]];
    else d=y%sp[x][2]?1:sp[x][2]; //judge large prime factor
    return ans*d;
}

int main(){
	clock_t t0=clock();
	init_gcd(); int ans=0;
	for (int i=0;i<10000000;i++){
		int x=rand()+1,y=rand()+1;
		ans+=gcd(x,y);
	}
	cout<<clock()-t0<<'\n';
}
