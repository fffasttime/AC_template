#include <bits/stdc++.h>
using namespace std;
typedef long long db;
const int N=2010;

#define Vec const vec &
struct vec{
	db x,y;
	vec operator-(Vec v)const{return {x-v.x,y-v.y};}
	db operator&(Vec v)const{return {x*v.y-y*v.x};}
	bool operator<(Vec v)const{return y==v.y?x<v.x:y<v.y;}//y order
	void rd(){scanf("%lld%lld",&x,&y);}
	void prt(){printf("%lld %lld",x,y);}
}p[N];
db cross(Vec a, Vec b, Vec c){return b-a&c-a;}

struct Lin{
	int a,b; vec v;
	bool operator<(const Lin &u){return (v&u.v)>0;}
}lin[N*N];
int d[N];

int main(){
	int n; while (cin>>n){
		for (int i=0;i<n;i++) p[i].rd(),d[i]=i;//p[i].oridx=i;
		sort(p,p+n); //[!] sort p by y axis, here x<v.x is also important
		int linc=0;
		for (int i=0;i<n;i++)
			for (int j=i+1;j<n;j++) //[!] only scan y+ direction
				lin[linc++]={i,j,p[j]-p[i]};
		sort(lin,lin+linc);
		db mim=9e18, mam=0;
		for (int i=0;i<linc;i++){
			int a=d[lin[i].a], b=d[lin[i].b]; //because p swapped, now d[a] is real index of lin[i].a
			assert(a+1==b);
			if (a && b<n-1) mam=max(mam,cross(p[a],p[0],p[b])+cross(p[a],p[b],p[n-1]));
			if (a && b<n-1) mim=min(mim,cross(p[a],p[a-1],p[b])+cross(p[a],p[b],p[b+1]));
			//... here can do some binary search on p[] 
			swap(p[a],p[b]); swap(d[lin[i].a],d[lin[i].b]); //swap order
			//swap(rk[p[a].oridx],rk[p[b].oridx]); //original p0 rank
		}
		printf("%lld %lld\n",mim,mam);
	}
	return 0;
}

