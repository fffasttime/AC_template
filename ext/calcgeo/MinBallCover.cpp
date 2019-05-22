#include <bits/stdc++.h>
using namespace std;
#define inc(i,n) for(int i=0;i<n;i++)
typedef double db;
struct vec{
	db x,y,z;
}p[110];
db dis(vec a, vec b){
	return sqrt((a.x-b.x)*(a.x-b.x)+(a.y-b.y)*(a.y-b.y)+(a.z-b.z)*(a.z-b.z));
}
const db eps=1e-12;
int main(){
	int n; cin>>n;
	inc(i,n) cin>>p[i].x>>p[i].y>>p[i].z;
	vec cur={0,0,0}; db r=1e6,delta=1;
	int cnt=0;
	while (delta>eps){
		int d=0; db md=0;
		inc(i,n) if (dis(cur,p[i])>md) d=i,md=dis(cur,p[i]);
		//cout<<md<<' ';
		if (md<r) r=md;
		cur.x+=(p[d].x-cur.x)*delta;
		cur.y+=(p[d].y-cur.y)*delta;
		cur.z+=(p[d].z-cur.z)*delta;
		delta*=0.99;
		cnt++;
	}
	printf("%.10f\n",r);
	return 0;
}
