#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
#define inc(i,n) for (int i=0;i<n;i++)
const int N=100010;

int sgn(ll x){
if (x<0) return -1;
return x>0;
}

#define Vec const vec&
struct vec{
	ll x,y;
	vec operator+(Vec v)const{return {x+v.x,y+v.y};}
	vec operator-(Vec v)const{return {x-v.x,y-v.y};}
	vec operator*(ll a)const{return {x*a,y*a};}
	vec operator/(ll a)const{return {x/a,y/a};}
	ll operator&(Vec v)const{return x*v.y-y*v.x;}
	ll operator|(Vec v)const{return x*v.x+y*v.y;}
	bool operator!=(Vec v)const{return x!=v.x || y!=v.y;}
	bool operator<(Vec v)const{return x==v.x?y<v.y:x<v.x;}
	int id()const{if (y>0) return x<0?1:0; return x<0?2:3;}
	void rd(){scanf("%d%d",&x,&y);}
	void prt(){printf("%d %d\n",x,y);}
};
ll cross(Vec a, Vec b, Vec c){return b-a&c-a;}

bool cmp2(Vec a, Vec b){
	if (a.id()^b.id()) return a.id()<b.id();
	return (a&b)>0;
}
int convex(vec *p, int n, vec *ans){
	sort(p,p+n);
	int m=0;
	for (int i=0;i<n;i++){
	    while (m>1 && cross(ans[m-2],ans[m-1],p[i])<=0) m--;
	    ans[m++]=p[i];
	}
	int k=m;
	for (int i=n-2;i>=0;i--){
	    while (m>k && cross(ans[m-2],ans[m-1],p[i])<=0) m--;
	    ans[m++]=p[i];
	}
	if (n>1) m--;
	return m;
}
vec p[2010],vp[2010],con[2010];

int iele[2010],rk[2010]; //i-th pos point, rank of i-th point

struct seg{
    vec v; short x, y;
    bool operator<(const seg &o) const{return cmp2(v,o.v);}
}lin[2010*2010];

bool cmp3(int x, int y){return p[x].y<p[y].y;}
int linc;

int main(){
    int n; cin>>n)
    inc(i,n) p[i].rd();
    int n1=convex(p,n,con);
    ll mim=9e18,mam=0;
    inc(i,n) iele[i]=i;
    sort(iele,iele+n,cmp3);
    linc=0;
    for (int i=0;i<n;i++) rk[iele[i]]=i;
    inc(i,n) inc(j,n) if (i^j) lin[linc++]={p[j]-p[i],i,j};
    sort(lin,lin+linc);
    inc(i,n){
        int d=0;        
        inc(j,n) if (i^j) vp[d++]=p[j]-p[i];
        sort(vp,vp+d,cmp2);
        vp[d]=vp[0]; vp[d+1]=vp[1];
        int down=0,up=0;
        inc(j,n1) {
            if ((con[j]-p[i]&vp[0])>(con[down]-p[i]&vp[0]))down=j;
            if (-(con[j]-p[i]&vp[0])>-(con[up]-p[i]&vp[0]))up=j;
        }
        inc(j,d) {
            while ((con[(down+1)%n1]-p[i]&vp[j])>(con[down]-p[i]&vp[j])) 
                down=(down+1)%n1;
            while (-(con[(up+1)%n1]-p[i]&vp[j])>-(con[up]-p[i]&vp[j])) 
                up=(up+1)%n1;
            if ((con[down]-p[i]&vp[j]) && (con[up]-p[i]&vp[j]))
            mam=max(mam,(con[down]-p[i]&vp[j])+(vp[j]&con[up]-p[i]));
        }
    }
    inc(i,linc){
        seg &cur=lin[i];
        int l=0,r=n-1;
        while (l<r){
            int mid=l+r>>1;
            if ((cur.v&p[iele[mid]]-p[cur.x])>0) r=mid;
            else l=mid+1;
        }
        ll s1=cur.v&p[iele[r]]-p[cur.x];
        l=0,r=n-1;
        while (l<r){
            int mid=l+r+1>>1;
            if ((cur.v&p[iele[mid]]-p[cur.x])<0) l=mid;
            else r=mid-1;
        }
        if (s1>0 && (p[iele[l]]-p[cur.x]&cur.v)>0)
        mim=min(mim,s1+(p[iele[l]]-p[cur.x]&cur.v));
        if (rk[cur.x]<rk[cur.y]){ //reorder after scannerline
            swap(rk[cur.x],rk[cur.y]);
            iele[rk[cur.x]]=cur.x;
            iele[rk[cur.y]]=cur.y;
        }
    }
    printf("%lld %lld\n",mim,mam);
    return 0;
}

