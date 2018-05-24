#include <bits/stdc++.h>
using namespace std;
typedef long long ll;

ll in()
{
	int x=0,f=1,c=getchar();
	while (!isdigit(c) && c!='-') c=getchar();
	if (c=='-') f=-1,c=getchar();
	while (isdigit(c)) x=x*10+c-'0', c=getchar();
	return x*f;
}

#define MAXN 100010

ll sum[MAXN<<2],tadd[MAXN<<2],tmul[MAXN<<2],a[MAXN];
ll n,m,p;

void build(int u,int l, int r)
{
	tmul[u]=1;
	if (l==r-1)
	{
		sum[u]=a[l];
		return;
	}
	int mid=(l+r)/2;
	build(u+u+1,l,mid);
	build(u+u+2,mid,r);
	sum[u]=(sum[u+u+1]+sum[u+u+2])%p;
}

void upd(int u, int l, int r)
{
	int lc=u+u+1,rc=u+u+2,mid=(l+r)/2;
	sum[lc]*=tmul[u]; sum[lc]+=(mid-l)*tadd[u]; sum[lc]%=p;
	sum[rc]*=tmul[u]; sum[rc]+=(r-mid)*tadd[u]; sum[rc]%=p;
	
	tadd[lc]*=tmul[u]; tadd[lc]+=tadd[u]; tadd[lc]%=p;
	tmul[lc]*=tmul[u]; tmul[lc]%=p;
	tadd[rc]*=tmul[u]; tadd[rc]+=tadd[u]; tadd[rc]%=p;
	tmul[rc]*=tmul[u]; tmul[rc]%=p;
	
	tadd[u]=0; tmul[u]=1;
}

void add(int u, int l, int r, int cl, int cr, ll c)
{
	if (cl<=l && cr>=r)
	{
		tadd[u]+=c; tadd[u]%=p;
		sum[u]+=c*(r-l)%p; sum[u]%=p;
		return;
	}
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=(l+r)/2;
	if (cl<mid) add(u+u+1,l,mid,cl,cr,c);
	if (cr>mid) add(u+u+2,mid,r,cl,cr,c);
	sum[u]=(sum[u+u+1]+sum[u+u+2])%p;
}

void mul(int u, int l, int r, int cl, int cr, ll c)
{
	if (cl<=l && cr>=r)
	{
		tadd[u]*=c; tadd[u]%=p;
		tmul[u]*=c; tmul[u]%=p;
		sum[u]*=c; sum[u]%=p;
		return;
	}
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=(l+r)/2;
	if (cl<mid) mul(u+u+1,l,mid,cl,cr,c);
	if (cr>mid) mul(u+u+2,mid,r,cl,cr,c);
	sum[u]=(sum[u+u+1]+sum[u+u+2])%p;
}

ll qu(int u, int l, int r, int cl, int cr)
{
	if (cl<=l && cr>=r)
		return sum[u];
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=(l+r)/2;
	ll ret=0;
	if (cl<mid) ret+=qu(u+u+1,l,mid,cl,cr);
	if (cr>mid) ret+=qu(u+u+2,mid,r,cl,cr);
	return ret%p;
}

int main()
{
	n=in(),m=in(),p=in();
	for (int i=0;i<n;i++)
		a[i]=in();
	build(0,0,n);
	for (int i=0;i<m;i++)
	{
		int c=in();
		int x,y; ll k; x=in(),y=in();
		x--;
		if (c==1)
		{
			k=in();
			mul(0,0,n,x,y,k);
		}
		else if (c==2)
		{
			k=in();
			add(0,0,n,x,y,k);
		}
		else
		{
			cout<<qu(0,0,n,x,y)<<'\n';
		}
	}
	return 0;
}

