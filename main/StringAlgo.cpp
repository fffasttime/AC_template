#include "base.cpp"

namespace StringHash{
//double module hash
typedef unsigned long long ll;
const ll m1=1000000007;
const int maxn=1000010;
ll h1[maxn],h2[maxn],b1[maxn],b2[maxn];
void pre(){
	b1[0]=b2[0]=1;
	inc(i,maxn-1)
		b1[i+1]=b1[i]*131%m1,
		b2[i+1]=b2[i]*137;
}
void gethash(char *s, int l){
	h1[l]=h2[l]=0;
	dec(i,l){
		h1[i]=(h1[i+1]*131+s[i])%m1;
		h2[i]=h2[i+1]*137+s[i];
		//cout<<h1[i]<<' '<<b1[i]<<'\n';
	}
}
//get substring [l,r) hash value
pair<ll,ll> substr(int l, int r){
	ll r1=h1[l]+m1-h1[r]*b1[r-l]%m1; if (r1>=m1) r1-=m1;
	ll r2=h2[l]-h2[r]*b2[r-l];
	return {r1,r2};
}
}

namespace KMP{
const int maxn=1000010;

int kmp[maxn];
//s is a short partten string
char s[maxn]; int sl; 
void getkmp(){
	int j=0,k=-1;
	kmp[0]=-1;
	while (j<sl)
		if (k==-1 || s[j]==s[k])
			kmp[++j]=++k;
		else
			k=kmp[k];
}
int kmp_idx(char *t, int tl){
	int i=0, j=0;
	while (i<sl && j<tl)
		if (i==-1 || s[i]==t[j])
			i++,j++;
		else
			i=kmp[i];
	if (i==sl) return j-sl;
	else return -1;
}
int kmp_cnt(char *t, int tl){
	int i=0, j=0, cnt=0;
	while (j<tl){
		if (i==-1 || s[i]==t[j])
			i++,j++;
		else
			i=kmp[i];
		if (i==sl) cnt++;
	}
	return cnt;
}
}
//!-- untested
//extend KMP
//extend[i]: LCP lenth between s1[i..l1] and s2
namespace E_KMP{
const int N=100010;
int next[N],extend[N];
void getnext(char *str){
    int i=0,j,po,len=strlen(str);
    next[0]=len;
    while(str[i]==str[i+1] && i+1<len) i++; next[1]=i; //calc next[1]
    po=1;
    for(i=2;i<len;i++)
        if(next[i-po]+i < next[po]+po)
            next[i]=next[i-po];
        else{
            j = next[po]+po-i;
            if(j<0) j=0;
            while(i+j<len && str[j]==str[j+i]) j++; next[i]=j;
            po=i;
        }
}
void exkmp(char *s1,char *s2){
    int i=0,j,po,len=strlen(s1),l2=strlen(s2);
    getnext(s2);
    while(s1[i]==s2[i] && i<l2 && i<len) i++; extend[0]=i;
    po=0;
    for(i=1;i<len;i++)
        if(next[i-po]+i < extend[po]+po)
            extend[i]=next[i-po];
        else //continue try match after e[po]+po
        {
            j = extend[po]+po-i;
            if(j<0) j=0;
            while(i+j<len && j<l2 && s1[j+i]==s2[j]) j++; extend[i]=j;
            po=i; //update po
        }
}
}

namespace ACAM{
const int maxn=100000,alpha=26; //maxn >= sigma len(si)
int ch[maxn][alpha],val[maxn],fail[maxn],lbl[maxn],len[maxn],pc=0;
int cnt[1000]; //str appear times, first element is 1
int strc=0;
void clear(){
	pc=0; strc=0;
	memset(ch,0,sizeof(ch));
	memset(fail,0,sizeof(fail));
	memset(val,0,sizeof(val));
	memset(lbl,0,sizeof(lbl));
}
//Trie construct
void ins(char *s){
	int l=strlen(s), cur=0;
	for (int i=0;i<l;i++){
		int v=s[i]-'a';
		if (!ch[cur][v]) ch[cur][v]=++pc;
		cur=ch[cur][v];
		len[cur]=i+1;
	}
	strc++;
	lbl[cur]=strc;
	val[cur]++;
}
int qu[maxn];
//fail edge add
void build(){
	int qh=0,qt=0;
	for (int i=0;i<alpha;i++)
		if (ch[0][i]) fail[ch[0][i]]=0,qu[qt++]=ch[0][i];
	while (qh<qt){
		int u=qu[qh];qh++;
		for (int i=0;i<alpha;i++)
			if (ch[u][i])
				fail[ch[u][i]]=ch[fail[u]][i],qu[qt++]=ch[u][i];
			else
				ch[u][i]=ch[fail[u]][i]; //opt, move to fail auto. Attention: the multi fail jump will be emitted
	}
}
//count how many mode str appeared in s as substr
int appear(char *s){
	int l=strlen(s),cur=0,ans=0;
	for (int i=0;i<l;i++){
		cur=ch[cur][s[i]-'a']; //the opt trans emitted fail jump chain, do it when necessary
		for (int t=cur;t && ~val[t];t=fail[t]) //the label be sure O(n)
			ans+=val[t],val[t]=-1;
	}
	return ans;
}
//count each mode str in s
//[!] worst O(n^2), a better way is dp on fail tree
void cntall(char *s){
	int l=strlen(s),cur=0;
	memset(cnt,0,sizeof(cnt));
	for (int i=0;i<l;i++){
		cur=ch[cur][s[i]-'a']; //the opt trans emitted fail jump chain, do it when necessary
		for (int t=cur;t;t=fail[t])
			cnt[lbl[t]]++;
	}
}
}

namespace SA{
//sa: pos of ith rk suf, rk: rk of i pos suf, a: s0-'a'
//t1,t2,c: temp array, h: height(LCP of sa[i] and sa[i-1])
int t1[N],t2[N],sa[N],h[N],rk[N],c[N],a[N];
int n,m;
void calcsa(){
	int *x=t1,*y=t2,p=0,f=0;
	icc(i,m) c[i]=0;        
	icc(i,n) c[x[i]=a[i]]++;  //first char sort
	icc(i,m) c[i]+=c[i-1];
	dcc(i,n) sa[c[x[i]]--]=i; //pos of ith first char
	for (int i=1;i<=n && p<=n;i<<=1){
		p=0;
		rpp(j,n-i+1,n) y[++p]=j;  //remain part
		icc(j,n) if (sa[j]>i) y[++p]=sa[j]-i; //main part
		icc(j,m) c[j]=0;
		icc(j,n) c[x[y[j]]]++;
		icc(i,m) c[i]+=c[i-1];
		dcc(j,n) sa[c[x[y[j]]]--]=y[j]; //sort, use dcc because sort should be stable
		swap(x,y);x[sa[1]]=p=1; 
		rpp(j,2,n) x[sa[j]]=y[sa[j]]==y[sa[j-1]]&&y[sa[j]+i]==y[sa[j-1]+i]?p:++p; //refill key
		m=p;
	}
	icc(i,n) rk[sa[i]]=i;
	icc(i,n){ //get height, O(n)
		int j=sa[rk[i]-1];
		if (f) f--; while (a[i+f]==a[j+f]) f++;
		h[rk[i]]=f;
	}
}

char s0[N];
int main(){
	scanf("%s",s0); int l=strlen(s0);
	inc(i,l) a[++n]=s0[i]-' ';
	m=200;
	calcsa();
	icc(i,n) printf("%d ",sa[i]);
	return 0;
}
}

namespace SAM{
const int maxn=100010,alpha=26;

//max state cnt: 2*strlen-1
//max transfer cnt: 3*strlen-4
struct Node{
	int l,num; bool vis;
	Node *p, *tr[alpha];
	//vector<Node *> ch;
	void set(int _l){l=_l;memset(tr,0,sizeof(tr));p=0;num=1;vis=0;/*ch.clear();*/}
}nodes[maxn<<1];
int nodec;
Node *root;
Node *open(int l){
	nodes[nodec++].set(l);
	return nodes+nodec-1;
}
void build(char *s, int l){
	Node *cur;
	cur=root=open(0);
	for (int i=0;i<l;i++){
		int x=s[i]-'a';
		Node *p=cur;
		cur=open(i+1);
		for (;p && !p->tr[x];p=p->p)
			p->tr[x]=cur;
		if (!p) cur->p=root;
		else{
			Node *q=p->tr[x];
			if (p->l+1==q->l) cur->p=q;
			else{
				Node *r=open(-1); r[0]=q[0]; r->l=p->l+1;
				q->p=r; cur->p=r; r->num=0;
				for (;p && p->tr[x]==q;p=p->p) p->tr[x]=r;
			}
		}
	}
}
//get substr last position
int pos(Node *u, char *s){
	if (*s==0) return u->l;
	if (!u->tr[*s-'a']) return -1;
	return pos(u->tr[*s-'a'],s+1);
}

int t[maxn],r[maxn]; //t:temp, r:rank(ith element pos)
//init |right(s)| before cnt
void initnum(int s0l){
	rep(i,0,s0l+1) t[i]=0;
	inc(i,nodec) t[nodes[i].l]++;
	rep(i,1,s0l+1) t[i]+=t[i-1];
	inc(i,nodec) r[--t[nodes[i].l]]=i; //sort by count
	per(i,nodec,1) nodes[r[i]].p->num+=nodes[r[i]].num; //dp
}
//count substr
int cnt(Node *u, char *s){
	if (*s==0) return u->num;
	if (!u->tr[*s-'a']) return 0;
	return cnt(u->tr[*s-'a'],s+1);
}
// longest substring
int lcs(char *x1){
	int lcs=0, ans=0, xl=strlen(x1);
	Node *p=root;
	inc(i,xl){
		int x=x1[i]-'a';
		if (p->tr[x]){
			lcs++;
			p=p->tr[x];
			ans=max(ans,lcs);
			continue;
		}
		for (;p && !p->tr[x];p=p->p);
		if (!p) p=root,lcs=0;
		else{
			lcs=p->l+1;
			p=p->tr[x];
		}
		ans=max(ans,lcs);
	}
	return ans;
}
}

//mulit-str SAM
namespace GSAM{
const int maxn=200010;
struct Node{
	int l, num, las, vis;
	Node *p;
	map<int,Node*> tr; //more time, less memory
	//int tr[26];
}nodes[maxn<<1];
int nodec;
Node *open(int l){
	nodes[nodec++].l=l;
	return nodes+nodec-1;
}
Node *root=open(0);
void build(int *s, int l){
	Node *cur=root;
	for (int i=0;i<l;i++){
		int x=s[i];
		if (cur->tr.count(x)){  //transfer existed
			cur=cur->tr[x];
			continue;
		}
		Node *p=cur;
		cur=open(i+1);
		for (;p && !p->tr.count(x);p=p->p)
			p->tr[x]=cur;
		if (!p) cur->p=root;
		else{
			Node *q=p->tr[x];
			if (p->l+1==q->l) cur->p=q;
			else{
				Node *r=open(-1); r[0]=q[0]; r->l=p->l+1;
				q->p=r; cur->p=r; r->num=0;
				for (;p && p->tr[x]==q;p=p->p) p->tr[x]=r;
			}
		}
	}
}
int len[200010],tot;
vector<int> str[200010];
int ts[200010];
int ans[200010];
//calc how many mode str appear in each query
void upd1(Node *u, int col){ 
	for (;u->las!=col && u!=root;u=u->p)
		u->las=col, u->num++;
}
//calc ecah mode str appear how many query
void upd2(Node *u, int col){ 
	for (;u->las!=col && u!=root;u=u->p)
		u->las=col,ans[col]+=u->vis;
}
//n: ptn str, m: query str
int main(){
	int n,m; cin>>n>>m;
	for (int i=0;i<n;i++){
		++tot;
		scanf("%d", len+tot);
		for (int j=0;j<len[tot];j++){
			scanf("%d",ts+j);
			str[tot].push_back(ts[j]);
		}
		build(ts,len[tot]);
	}
	for (int i=1;i<=tot;i++){
		Node *cur=root;
		for (int j=0;j<len[i];j++)
			cur=cur->tr[str[i][j]],
			upd1(cur,i);
	}
	for (int i=0;i<m;i++){
		int l,x; bool flag=1;
		scanf("%d",&l);
		Node *cur=root;
		for (int j=0;j<l;j++){
			scanf("%d",&x);
			if (flag)
				if (cur->tr.count(x))
					cur=cur->tr[x];
				else //no transfer
					flag=0;
		}
		if (flag)
			printf("%d\n",cur->num),
			cur->vis++;
		else
			printf("0\n");
	}
	for (int i=0;i<nodec;i++) nodes[i].las=0; //!-- clear
	for (int i=1;i<=tot;i++){
		Node *cur=root;
		for (int j=0;j<len[i];j++)
			cur=cur->tr[str[i][j]],
			upd2(cur,i);
	}
	for (int i=1;i<=tot;i++)
		printf("%d ",ans[i]);
	return 0;
}
}

namespace Manacher{
const int maxn=10000000;
//p[]: max palindrome len at pos i
int p[maxn<<1];char s[maxn<<1],s0[maxn];
int sl,s0l;
int manacher(){
    s0l=strlen(s0);
    sl=1; s[0]='$'; s[1]='#';
    inc(i,s0l) s[++sl]=s0[i],s[++sl]='#';
    s[++sl]=0;
    int mx=0,mi=0,ans=0; //mx: max cur pstr right pos, mi: max cur pstr center pos
    rep(i,1,sl){
        p[i]=i<mx?min(p[mi*2-i], mx-i):1;
        while (s[i-p[i]]==s[i+p[i]]) p[i]++;
        if (mx<i+p[i]) mi=i,mx=i+p[i];
        ans=max(ans,p[i]-1);
    }
    return ans;
}
}

namespace PAM{
const int maxn=2000500;

//ch[x]: if cur pstr is a, the ch is xax.  len: len of cur pstr
//fail: longest pstr suffix of cur point.  cnt: count of this pstr.
struct Node{
    int ch[10],fail,len;
	int cnt;
}node[maxn];
int nodec,cur, len[maxn];
char s[maxn];

void pre(){
    node[0].fail=1; node[1].len=-1;
    nodec=2;cur=0;
}
void insert(int p){
    int j, x=s[p]-'0';
    while(s[p-node[cur].len-1]!=s[p])cur=node[cur].fail; //find ch
    if(!node[cur].ch[x]){
        node[nodec].len=node[cur].len+2;
        j=node[cur].fail;
        while(s[p-node[j].len-1]!=s[p])j=node[j].fail; //find fail
        node[nodec].fail=node[j].ch[x];
        node[cur].ch[x]=nodec;
        cur=nodec;
		nodec++;
    }
    else cur=node[cur].ch[x];
    len[p]=node[cur].len;
	node[cur].cnt++;
}
char ts[maxn];
void dfs1(int u, int deep){
	cout<<ts<<' '<<node[u].len<<'\n'; //cur node
	for (int i=0;i<10;i++)
		if (node[u].ch[i]){
			ts[deep]=i+'0';
			dfs1(node[u].ch[i],deep+1);
		}
}
int main(){
	pre();
	scanf("%s",s); int l=strlen(s);
	for (int i=0;i<l;i++) insert(i);
	for (int i=nodec-1;i>0;i--) 
		node[node[i].fail].cnt+=node[i].cnt;
	dfs1(0,0); //even pstr
	dfs1(1,0); //odd pstr
	return 0;
}
}

