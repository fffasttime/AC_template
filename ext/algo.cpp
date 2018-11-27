

namespace PartialOrder_3D{
const int maxn=200010;
int ans[maxn],a1[maxn];

struct Node{
    int x,y,z,*sum;
    bool operator<(const Node &v) const{
        if (x==v.x) return y==v.y?z<v.z:y<v.y;
        return x<v.x;
    }
}a[maxn],b[maxn],c[maxn];

int tr[maxn];
int sum(int p){int ret=0; for(;p;p-=p&-p)ret+=tr[p]; return ret;}
void add(int p, int x){for(;p<maxn;p+=p&-p)tr[p]+=x;}

void cdq1(int l, int r){
    if (l==r-1) return;
    int mid=l+r>>1;
    cdq1(l,mid); cdq1(mid,r);
    for (int cl=l,cr=mid,cc=l;cc<r;cc++)
        if (cr>=r || cl<mid && a[cl].y<=a[cr].y)
            b[cc]=a[cl],add(b[cc].z,1),cl++;
        else
            b[cc]=a[cr],*b[cc].sum+=sum(b[cc].z),cr++;
    for (int i=l;i<mid;i++) add(a[i].z,-1);
    for (int i=l;i<r;i++) a[i]=b[i];
}

int main(){
    int n,k; cin>>n>>k;
    for (int i=0;i<n;i++)
        scanf("%d%d%d",&a[i].x,&a[i].y,&a[i].z),a[i].sum=ans+i;
    sort(a,a+n);
    for (int i=n-1;i;i--) if (a[i].x==a[i-1].x && a[i].y==a[i-1].y && a[i].z==a[i-1].z) *a[i-1].sum=*a[i].sum+1;
    cdq1(0,n);
    for (int i=0;i<n;i++) a1[ans[i]]++;
    for (int i=0;i<n;i++) printf("%d\n",a1[i]);
    return 0;
}
}

namespace DymanicInversedPair{
typedef long long ll;

const int maxn=200010;
ll ans[maxn]; int pos[maxn];

struct Node{
	int t,x,y;
	bool operator<(const Node &v) const{
		return t<v.t;
	}
}a[maxn],b[maxn];

int tr[maxn],n;
int sum(int p){int ret=0; for(;p;p-=p&-p)ret+=tr[p]; return ret;}
void add(int p, int x){for(;p<=n;p+=p&-p)tr[p]+=x;}

void cdq1(int l, int r){
	if (l==r-1) return;
	int mid=l+r>>1;
	cdq1(l,mid); cdq1(mid,r);
	for (int cl=l,cr=mid,cc=l;cc<r;cc++)
		if (cr>=r || cl<mid && a[cl].x<a[cr].x)
			b[cc]=a[cl],add(b[cc].y,1),cl++;
		else //upd sum of reversed pair that greater and left b[cc].t
			b[cc]=a[cr],ans[b[cc].t]+=sum(n)-sum(b[cc].y),cr++;
	for (int i=l;i<mid;i++) add(a[i].y,-1);
    for (int i=l;i<r;i++) a[i]=b[i];
    for (int i=r-1;i>=l;i--)
    	if (a[i].t<mid) add(a[i].y,1);
    	else ans[a[i].t]+=sum(a[i].y); //smaller and on right
    for (int i=l;i<r;i++) 
    	if (a[i].t<mid) add(a[i].y,-1);
}

int main(){
	int m,t0,p; cin>>n>>m; t0=n;
	for (int i=1;i<=n;i++){
		scanf("%d",&p);
		pos[p]=i; a[i]={0,i,p};
	}
	for (int i=1;i<=m;i++){
		scanf("%d",&p); 
		a[pos[p]].t=t0--;
	}
	for (int i=1;i<=n;i++) if (!a[i].t) a[i].t=t0--;
	sort(a+1,a+n+1);
	cdq1(1,n+1);
	for (int i=1;i<=n;i++) ans[i]+=ans[i-1];
	for (int i=n;i>n-m;i--) printf("%lld\n",ans[i]);
	return 0;
}
}

namespace sphi{
typedef long long ll;
const int maxn = 1700010;
int T, tot, prime[maxn], mu[maxn];
map<int, ll> ans_mu;

void sieve() {
    fill(prime, prime + maxn, 1);
    mu[1] = 1, tot = 0;
    for (int i = 2; i < maxn; i++) {
        if (prime[i]) {
            prime[++tot] = i, mu[i] = -1;
        }
        for (int j = 1; j <= tot && i * prime[j] < maxn; j++) {
            prime[i * prime[j]] = 0;
            if (i % prime[j] == 0) {
                mu[i * prime[j]] = 0; break;
            } else {
                mu[i * prime[j]] = -mu[i];
            }
        }
    }
    for (int i = 2; i < maxn; i++) mu[i] += mu[i - 1];
}

ll calc_mu(int x) {
    if (x < maxn) return mu[x];
    if (ans_mu.count(x)) return ans_mu[x];
    ll ans = 1;
    for (ll i = 2, j; i <= x; i = j + 1) {
        j = x / (x / i), ans -= (j - i + 1) * calc_mu(x / i);
    }
    return ans_mu[x] = ans;
}

ll calc_phi(int x) {
    ll ans = 0;
    for (ll i = 1, j; i <= x; i = j + 1) {
        j = x / (x / i), ans += (x / i) * (x / i) * (calc_mu(j) - calc_mu(i - 1));
    }
    return ((ans - 1) >> 1) + 1;
}

int main() {
    sieve();
    scanf("%d", &T);
    for (int i = 1, n; i <= T; i++) {
        scanf("%d", &n);
        printf("%lld %lld\n", calc_phi(n), calc_mu(n));
    }
    return 0;
}
}
