#include<iostream>
#include<cstdio>
#include<algorithm>
#include<cstring>
#include<cmath>
using namespace std;
typedef long long ll;
ll ans=0,n2;
void chk(ll d){
    ll s=n2/d,j;
    for(ll i=1;i*i<=s;++i){
        j=sqrt(s-i*i);
        if(i>=j) break; //i<j
        if (i*i+j*j==s && __gcd(i,j)==1){
        	ll y=d*(j*j-i*i)/2, x=sqrt(n2*n2/4-y*y);
        	cout<<x<<' '<<y<<'\n'; //x*x+y*y==n*n
        	ans++;
		}
    }
}
//solution of x*x+y*y=n*n, O(sqrt(n))
int main(){
	ll n;
    cin>>n;  n2=n<<1;
    for(ll i=1;i*i<=n2;++i)if(!(n2%i)){
        chk(i);
        if(i*i!=n2) chk(n2/i);
    }
    cout<<ans*4+4<<'\n'; //add (0,r)
    return 0;
}
