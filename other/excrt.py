n,m=map(int,input().split())
a=[]
p=[]
 
def exgcd(a,b):
    if b==0:
        return a,1,0
    t,y,x=exgcd(b,a%b)
    y-=a//b*x
    return t,x,y
 
def china():
    n1=p[0]
    a1=a[0]
    for i in range(1,n):
        n2=p[i]
        a2=a[i]
        c=(a2-a1%n2+n2)%n2
        gcd,k1,k2=exgcd(n1,n2)
        if (c%gcd):
            return -1
        t=n2//gcd
        K=c//gcd*k1%t
        a1+=n1*K
        n1*=t
        a1=(a1+n1)%n1
    return a1
 
for i in range(n):
    x,y=map(int,input().split())
    p.append(x)
    a.append(y)
ret=china()
if (ret>m):
    print("he was probably lying")
elif (ret==-1):
    print("he was definitely lying")
else:
    print(ret)
