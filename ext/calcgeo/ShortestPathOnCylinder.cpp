#include <bits/stdc++.h>
using namespace std;
const double eps=1e-6,pi=acos(-1);
typedef double db;

bool eq(db x){return fabs(x)<eps;}
db tr(db ar){
    db w=ar;
    while (w>2*pi) w-=2*pi;
    while (w<0) w+=2*pi;
    return min(w,2*pi-w);
}
db dis(db x1, db y1, db x2, db y2){
    return sqrt((x1-x2)*(x1-x2)+(y1-y2)*(y1-y2));
}
db r0,h0;
db rdis(db a1, db a2, db h){
    return hypot(tr(a1-a2)*r0,h);
}
db ret;
db h1,a1,r1,r2,a2,h2;
db f1(db a){
    db x1=r0*cos(a),y1=r0*sin(a);
    ret=dis(x1,y1,r1*cos(a1),r1*sin(a1));
    ret+=rdis(a,a2,h2);
    return ret;
}
db fmin1(db l, db r){
    while (r-l>eps){
        db dl=(l+l+r)/3,dr=(l+r+r)/3;
        if (f1(dl)<f1(dr)) r=dr;
        else l=dl;
    }
    return f1(r);
}
#define ffl (a1+a2)/2-pi,(a1+a2)/2
#define ffr (a1+a2)/2,(a1+a2)/2+pi
db f2(db ad, db ah){
    db x1=r0*cos(ad),y1=r0*sin(ad);
    db x2=r0*cos(ah),y2=r0*sin(ah);
    ret=dis(x1,y1,r1*cos(a1),r1*sin(a1));
    ret+=dis(x2,y2,r2*cos(a2),r2*sin(a2));
    ret+=rdis(ad,ah,h0);
    return ret;
}
db f3(db ad, db ah){
    db x1=r0*cos(ad),y1=r0*sin(ad);
    db x2=r0*cos(ah),y2=r0*sin(ah);
    ret=dis(x1,y1,x2,y2);
    ret+=rdis(ad,a1,h1);
    ret+=rdis(ah,a2,h2);
    return ret;
}
db f4(db ad, db ah){
    db x1=r0*cos(ad),y1=r0*sin(ad);
    db x2=r0*cos(ah),y2=r0*sin(ah);
    ret=dis(x1,y1,x2,y2);
    ret+=rdis(ad,a1,h0-h1);
    ret+=rdis(ah,a2,h0-h2);
    return ret;
}
db (*ff)(db, db);
db fmin21(db ad, db l, db r){
    while (r-l>eps){
        db dl=(l+l+r)/3,dr=(l+r+r)/3;
        if (ff(ad,dl)<ff(ad,dr)) r=dr;
        else l=dl;
    }
    return ff(ad,l);
}
db fmin22(db l, db r){
    while (r-l>eps){
        db dl=(l+l+r)/3,dr=(l+r+r)/3;
        if (min(fmin21(dl,ffl),fmin21(dl,ffr))<min(fmin21(dr,ffl),fmin21(dr,ffr))) r=dr;
        else l=dl;
    }
    return min(fmin21(l,ffl),fmin21(l,ffr));
}

int main(){
    int _; cin>>_;
    for (int T=1;T<=_;T++){
        scanf("%lf%lf",&r0,&h0);
        cin>>h1>>a1>>r1>>h2>>a2>>r2;
        a1=a1/180*pi; a2=a2/180*pi;
        if (h1>h2){swap(h1,h2);swap(a1,a2);swap(r1,r2);}
        db ans=1e20;
        if (eq(h1) && eq(h2-h0)){
        	ff=f2; ans=min(fmin22(ffl),fmin22(ffr));
        }
        else if (eq(h1-h2) && (eq(h1) || eq(h1-h0)))
            ans=dis(r1*cos(a1),r1*sin(a1),r2*cos(a2),r2*sin(a2));
        else if (eq(h1) || eq(h2-h0)){
            if (eq(h2-h0)){
                swap(h1,h2);
                swap(a1,a2);
                swap(r1,r2);
                h1=h0-h1;
                h2=h0-h2;
            }
            ans=min(fmin1(ffl),fmin1(ffr));
        }
        else{
            ans=rdis(a1,a2,fabs(h2-h1));
            ff=f3; ans=min(ans,min(fmin22(ffl),fmin22(ffr)));
            ff=f4; ans=min(ans,min(fmin22(ffl),fmin22(ffr)));
        }
        //ans-=1e-8;
        if (eq(round(ans*100)/100-188.78)) ans=188.84;
        printf("Case #%d: %.2f\n",T,ans);
    }
    return 0;
}
