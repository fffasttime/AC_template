#include "base.cpp"

namespace DateTime{

int gettime(int h, int m, int s){
	return h*3600+m*60+s;
}

bool isleapyear(int y){
	//if (y<0) return isleapyear(-y-1);
	//if (y%3200==0) return y%172800==0; 
	return y%4==0 && y%100 || y%400==0;
}

int mm[13]={0,31,28,31,30,31,30,31,31,30,31,30,31};
//get day diff from 0000/01/01 (BC 0001y), but require y>0
int getday(int y, int m, int d){
	if (m<3) y--,m+=12;
	return (d+30*m+3*(m+1)/5+y*365+y/4-y/100+y/400)-33;
}
//inverse function of getday()
void getdate(int d0, int &y, int &m, int &d){
	int y1=(d0)/146097;
	int y2=(d0-1-y1*146097)/36524;
	int y3=(d0-1-y1*146097-y2*36524)/1461;
	y=y1*400+y2*100+y3*4+(d0-1-y1*146097-y2*36524-y3*1461)/365;
	d=d0-y*365-(y-1)/4+(y-1)/100-(y-1)/400; m=1;
	if (y%4==0&&y%100||y%400==0) mm[2]++;
	while (d-mm[m]>0) d-=mm[m++];
	if (y%4==0&&y%100||y%400==0) mm[2]--;
}

//get week by date,1 for Monday
//[!] Because 1582/10/05~1582/10/14 is not existed
// the formula is correct after that day
int getweek(int y, int m, int d){
	if (m<3) y--,m+=12;
	return (d+2*m+3*(m+1)/5+y+y/4-y/100+y/400+1)%7;
}

}
