#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <set>
#include <map>
#include <regex>
using namespace std;

struct Token{
	enum TokenType{
		INT,
		FLOAT,
		STRING,
		KEYWORD,
		NAME,
		OPERATOR,
		LBRACE,
		RBRACE
	};
	TokenType type;
	string value;
	Token(TokenType type, string value):type(type), value(value){}
	void debug(){cout<<value<<' '<<type<<'\n';}
};

const set<string> KEYWORDS={"if","else","while","for"};


bool isopchar(char c){
	switch (c){
		case '+': case '-': case '*': case '/':
		case '%': case '<': case '>': case ':':
		case ',': case '.': case '=': case '|':
		case '^': case '&': case '!': case '@':
		case ';':
		return true;
	}
	return false;
}

vector<Token> token;
//lexer
void gettokens(const string &s){
	stringstream ss(string(" ")+s+" ");
#define PUSH(TYPE) token.emplace_back(Token:: TYPE , res)
	while (!ss.eof()){
		if (isspace(ss.peek())){
			ss.get();
			continue;
		}
		char ch=ss.peek();
		ostringstream os; //result str
		//number, integer or float
		if (isdigit(ch)){
			int dot=0;
			while (isdigit(ch) || ch=='.' || isdigit(ch)){
				os<<ch; ss.get();
				if (ch=='.') dot++;
				ch=ss.peek();
			}
			auto res=os.str();
			if (dot) PUSH(FLOAT);
			else PUSH(INT);
		}
		else if (isalpha(ch) || ch=='_'){
			while (isalpha(ch) || ch=='_'){
				os<<ch; ss.get();
				ch=ss.peek();
			}
			auto res=os.str();
			if (KEYWORDS.count(res)) PUSH(KEYWORD);
			else PUSH(NAME);
		}
		else if (isopchar(ch)){
			while (isopchar(ch)){
				os<<ch; ss.get();
				ch=ss.peek();
			}
			auto res=os.str();
			PUSH(OPERATOR);
		}
		else if (ch=='\"' || ch=='\''){
			char st=ch;
			ss.get(); ch=ss.peek();
			bool flag=0; // emit \" 
			while (ch!=st || flag){
				os<<ch;
				//TODO : transfer meaning
				if (!flag && ch=='\\'){
					flag=1;
				}
				else flag=0;
				ss.get();
				ch=ss.peek();
			}
			ss.get();
			auto res=os.str();
			PUSH(STRING);
		}
		else if (ch=='{' || ch=='('){
			os<<ch;
			auto res=os.str();
			ss.get();
			PUSH(LBRACE);
		}
		else if (ch=='}' || ch==')'){
			os<<ch;
			auto res=os.str();
			ss.get();
			PUSH(RBRACE);
		}
		else{
			if (ch==EOF) break; 
			cout<<"ERROR unknown char "<<ch<<'\n';
			ss.get();
		}
	}
#undef PUSH
}

string preprocess(const string &s){
	istringstream ss(string(" ")+s+" ");
	ostringstream result;
	while (!ss.eof()){
		char ch=ss.peek();
		if (ch=='\"' || ch=='\''){
			char st=ch; result<<ch;
			ss.get(); ch=ss.peek();
			bool flag=0; // emit \" 
			while (ch!=st || flag){
				result<<ch;
				if (!flag && ch=='\\') flag=1;
				else flag=0;
				ss.get();
				ch=ss.peek();
			}
			result<<ch;
			ss.get();
		}
		else if (ch=='/'){
			ss.get();
			if (ss.peek()=='*'){
				ss.get();
				while (1){
					ch=ss.peek();
					if (ch=='*'){
						ss.get();
						if (ss.peek()=='/')
							break;
					}
					else ss.get();
				}
				ss.get();
				if (!isspace(ss.peek())) result<<' ';
			}
			else if(ss.peek()=='/'){
				while (ss.peek()!='\n')
					ss.get();
			}
			else
				result<<'/';
		}
		else{
			result<<ch;
			ss.get();
		}
	}
	return result.str();
}

int main(){
	string s,ts;
	cin>>s; //preproce
	/*adfasdf*/
	"//safadf";
	while (getline(cin,ts)){
		s+=ts+"\n";
	}s=preprocess(s);
	cout<<s<<'\n';
	
	gettokens(s);
	for (auto &tk:token)
		tk.debug();
	return 0;
}

