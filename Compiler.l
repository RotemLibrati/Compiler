%%
%{
/*
alternative comment catcher

"/%"([^%]|%+[^%/])*%+"/"

*/
%}
"/%" {	char c, c1;
	c=input();
	while(1){
		if(c=='\n') yylineno++;
		c1=input();
		if(c=='%' && c1=='/')	break;
		c=c1;
	} ;
};
"\'"(" "|[!@\#$%&\(\)_\-+*/^=\.,;]|[a-zA-Z]|[0-9])"\'" {yylval.string=strdup(yytext); return charlitT;};
"\""(" "|[!@\#$%&\(\)_\-+*/^=\.,;]|[a-zA-Z]|[0-9])*"\"" {yylval.string=strdup(yytext); return strlitT;};
[ \t] ;
\n yylineno++;
bool return boolT;
char return charT;
int return intT;
real return realT;
string return strT;
int"*" return intpT;
char"*" return charpT;
real"*" return realpT;
if return ifT;
else return elseT;
while return whileT;
var return varT;
func return funcT;
proc return procT;
return return returnT;
null return nullT;
"&&" return andT;
"==" return eqT;
">=" return gteqT;
"<=" return lteqT;
"!=" return neqT;
"\|\|" return orT;
"true" return trueT;
"false" return falseT;
[1-9][0-9]*|[0] {yylval.number=atoi(yytext); return numT;};
[0][xX][0-9a-fA-F]+ {yylval.number=strtoul(yytext, NULL, 0); return numT;};
([0-9]+([.][0-9]*)?([eE][+-]?[0-9]+)?|[.][0-9]+([eE][+-]?[0-9]+)?) {yylval.string=strdup(yytext); return realnumT;};
[a-zA-Z][_a-zA-Z0-9]* {yylval.string=strdup(yytext); return idT;};
. return yytext[0];
%%