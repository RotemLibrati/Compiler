%{
#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#include<stdbool.h>
int counter = 0;
int scopeCounter = 0;
int labelCounter = 0;
int varCounter = 0;
int varsFinderCounter = -1;
typedef struct node
{
	char *token;
	struct node *left;
	struct node *right;
	char *startLabel;
	char *falseLabel;
	char *nextLabel;
	char *endLabel;
	char *var;
	int endFunc;
	int varsSize;
} node;
typedef struct node2
{
	struct node *original;
	struct node *clean;
} node2;
typedef struct idLinkedList
{
	char *key;
	char *type;
	int size;
	char *returnType;
	struct idLinkedList *args;
	struct idLinkedList *next;
	struct scopeLinkedList *nextscope;
} idLinkedList;
typedef struct scopeLinkedList
{
	struct idLinkedList *id;
	struct scopeLinkedList *parent;
} scopeLinkedList;
node* finalOriginalTree;
scopeLinkedList stackMemScope = {.id=NULL, .parent=NULL};
scopeLinkedList *highestScope = &stackMemScope;
scopeLinkedList *firstScope = &stackMemScope;
idLinkedList *tempArgs;
idLinkedList *currentCallable;
bool currentArgs = 0;
bool Args = false;
bool Main = false;
bool isReal = false;
bool condition = false;
int cond = 0;
void removeLastScope();
void addNewScope();
int checkIfIdExistAtCurrentScope(char *name);
int checkIfVarExistAtCurrentScope(char *name);
int checkIdList(char arr[10][10],char *list);
int getNumFromStrType(char *strType);
int typeIsString(char *type);
idLinkedList * declareId(char* name,char* type);
idLinkedList *getIdLink(char* name, char* type);
char* stringMissingArgs(idLinkedList *firstMissingArg);
void callableExistsOrExit(char* callableName);
void addTempArgs(idLinkedList* link);
int find(scopeLinkedList *tree,char *name, char *type);
node *mknode(char *token,node *left,node *right);
void printtree(node *tree);
void printtreeAll(node *tree);
void printtabs();
//void printscopes(scopeLinkedList *tree);
void printcurrentscope(idLinkedList *tree);
node* getFirstNonKeywordNode(node* tree);
node* getLastNonKeywordNode(node *tree);
int getSizeOfCallableVars(char* callable, node *tree);
node* getMinimalTree(node *left,node *right);
%}
%union
{
	int number;
	float realnum;
	char *string;
	node2 *tree;
}
%token <string> idT strlitT charlitT realnumT
%token <number> numT boolT charT intT realT strT intpT charpT realpT ifT elseT whileT varT funcT procT returnT nullT eqT gteqT lteqT neqT trueT falseT
//%token <realnum> realnumT
%start S
%type <tree> S CODE ASN EXP COND TOTALBLOCK BLOCK SUBBLOCK ST PROCC UPPERARGS ARGS ARGSET UPPERBODY BODY /*SUBBODY*/ FUNCC FUPPERBODY UPDEC DECLARATIONS DECBODYORDEC LBRACE RBRACE FUNCORPROCCALL EXPORANYVAL CONDITION SIMPLE SCOND ACOND INNERBODY VARDECLARE
%type <string> AOP COMP /*IDORNUM*/ IDLIST TYPE PROCORFUNC /*NUMORIDLIST UPPERLIST*/ ANYVAL NOT CALLARG CALLARGLIST
%left andT orT '+' '-'
%left '*' '/'
%%
S: CODE {
	if(Main){
		$$=$1;finalOriginalTree=$$->original;
		//printtree($$->original);
		//printscopes(firstScope);
		labelNodes($$->clean);
		genCode($$->clean);//printtreeAll($$->clean);
	}
	else {
	printf("ERROR!(line %d) Main Procedure Must Be Declared\n",yylineno);
	}
};

CODE: PROCC {$$=$1;}
	| FUNCC {$$=$1;}
	| CODE PROCC {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;}

	| CODE FUNCC {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;};

PROCC: PROCORFUNC '(' UPPERARGS ')' '{' UPPERBODY '}' {
	char *a=strdup($1);
	//char *b=strdup("Proc");
	if (!strcmp(a, "Main")) { 
		if(strcmp($3->original->token,"(ARGS NONE)")){
			printf("ERROR!(line %d) Main Procedure Cant Accept Arguments\n",yylineno);
			exit(1);
		}
	} 
	//declareId(a,b);
	idLinkedList *proc=getIdLink(a,"Proc\0");
	//saveArgsData(proc);
	$$=mknode2();$$->original=mknode("skip\0",mknode("(PROC\0",mknode("skip\0",mknode($1,NULL,NULL),$3->original),$6->original),mknode(")\0",NULL,NULL));
	$$->clean=mknode("PROC\0",NULL,$6->clean);$$->clean->startLabel=strdup($1);
	$$->clean->varsSize=$6->clean->varsSize;
};

FUNCC: PROCORFUNC '(' UPPERARGS ')' returnT TYPE '{' FUPPERBODY  '}'  {
	char *a=strdup("(RET \0");
	char *b=strdup($1);
	idLinkedList *func = getIdLink(b,"Func\0");
	func->returnType=strdup($6);
	//saveArgsData(func);
	//char *c=strdup("Func\0");
	if (!strcmp(b, "Main")) {
		printf("ERROR!(line %d) Main Cant Be Function\n",yylineno);
		exit(1);
	}
	//if (!checkIfIdExistAtCurrentScope(b)) {
	//	printf("ERROR!(line %d) %s Function/Procedure Already Declared\n",yylineno,b);
	//	exit(1);
	//}
	//declareId(b,c);
	char *name=strdup($8->original->left->right->left->left->token);//TODO: if returns var, check it is defined in current scope.
	
	char *t1=getTypeOfCallArg(name);
	if(!strcmp(t1,"VAR\0")){
		name=getType(name);
	}else{
		name=t1;
	}
	if(!strcmp(name,"CHAR\0")){
		if(strcmp($6,"CHAR\0")){
			printf("ERROR!(line %d) Function %s declared return type is %s and returned CHAR\n",yylineno,$1,$6);exit(1);
		}
	}else{
		char *type = name;
		if(!strcmp($6,"STRING\0")){
			printf("ERROR!(line %d) return type for function %s can't be a string.\n",yylineno,$1);
			exit(1);
		}
		if(strcmp($6,type)){
			printf("ERROR!(line %d) return type for function %s was %s, needs to be the same as declared(%s).\n",yylineno,$1,type,$6);
			exit(1);
		}
	}
	strcat(a,$6);
	strcat(a,")\0");
	$$=mknode2();$$->original=mknode("skip\0",mknode("(FUNC\0",mknode("skip\0",mknode($1,NULL,NULL),mknode("skip\0",$3->original,mknode(a,NULL,NULL))),$8->original),mknode(")\0",NULL,NULL));
	$$->clean=mknode("FUNC\0",NULL,$8->clean);$$->clean->startLabel=strdup($1);
	$$->clean->varsSize=$8->clean->varsSize;
};

PROCORFUNC: procT idT {
			idLinkedList *temp;
			char *a=strdup($2);
			char *b=strdup("Proc");
			if (!strcmp(a, "Main")) { 
				if (Main) {
					printf("ERROR!(line %d) Main Procedure Already Declared\n",yylineno);
					exit(1);
				}
				Main = true;
			} 
			else if (!checkIfIdExistAtCurrentScope(a)) {
				printf("ERROR!(line %d) %s Function/Procedure Already Declared\n",yylineno,a);
				exit(1);
			}
			temp=declareId(a,b);
			currentCallable=temp;
			addNewScope();
			temp->nextscope = highestScope;
			$$=a;
			}
	| funcT idT {
			idLinkedList *temp;
			char *a=strdup($2);
			char *b=strdup("Func");
			if (!strcmp(b, "Main")) {
				printf("ERROR!(line %d) Main Cant Be Function\n",yylineno);
				exit(1);
			}
			if (!checkIfIdExistAtCurrentScope(a)) {
				printf("ERROR!(line %d) %s Function/Procedure Already Declared\n",yylineno,b);
				exit(1);
			}
			temp=declareId(a,b);
			currentCallable=temp;
			addNewScope();
			temp->nextscope = highestScope;
			$$=a;
			};

LBRACE: '{' {addNewScope();};

RBRACE: '}' {removeLastScope();};

UPPERARGS:  {$$=mknode2();$$->original=mknode("(ARGS NONE)\0",NULL,NULL);}
	| ARGS {
		saveArgsData(currentCallable);
		currentCallable=NULL;
		$$=mknode2();$$->original=mknode("skip\0",mknode("(ARGS\0",$1->original,NULL),mknode(")\0",NULL,NULL))
		;};

ARGS: ARGSET {$$=$1;}
	| ARGS ';' ARGSET {$$=mknode2();$$->original=mknode("skip\0",$1->original,$3->original);};

ARGSET: idT ':' TYPE {
			char *a=strdup("(\0");
			strcat(a,$3);
			strcat(a," \0");
			strcat(a,$1);
			strcat(a,")\0");
			if (!checkIfVarExistAtCurrentScope($1)) {
				printf("ERROR!(line %d) %s Variable Already Declared\n",yylineno,$1);
				exit(1);
			}
			idLinkedList *link=declareId($1,$3);
			addTempArgs(link);
			$$=mknode2();$$->original=mknode(a,NULL,NULL);
			}
	| idT IDLIST ':' TYPE {
				char *id;
				char *a=strdup("(\0");
				strcat(a,$4);
				strcat(a," \0");
				strcat(a,$1);
				strcat(a,$2);
				strcat(a,")\0");
				if (!checkIfVarExistAtCurrentScope($1)) {
					printf("ERROR!(line %d) %s Variable Already Declared\n",yylineno,$1);
					exit(1);
				}
				idLinkedList *link=declareId($1,$4);
				addTempArgs(link);
				id = strtok ($2," ");
				while(id != NULL){
					if (!checkIfVarExistAtCurrentScope(id)) {
						printf("ERROR!(line %d) %s Variable Already Declared\n",yylineno,id);
						exit(1);
					}
					link=declareId(id,$4);
					addTempArgs(link);
					id = strtok(NULL," ");
				}
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				};

IDLIST: ',' idT IDLIST {
			char *s;
			s=strdup(" \0");
			strcat(s,$2);
			strcat(s,$3);
			$$=s;
			}
	| ',' idT {
			char *s;
			s=strdup(" \0");
			strcat(s,$2);
			$$=s;
		};


UPPERBODY: DECBODYORDEC {
			$$=mknode2();$$->original=mknode("skip\0",mknode("(BODY\0",$1->original,NULL),mknode(")\0",NULL,NULL))
			;$$->clean=$1->clean;};


DECBODYORDEC: UPDEC BODY {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;}

	| UPDEC {$$=$1;}

	| BODY {$$=$1;}

	| INNERBODY {$$=$1;};

FUPPERBODY: DECBODYORDEC returnT ANYVAL ';' {
$$=mknode2();$$->original=mknode(
	"skip\0",
	mknode(
		"(BODY\0",
		mknode(
			"skip\0",
			$1->original,
			NULL
		),
		mknode(
			"skip\0",
			mknode(
				"(RET\0",
				mknode($3,NULL,NULL),
				NULL
			),
			mknode(
				")\0",
				NULL,
				NULL
			)
		)
	),
	mknode(")\0",NULL,NULL));$$->clean=mknode("skip\0",$1->clean,mknode("RETURN\0",NULL,mknode($3,NULL,NULL)));$$->clean->varsSize=$1->clean->varsSize;}

	| returnT ANYVAL ';' {
	$$=mknode2();$$->original=mknode("skip\0",mknode("(BODY\0",NULL,mknode("skip\0",mknode("(RET\0",mknode($2,NULL,NULL),NULL),mknode(")\0",NULL,NULL))),mknode(")\0",NULL,NULL));$$->clean=mknode("RETURN\0",NULL,mknode($2,NULL,NULL));};


BODY: BLOCK {$$=$1;}/*

	| BODY SUBBODY {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);}*/;

// DECBODYORDEC	{var c:char;}c1='c';

INNERBODY: LBRACE DECBODYORDEC RBRACE {$$=mknode2();$$->original=mknode("skip\0",mknode("(BLOCK\0",$2->original,NULL),mknode(")\0",NULL,NULL));$$->clean=$2->clean;}
	| INNERBODY LBRACE DECBODYORDEC RBRACE {$$=mknode2();$$->original=mknode("skip\0",mknode("(BLOCK\0",$1->original,$3->original),mknode(")\0",NULL,NULL));$$->clean=getMinimalTree($1->clean,$3->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($3->clean->varsSize)vSize+=$3->clean->varsSize;
	$$->clean->varsSize=vSize;};

UPDEC: DECLARATIONS {$$=$1;}

	| INNERBODY DECLARATIONS {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;}

	| UPDEC DECLARATIONS {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;}/*

	| LBRACE DECBODYORDEC RBRACE {$$=mknode2();$$->original=mknode("skip\0",mknode("(BLOCK\0",$2->original,NULL),mknode(")\0",NULL,NULL));}

	| UPDEC LBRACE DECBODYORDEC RBRACE {$$=mknode2();$$->original=mknode("skip\0",$1->original,mknode("skip\0",mknode("(BLOCK\0",$3->original,NULL),mknode(")\0",NULL,NULL)));}*/;

DECLARATIONS: VARDECLARE {$$=$1;}

	| PROCC {$$-mknode2();$$->original=$1->original;$$->clean=mknode("skip\0",NULL,$1->clean);;$$->clean->varsSize=0;removeLastScope();}

	| FUNCC {$$=mknode2();$$->original=$1->original;$$->clean=mknode("skip\0",NULL,$1->clean);$$->clean->varsSize=0;removeLastScope();};

/*SUBBODY: ST {$$=$1;}

	| SUBBLOCK {$$=$1;};*/


ST: ifT '(' CONDITION ')' LBRACE /* { */ TOTALBLOCK /* ;} */ RBRACE elseT LBRACE /* { */ TOTALBLOCK /* ;} */ RBRACE {
	$$=mknode2();
	$$->original=
mknode(
	"skip\0",
	mknode(
		"(IF-ELSE\0",
		mknode(
			"skip\0",
			$3->original,
			$6->original
		),
		mknode(
			"skip\0",
			$10->original,
			NULL
		)
	),
	mknode(
		")\0",
		NULL,
		NULL
	)
);
$$->clean=mknode("skip\0",mknode("IF\0",NULL,mknode("skip\0",$3->clean,$6->clean)),mknode("ELSE\0",NULL,$10->clean));int vSize=0;if($3->clean->varsSize)vSize+=$3->clean->varsSize;
	if($6->clean->varsSize)vSize+=$6->clean->varsSize;
	if($10->clean->varsSize)vSize+=$10->clean->varsSize;
	$$->clean->varsSize=vSize;
	}

	| ifT '(' CONDITION ')' LBRACE /* { */ TOTALBLOCK /* ;} */ RBRACE {
		$$=mknode2();$$->original=mknode("skip\0",mknode("(IF\0",$3->original,$6->original),mknode(")\0",NULL,NULL));$$->clean=mknode("IF\0",NULL,mknode("skip\0",$3->clean,$6->clean));int vSize=0;if($3->clean->varsSize)vSize+=$3->clean->varsSize;
	if($6->clean->varsSize)vSize+=$6->clean->varsSize;
	$$->clean->varsSize=vSize;
	}
	| whileT '(' CONDITION ')' LBRACE TOTALBLOCK RBRACE {
		$$=mknode2();$$->original=mknode("skip\0",mknode("(WHILE\0",$3->original,$6->original),mknode(")\0",NULL,NULL));$$->clean=mknode("WHILE\0",NULL,mknode("skip\0",$3->clean,$6->clean));int vSize=0;if($3->clean->varsSize)vSize+=$3->clean->varsSize;
	if($6->clean->varsSize)vSize+=$6->clean->varsSize;
	$$->clean->varsSize=vSize;
	};

TOTALBLOCK: BLOCK {$$=mknode2();$$->original=mknode("skip\0",mknode("(BLOCK\0",$1->original,NULL),mknode(")\0",NULL,NULL));$$->clean=$1->clean;};

BLOCK: BLOCK SUBBLOCK {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;
	}

	| SUBBLOCK {$$=$1;};

SUBBLOCK: ASN {$$=$1;}

	| INNERBODY ASN {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;
	}

	| FUNCORPROCCALL {$$=$1;}

	| INNERBODY FUNCORPROCCALL {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;
	}

	| ST {$$=$1;}

	| INNERBODY ST {$$=mknode2();$$->original=mknode("skip\0",$1->original,$2->original);$$->clean=getMinimalTree($1->clean,$2->clean);
	int vSize=0;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($2->clean->varsSize)vSize+=$2->clean->varsSize;
	$$->clean->varsSize=vSize;
	};

VARDECLARE: varT idT IDLIST ':' TYPE ';' {
						char *id;
						if (!checkIfVarExistAtCurrentScope($2)) {
							printf("ERROR!(line %d) %s Variable Already Declared\n",yylineno,$2);
							exit(1);
						}
						declareId($2,$5);
						int typeSize = getTypeSize($5);
						int vSize = typeSize;
						int isStr=typeIsString($5);
						int len = 0;
						idLinkedList *str=NULL;
						if(isStr){
							str=getIdLink($2,$5);
							len = getNumFromStrType($5);
							str->size=len;
						}
						id = strtok ($3," ");
						
						while(id != NULL){
							if (!checkIfVarExistAtCurrentScope(id)){
								printf("ERROR!(line %d) %s Variable Already Declared\n",yylineno,id);
								exit(1);
							}
							declareId(id,$5);
							vSize+=typeSize;
							if(isStr){
								str=getIdLink(id,$5);
								str->size=len;
							}
							id = strtok(NULL," ");
						}
						char *s;
						s=strdup("(VAR \0");
						strcat(s,$5);
						strcat(s," \0");
						strcat(s,$2);
						strcat(s,$3);
						strcat(s,")\0");
						$$=mknode2();$$->original=mknode(s,NULL,NULL);
						$$->clean=mknode(s,NULL,NULL);
						$$->clean->varsSize=vSize;
					}
	| varT idT ':' TYPE ';' {
				if (!checkIfVarExistAtCurrentScope($2)) {
					printf("ERROR!(line %d) %s Variable Already Declared\n",yylineno,$2);
					exit(1);
				}
				declareId($2,$4);
				if(typeIsString($4)){
					idLinkedList *str=getIdLink($2,$4);
					int len = getNumFromStrType($4);
					str->size=len;
				}
				char *s;
				s=strdup("(VAR \0");
				strcat(s,$4);
				strcat(s," \0");
				strcat(s,$2);
				strcat(s,")\0");
				$$=mknode2();$$->original=mknode(s,NULL,NULL);
				$$->clean=mknode(s,NULL,NULL);
				$$->clean->varsSize=getTypeSize($4);
			};

TYPE: intT {$$="INT\0";}

	/*| intT '[' numT ']' {
				char* s;
				char num1[5];
				num1[4]='\0';
				s=strdup("INT\0");
				strcat(s,"[\0");
				sprintf(num1,"%d",$3);
				strcat(s,num1);
				strcat(s, "]\0");
				$$=s;
			}*/

        | realT {$$="REAL\0";}

	/*| realT '[' numT ']' {
				char* s;
				char num1[5];
				num1[4]='\0';
				s=strdup("REAL\0");
				strcat(s,"[\0");
				sprintf(num1,"%d",$3);
				strcat(s,num1);
				strcat(s, "]\0");
				$$=s;
			}*/

	/*| charT '[' numT ']' {
				char* s;
				char num1[5];
				num1[4]='\0';
				s=strdup("CHAR\0");
				strcat(s,"[\0");
				sprintf(num1,"%d",$3);
				strcat(s,num1);
				strcat(s, 	"]\0");
				$$=s;
			}*/

         | boolT {$$="BOOL\0";}

         | charT {$$="CHAR\0";}

        /*| strT {$$="STRING\0";}*/

	| strT '[' numT ']' {
				char* s;
				char num1[5];
				num1[4]='\0';
				s=strdup("STRING\0");
				strcat(s,"[\0");
				sprintf(num1,"%d",$3);
				strcat(s,num1);
				strcat(s, "]\0");
				$$=s;
			}

         | intpT {$$="INTPOINTER\0";}

        | charpT {$$="CHARPOINTER\0";}

        | realpT {$$="REALPOINTER\0";};

ASN: idT '=' idT ';' {
			if(find3($1)){
				printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
				exit(1);
			}
			if(find3($3)){
				printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$3);
				exit(1);
			}
			char *t1=getType($1);
			char *t2=getType($3);
			if(strcmp(t1,t2)){
				printf("ERROR!(line %d)type of %s (%s) is not type of %s (%s)\n",yylineno,$1,t1,$3,t2);
				exit(1);
			}
			char *a=strdup("(=\0");
			strcat(a,$1);
			strcat(a," \0");
			strcat(a,$3);
			strcat(a,")\0");
			$$=mknode2();$$->original=mknode(a,NULL,NULL);
			$$->clean=mknode("=",mknode($1,NULL,NULL),mknode($3,NULL,NULL));
		}
	| idT '=' realnumT ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *t1=getType($1);
				if(strcmp(t1,"REAL\0")){
					printf("ERROR!(line %d) Can't assign REAL into %s (%s).\n",yylineno,$1,t1);
					exit(1);
				}
				char *a=strdup("(=\0");
				strcat(a,$1);
				strcat(a," \0");
				strcat(a,$3);
				strcat(a,")\0");
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				$$->clean=mknode("=",mknode($1,NULL,NULL),mknode($3,NULL,NULL));
				}
	| idT '=' charlitT ';' {
			if(find3($1)){
				printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
				exit(1);
			}
			char *t1=getType($1);
			if(strcmp(t1,"CHAR\0")){
				printf("ERROR!(line %d)type of %s (%s) is not type of CHAR\n",yylineno,$1,t1);
				exit(1);
			}
			char *a=strdup("(=\0");
			strcat(a,$1);
			strcat(a," \0");
			strcat(a,$3);
			strcat(a,")\0");
			$$=mknode2();$$->original=mknode(a,NULL,NULL);
			$$->clean=mknode("=",mknode($1,NULL,NULL),mknode($3,NULL,NULL));
		}
	
	| idT '=' strlitT ';' {
			if(find3($1)){
				printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
				exit(1);
			}
			char *t1=getType($1);
			if(!typeIsString(t1)){
				printf("ERROR!(line %d) Can't assign string literal to %s, only to string.\n",yylineno,t1);
				exit(1);
			}
			char *a=strdup("(=\0");
			strcat(a,$1);
			strcat(a," \0");
			strcat(a,$3);
			strcat(a,")\0");
			$$=mknode2();$$->original=mknode(a,NULL,NULL);
			$$->clean=mknode("=",mknode($1,NULL,NULL),mknode($3,NULL,NULL));
		}
	| idT '=' '&' idT ';'{
			if(find3($1)){
				printf("ERROR!(line %d) %s Never Declared. \n",yylineno,$1);
				exit(1);
			}
			if(find3($4)){
				printf("ERROR!(line %d) %s Never Declared. \n",yylineno,$4);
				exit(1);
			}
			char *t1 = getType($1);
			char *t2 = getType($4);		
			if(!strcmp(t1,"BOOL") || !strcmp(t2,"BOOL")){
				printf("ERROR!(line %d)type, Can't be boolean type\n",yylineno);
				exit(1);
			}
			else if(!strcmp(t1,"INTPOINTER") && strcmp(t2,"INT")){
				printf("ERROR!(line %d)type, %s (%s) need to be INT type.\n",yylineno,$4,t2 );
				exit(1);
			}
			else if(!strcmp(t1,"CHARPOINTER") && strcmp(t2,"CHAR")){
				printf("ERROR!(line %d)type, %s (%s) need to be CHAR type.\n",yylineno,$4,t2 );
				exit(1);
			}
			else if(!strcmp(t1,"REALPOINTER") && strcmp(t2,"REAL")){
				printf("ERROR!(line %d)type, %s (%s) need to be REAL type.\n",yylineno,$4,t2 );
				exit(1);
			}
			else if(!strcmp(t1,"INT") || !strcmp(t1,"CHAR") || !strcmp(t1,"REAL") || typeIsString(t1)){
				printf("ERROR!(line %d)type, Your first argument %s (%s) need to be pointer type.\n",yylineno, $1,t1);
				exit(1);
			}
			char *a = strdup("(=\0");
			strcat(a,$1);
			strcat(a," &\0");
			strcat(a,$4);
			strcat(a, ")\0");
			$$=mknode2();$$->original=mknode(a, NULL,NULL);			
			$$->clean=mknode("=",mknode($1,NULL,NULL),mknode("&",NULL,mknode($4,NULL,NULL)));
			}
	| idT '=' '^' idT ';'{
			if(find3($1)){
				printf("ERROR!(line %d) %s Never Declared. \n",yylineno,$1);
				exit(1);
			}
			if(find3($4)){
				printf("ERROR!(line %d) %s Never Declared. \n",yylineno,$4);
				exit(1);
			}
			char *t1 = getType($1);
			char *t2 = getType($4);		
			if(!strcmp(t1,"BOOL") || !strcmp(t2,"BOOL")){
				printf("ERROR!(line %d)type, Can't be boolean type\n",yylineno);
				exit(1);
			}
			else if(strcmp(t2,"INTPOINTER") && !strcmp(t1,"INT")){
				printf("ERROR!(line %d)type, %s (%s) need to be INTPOINTER type.\n",yylineno,$4,t2 );
				exit(1);
			}
			else if(strcmp(t2,"CHARPOINTER") && !strcmp(t1,"CHAR")){
				printf("ERROR!(line %d)type, %s (%s) need to be CHARPOINTER type.\n",yylineno,$4,t2 );
				exit(1);
			}
			else if(strcmp(t2,"REALPOINTER") && !strcmp(t1,"REAL")){
				printf("ERROR!(line %d)type, %s (%s) need to be REALPOINTER type.\n",yylineno,$4,t2 );
				exit(1);
			}
			else if(!strcmp(t1,"INTPOINTER") || !strcmp(t1,"CHARPOINTER") || !strcmp(t1,"REALPOINTER") || typeIsString(t1)){
				printf("ERROR!(line %d)type, Your first argument %s (%s) need to be primitive type.\n",yylineno, $1,t1);
				exit(1);
			}
			char *a = strdup("(=\0");
			strcat(a,$1);
			strcat(a," &\0");
			strcat(a,$4);
			strcat(a, ")\0");
			$$=mknode2();$$->original=mknode(a, NULL,NULL);			
			$$->clean=mknode("=",mknode($1,NULL,NULL),mknode("^",NULL,mknode($4,NULL,NULL)));
			}

	| idT '=' numT ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *t1=getType($1);
				char num[9];
				num[8]='\0';
				sprintf(num,"%d",$3);
				if(strcmp(t1,"INT\0")){
					printf("ERROR!(line %d)type of %s (%s) is not type of %d (INT)\n",yylineno,$1,t1,$3);
				}
				char *a=strdup("(=\0");
				strcat(a,$1);
				strcat(a," \0");
				strcat(a,num);
				strcat(a,")\0");
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				$$->clean=mknode("=",mknode($1,NULL,NULL),mknode(num,NULL,NULL));
			}
	| idT '=' '|' idT '|' ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *t1=getType($1);
				int notFound=find3($4);
				if(notFound){
					printf("ERROR!(line %d) String %s was not found.\n",yylineno,$4);
					exit(1);
				}
				char *type=strdup(getType($4));
				if(!typeIsString(type)){
					printf("ERROR!(line %d) Operator || can only be used on a string, not %s.\n",yylineno,type);
					exit(1);
				}
				if(strcmp(t1,"INT\0")){
					printf("ERROR!(line %d) Can't assign INT into %s (%s).\n",yylineno,$1,t1);
					exit(1);
				}
				char *a=strdup("(=\0");
				strcat(a,$1);
				strcat(a," \0");
				strcat(a,"|\0");
				strcat(a,$4);
				strcat(a,"|\0");
				strcat(a,")\0");
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				$$->clean=mknode("=",mknode($1,NULL,NULL),mknode("||",NULL,mknode($4,NULL,NULL)));
				}
	| idT '=' '|' strlitT '|' ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *t1=getType($1);
				if(strcmp(t1,"INT\0")){
					printf("ERROR!(line %d) Can't assign INT into %s (%s).\n",yylineno,$1,t1);
					exit(1);
				}
				char *a=strdup("(=\0");
				strcat(a,$1);
				strcat(a," \0");
				strcat(a,"|\0");
				strcat(a,$4);
				strcat(a,"|\0");
				strcat(a,")\0");
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				$$->clean=mknode("=",mknode($1,NULL,NULL),mknode("||",NULL,mknode($4,NULL,NULL)));
				}
	| idT '=' nullT ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *t1=getType($1);
				if(
					strcmp(t1,"INTPOINTER\0")
					&&strcmp(t1,"CHARPOINTER\0")
					&&strcmp(t1,"REALPOINTER\0")
				){
					printf("ERROR!(line %d) Can only assign null to a pointer type, not %s.\n",yylineno,t1);
					exit(1);
				}
				char *a=strdup("(=\0");
				strcat(a,$1);
				strcat(a," NULL\0");
				strcat(a,")\0");
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				$$->clean=mknode("=",mknode($1,NULL,NULL),mknode("NULL",NULL,NULL));
			}

	| idT '=' EXP ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *a=strdup("(=\0");
				strcat(a,$1);
				char *t1=getType($1);
				if(isReal){
					if(strcmp(t1,"REAL")){
						printf("ERROR!(line %d)type of %s (%s) is not type of EXPRESSION (REAL)\n",yylineno,$1,t1);
						exit(1);
					}
				}
				else if(strcmp(t1,"INT\0")){
					printf("ERROR!(line %d)type of %s (%s) is not type of EXPRESSION (INT)\n",yylineno,$1,t1);
					exit(1);
				}
				isReal = false;
				$$=mknode2();$$->original=mknode("skip\0",mknode(a,$3->original,NULL),mknode(")\0",NULL,NULL));
				$$->clean=mknode("=",mknode($1,NULL,NULL),$3->clean);
				$$->clean->varsSize=$3->clean->varsSize;
			}

	| idT '=' SCOND ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *type=strdup(getType($1));
				if(strcmp(type,"BOOL\0")){
					printf("ERROR!(line %d) Can't assign bool value into variable %s (%s).\n",yylineno,$1,type);
					exit(1);
				}
				char *a=strdup("(=\0");
				$$=mknode2();$$->original=mknode("skip\0",mknode(a,mknode($1,NULL,NULL),$3->original),mknode(")\0",NULL,NULL));
				$$->clean=mknode("=",mknode($1,NULL,NULL),$3->clean);
				$$->clean->varsSize=$3->clean->varsSize;
			}

	| idT '=' ACOND ';' {
				if(find3($1)){
					printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
					exit(1);
				}
				char *type=strdup(getType($1));
				if(strcmp(type,"BOOL\0")){
					printf("ERROR!(line %d) Can't assign bool value to %s variable.\n",yylineno,type);
					exit(1);
				}
				char *a=strdup("(=\0");
				$$=mknode2();$$->original=mknode("skip\0",mknode(a,mknode($1,NULL,NULL),$3->original),mknode(")\0",NULL,NULL));
				$$->clean=mknode("=",mknode($1,NULL,NULL),$3->clean);
				$$->clean->varsSize=$3->clean->varsSize;
			}

	| idT '[' numT ']' '=' idT ';' {
					if(find3($1)){
						printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
						exit(1);
					}
					if(find3($6)){
						printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$6);
						exit(1);
					}
					char *t1=getType($1);
					if(!typeIsString(t1)){
						printf("ERROR!(line %d) The [] operator can't be used on a %s, only on a string.\n",yylineno,t1);
						exit(1);
					}
					char num[9];
					num[8]='\0';
					sprintf(num,"%d",$3);
					idLinkedList *str=getIdLink($1,t1);
					int maxlen=str->size;
					if(!($3>=0 && $3<maxlen)){
						printf("ERROR!(line %d) Illegal index number (%d) is not in range (%d-%d).\n",yylineno,$3,0,maxlen-1);
						exit(1);
					}
					char *t2=getType($6);
					if(strcmp(t2,"CHAR\0")){
						printf("ERROR!(line %d) Type of %s (%s) is not type of %s (%s)\n",yylineno,$1,t1,$6,t2);
						exit(1);
					}
					char *a=strdup("(=\0");
					strcat(a,$1);
					strcat(a,"[\0");
					strcat(a,num);
					strcat(a,"] \0");
					strcat(a,$6);
					strcat(a,")\0");
					$$=mknode2();$$->original=mknode(a,NULL,NULL);
					$$->clean=mknode("=",mknode("+",mknode($1,NULL,NULL),mknode(num,NULL,NULL)),mknode($6,NULL,NULL));
					}
	| idT '[' numT ']' '=' charlitT ';' {
					if(find3($1)){
						printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
						exit(1);
					}
					char *t1=getType($1);
					if(!typeIsString(t1)){
						printf("ERROR!(line %d) The [] operator can't be used on a %s, only on a string.\n",yylineno,t1);
						exit(1);
					}
					char num[9];
					num[8]='\0';
					sprintf(num,"%d",$3);
					idLinkedList *str=getIdLink($1,t1);
					int maxlen=str->size;
					if(!($3>=0 && $3<maxlen)){
						printf("ERROR!(line %d) Illegal index number (%d) is not in range (%d-%d).\n",yylineno,$3,0,maxlen-1);
						exit(1);
					}
					char *a=strdup("(=\0");
					strcat(a,$1);
					strcat(a,"[\0");
					strcat(a,num);
					strcat(a,"] \0");
					strcat(a,$6);
					strcat(a,")\0");
					$$=mknode2();$$->original=mknode(a,NULL,NULL);
					$$->clean=mknode("=",mknode("+",mknode($1,NULL,NULL),mknode(num,NULL,NULL)),mknode($6,NULL,NULL));
					}

	/*| idT '[' numT ']' '=' numT ';' {
					if(find3($1)){
						printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
						exit(1);
					}
					char *t1=getType($1);
					char num[9];
					num[8]='\0';
					sprintf(num,"%d",$3);
					char num2[9];
					num2[8]='\0';
					sprintf(num2,"%d",$6);
					if(strcmp(t1,"INT\0")){
						printf("ERROR!(line %d)type of %s (%s) is not type of %d (INT)\n",yylineno,$1,t1,$6);
					}
					char *a=strdup("(=\0");
					strcat(a,$1);
					strcat(a,"[\0");
					strcat(a,num);
					strcat(a,"] \0");
					strcat(a,num2);
					strcat(a,")\0");
					$$=mknode2();$$->original=mknode(a,NULL,NULL);
					}*/

	/*| idT '[' numT ']' '=' EXP ';' {
					if(find3($1)){
						printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
						exit(1);
					}
					char *t1=getType($1);
					char num[9];
					num[8]='\0';
					sprintf(num,"%d",$3);
					if(strcmp(t1,"INT\0")){
						printf("ERROR!(line %d)type of %s (%s) is not type of expression (INT)\n",yylineno,$1,t1);
					}
					char *a=strdup("(=\0");
					strcat(a,$1);
					strcat(a,"[\0");
					strcat(a,num);
					strcat(a,"] \0");
					$$=mknode2();$$->original=mknode("skip\0",mknode(a,$6->original,NULL),mknode(")\0",NULL,NULL))
				;}*/
	| idT '=' FUNCORPROCCALL {
	char *t1=strdup(getType($1));
	char *t2=strdup(getType($3->original->token));
	if(strcmp(t2,"Func\0")){
		printf("ERROR!(line %d) Can't assign from procedure.\n",yylineno);exit(1);
	}
	idLinkedList *func = getIdLink($3->original->token,"Func\0");
	if(strcmp(t1,func->returnType)){
		printf("ERROR!(line %d) Var type (%s) and function return type (%s) must be the same.\n",yylineno,t1,func->returnType);exit(1);
	}
	char *asnStr=strdup("(=\0");
	char *callName=strdup("(CALL \0");
	strcat(callName,$3->original->token);
	node *argsOfCall=NULL;
	node *hasOneArg=$3->original->left;
	node *hasMoreArgs=$3->original->right;
	node *rightCloserOfCall=NULL;
	if(hasOneArg){
		rightCloserOfCall=mknode(")\0",NULL,NULL);
		char *args=strdup("(ARGS \0");
		strcat(args,hasOneArg->token);
		if(hasMoreArgs){
			strcat(args,hasMoreArgs->token);
		}
		strcat(args,")\0");
		argsOfCall=mknode(args,NULL,NULL);
	}else{
		strcat(callName,")\0");
	}
	strcat(asnStr,$1);
	$$=mknode2();$$->original=mknode(
		"skip\0",
		mknode(
			asnStr,
			mknode(
				callName,
				argsOfCall,
				NULL
			),
			rightCloserOfCall
		),
		mknode(
			")\0",
			NULL,
			NULL
		)
	);
	$$->clean=mknode("=",mknode($1,NULL,NULL),$3->clean);
	$$->clean->varsSize=$3->clean->varsSize;
};


CONDITION: ACOND {$$=$1;}
	| SCOND {$$=$1;}
	| EXPORANYVAL {$$=$1;};

ACOND: NOT '(' COND ')' {$$=mknode2();$$->original=mknode("skip\0",mknode($1,NULL,NULL),mknode("skip\0",mknode("(\0",$3->original,NULL),mknode(")\0",NULL,NULL)));$$->clean=mknode("!",NULL,$3->clean);$$->clean->varsSize=$3->clean->varsSize;}
	| COND {$$=mknode2();$$->original=mknode("skip\0",$1->original,NULL);$$->clean=$1->clean;};

SCOND: SIMPLE {$$=$1;}
	| NOT SIMPLE {$$=mknode2();$$->original=mknode("skip\0",mknode($1,NULL,NULL),$2->original);$$->clean=mknode("!",NULL,$2->clean);$$->clean->varsSize=$2->clean->varsSize;}
	| '(' SCOND ')' {$$=mknode2();$$->original=mknode("skip\0",mknode("(\0",$2->original,NULL),mknode(")\0",NULL,NULL));$$->clean=$2->clean;}
	| NOT '(' SCOND ')' {$$=mknode2();$$->original=mknode("skip\0",mknode("skip\0",mknode("!\0",NULL,NULL),mknode("(\0",$3->original,NULL)),mknode(")\0",NULL,NULL));$$->clean=mknode("!",NULL,$3->clean);$$->clean->varsSize=$3->clean->varsSize;};

EXPORANYVAL: EXP {$$=$1;isReal=0;} // TODO: check if need to set global isReal to false here.
	| CALLARG {$$=mknode2();$$->original=mknode($1,NULL,NULL);$$->clean=mknode($1,NULL,NULL);$$->clean->varsSize=0;};
// ACOND
COND: COND COMP SCOND {$$=mknode2();$$->original=mknode($2,$1->original,$3->original);$$->clean=mknode($2,$1->clean,$3->clean);$$->clean->varsSize=$1->clean->varsSize+$3->clean->varsSize;}
	| SCOND COMP SCOND {$$=mknode2();$$->original=mknode($2,$1->original,$3->original);$$->clean=mknode($2,$1->clean,$3->clean);$$->clean->varsSize=$1->clean->varsSize+$3->clean->varsSize;}
	| SCOND COMP '(' COND ')' {$$=mknode2();$$->original=mknode($2,$1->original,mknode("skip\0",mknode("(\0",$4->original,NULL),mknode(")\0",NULL,NULL)));$$->clean=mknode($2,$1->clean,$4->clean);$$->clean->varsSize=$1->clean->varsSize+$4->clean->varsSize;}
	| COND COMP '(' COND ')' {$$=mknode2();$$->original=mknode($2,$1->original,mknode("skip\0",mknode("(\0",$4->original,NULL),mknode(")\0",NULL,NULL)));$$->clean=mknode($2,$1->clean,$4->clean);$$->clean->varsSize=$1->clean->varsSize+$4->clean->varsSize;}
	| '(' COND ')' {$$=mknode2();$$->original=mknode("skip\0",mknode("(\0",$2->original,NULL),mknode(")\0",NULL,NULL));$$->clean=$2->clean;};



SIMPLE: EXPORANYVAL COMP EXPORANYVAL {char *a=strdup("(\0");strcat(a,$2);$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,$3->original),mknode(")\0",NULL,NULL));$$->clean=mknode($2,$1->clean,$3->clean);
	int vSize=1;if($1->clean->varsSize)vSize+=$1->clean->varsSize;
	if($3->clean->varsSize)vSize+=$3->clean->varsSize;
	$$->clean->varsSize=vSize;}/*
	| EXPORANYVAL COMP trueT {char *a=strdup("(\0");strcat(a,$2);$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,mknode("TRUE\0",NULL,NULL)),mknode(")\0",NULL,NULL));}
	| EXPORANYVAL COMP falseT {char *a=strdup("(\0");strcat(a,$2);$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,mknode("FALSE\0",NULL,NULL)),mknode(")\0",NULL,NULL));}
	| trueT {$$=mknode2();$$->original=mknode("TRUE\0",NULL,NULL);}
	| falseT {$$=mknode2();$$->original=mknode("FALSE\0",NULL,NULL);}*/;

NOT: '!' {$$="!\0";}; // !(!X<Y && FALSE || (y<=5))

COMP: '>' {$$=">\0";}

	| '<' {$$="<\0";}

	| eqT {$$="==\0";}

	| gteqT {$$=">=\0";}

	| lteqT {$$="<=\0";}

	| neqT {$$="!=\0";}
	
	| andT {$$="&&\0";}

	| orT {$$="||\0";};


/*ANDOR:	andT {$$="&&\0";}

	| orT {$$="||\0";};*/


/*COND: COND COMP ANYVAL {;}

	| ANYVAL COMP ANYVAL {
				char *a=strdup("(\0");
				strcat(a,$2);
				$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,$3),mknode(")\0",NULL,NULL))
	;}
	
	| ANYVAL{
			if(!strcmp($1,"(TRUE)") || !strcmp($1,"(FALSE)")){
				$$=mknode2();$$->original=mknode($1,NULL,NULL)
			;}
			else $$=mknode2();$$->original=mknode("skip\0",mknode("(\0",mknode($1,NULL,NULL),NULL),mknode(")\0",NULL,NULL))
			if ( cond ) condition = true;
			else condition = false;
		};*/

	//| EXP {$$=mknode2();$$->original=mknode("skip\0",mknode("(\0",$1->original,NULL),mknode(")\0",NULL,NULL));};



ANYVAL: idT {
		if(find3($1)){
			printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
			exit(1);
		}
		$$=$1;}

	| numT {
		char *number;
		char num[9];
		num[8]='\0';
		sprintf(num,"%d",$1);
		number=strdup(num);
		$$ = number;
		if($1 != 0) cond++;
		}
	
	| realnumT{
		if(atof($1) != 0 ) cond++;
		$$ = $1;	
	}

	| charlitT {$$=$1;};

	/*| trueT {
			char *a=strdup("(TRUE)\0");
			$$=a;
			cond++;
		}

	| falseT {
			char *a=strdup("(FALSE)\0");
			$$=a;
		};*/


/*EXP: EXP AOP IDORNUM {
			char *a=strdup("(\0");
			strcat(a,$2);
			$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,mknode($3,NULL,NULL)),mknode(")\0",NULL,NULL))
			;}

	| IDORNUM AOP IDORNUM {
				char *a=strdup("(\0");
				strcat(a,$2);
				strcat(a," \0");
				strcat(a,$1);
				strcat(a," \0");
				strcat(a,$3);
				strcat(a,")\0");
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				}
	| EXP AOP '(' EXP ')' {
			char *a=strdup("(\0");
			strcat(a,$2);
			$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,$4),mknode(")\0",NULL,NULL))
			;}
	| IDORNUM AOP '(' EXP ')' {
				char *a=strdup("(\0");
				strcat(a,$2);
				strcat(a," \0");
				strcat(a,$1);
				$$=mknode2();$$->original=mknode("skip\0",mknode(a,$4->original,NULL),mknode(")\0",NULL,NULL))
				;}
	| '(' EXP ')' {$$=$2;};*/

EXP: EXP AOP CALLARG {
			validSubExp($3);
			char *a=strdup("(\0");
			strcat(a,$2);
			$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,mknode($3,NULL,NULL)),mknode(")\0",NULL,NULL));
			$$->clean=mknode($2,$1->clean,mknode($3,NULL,NULL));
			int vSize=4;
			if(isReal)vSize=8;
			$$->clean->varsSize=vSize+$1->clean->varsSize;
			}

	| CALLARG AOP CALLARG {
				validSubExp($1);
				validSubExp($3);
				char *a=strdup("(\0");
				strcat(a,$2);
				strcat(a," \0");
				strcat(a,$1);
				strcat(a," \0");
				strcat(a,$3);
				strcat(a,")\0");
				$$=mknode2();$$->original=mknode(a,NULL,NULL);
				$$->clean=mknode($2,mknode($1,NULL,NULL),mknode($3,NULL,NULL));
				int vSize=4;
				if(isReal)vSize=8;
				$$->clean->varsSize=vSize;
				}
	| EXP AOP '(' EXP ')' {
			char *a=strdup("(\0");
			strcat(a,$2);
			$$=mknode2();$$->original=mknode("skip\0",mknode(a,$1->original,$4->original),mknode(")\0",NULL,NULL));
			$$->clean=mknode($2,$1->clean,$4->clean);
			int vSize=4;
			if(isReal)vSize=8;
			$$->clean->varsSize=vSize+$1->clean->varsSize+$4->clean->varsSize;
			}
	| CALLARG AOP '(' EXP ')' {
				validSubExp($1);
				char *a=strdup("(\0");
				strcat(a,$2);
				strcat(a," \0");
				strcat(a,$1);
				$$=mknode2();$$->original=mknode("skip\0",mknode(a,$4->original,NULL),mknode(")\0",NULL,NULL));
				$$->clean=mknode($2,mknode($1,NULL,NULL),$4->clean);
				int vSize=4;
				if(isReal)vSize=8;
				$$->clean->varsSize=vSize+$4->clean->varsSize;
				}
	| '(' EXP ')' {$$=$2;}

	| AOP CALLARG {
		if(strcmp($1,"-\0")){
			printf("ERROR!(line %d) %s is a binary operator.\n",yylineno,$1);
			exit(1);
		}
		validSubExp($2);
		char *a=strdup("(-\0");
		strcat(a,$2);
		strcat(a,")\0");
		$$=mknode2();$$->original=mknode(a,NULL,NULL);
		$$->clean=mknode($1,NULL,mknode($2,NULL,NULL));
		int vSize=4;
		if(isReal)vSize=8;
		$$->clean->varsSize=vSize;
	};

/*IDORNUM: idT {
		if(find3($1)){
			printf("ERROR!(line %d) %s Never Declared.\n",yylineno,$1);
			exit(1);
		}
		char *type = getType($1);
		if(!strcmp(type,"INT")) ;
		else if(!strcmp(type,"REAL")) isReal = true;
		else {
			printf("ERROR!(line %d) %s Type Is Not Int OR Real.\n",yylineno,$1);
			exit(1);
		}
		$$=$1;}

	| numT {
		char *number;
		char num[9];
		num[8]='\0';
		sprintf(num,"%d",$1);
		number=strdup(num);
		$$=number;printf("AAAAA1 %s\n",num);
		}
	| realnumT {$$=$1;isReal = true;};*/


AOP: '+' {$$="+\0";}

	| '-' {$$="-\0";}

	| '*' {$$="*\0";}

	| '/' {$$="/\0";};

/*UPPERLIST: UPPERLIST NUMORIDLIST {
					char *a=strdup($1);
					strcat(a,$2);
					$$=a;
				}

	| NUMORIDLIST {$$=$1;};

NUMORIDLIST: ',' idT {
			char *s;
			s=strdup(" \0");
			strcat(s,$2);
			$$=s;
		}
	| ',' numT {
			char s[10];s[9]='\0';
			sprintf(s,"%d",$2);
			char *a=strdup(" \0");
			strcat(a,s);
			$$=a;
		};*/

CALLARG: idT {$$=$1;}
	| numT {char num[9];
		num[8]='\0';
		sprintf(num,"%d",$1);
		char *a=strdup(num);
		$$=a;}
	| realnumT {$$=$1;}
	| charlitT {$$=$1;}
	| trueT {char *a=strdup("TRUE\0");$$=a;}
	| falseT {char *a=strdup("FALSE\0");$$=a;}
	| '|' idT '|' {
			int notFound=find3($2);
			if(notFound){
				printf("ERROR!(line %d) String %s was not found.\n",yylineno,$2);
				exit(1);
			}
			char *type=strdup(getType($2));
			if(!typeIsString(type)){
				printf("ERROR!(line %d) Operator || can only be used on a string, not %s.\n",yylineno,type);
				exit(1);
			}
			char *a=strdup("|\0");
			strcat(a,$2);
			strcat(a,"|\0");
			$$=a;
			}
	| '|' strlitT '|' {
			char *a=strdup("|\0");
			strcat(a,$2);
			strcat(a,"|\0");
			$$=a;
			};

CALLARGLIST: ',' CALLARG CALLARGLIST {
			char *s;
			s=strdup(" \0");
			strcat(s,$2);
			strcat(s,$3);
			$$=s;
			}
	| ',' CALLARG {
			char *s;
			s=strdup(" \0");
			strcat(s,$2);
			$$=s;
		};

FUNCORPROCCALL: idT '(' ')' ';' {
	callableExistsOrExit($1);

	//next code checks for missing arguments
	idLinkedList *callable;
	int notFunc=find2($1,"Func\0");
	char *call;
	int vSize=0;
	if(notFunc){
		callable=getIdLink($1,"Proc\0");
		call = strdup("PCALL\0");
	}else{
		callable=getIdLink($1,"Func\0");
		call = strdup("FCALL\0");
		vSize=getTypeSize(callable->returnType);
	}
	if(callable->args){
		idLinkedList *firstMissingArg=callable->args;
		char *missingArgs=strdup(stringMissingArgs(firstMissingArg));
		printf("ERROR!(line %d) %s is missing args: %s.\n",yylineno,$1,missingArgs);
		exit(1);
	}
	$$=mknode2();$$->original=mknode($1,NULL,NULL);
	$$->clean=mknode(call,NULL,mknode("skip\0",mknode($1,NULL,NULL),NULL));
	$$->clean->varsSize=vSize;}

	| idT '(' CALLARG ')' ';' {
	char *argType=strdup(getTypeOfCallArg($3));
	callableExistsOrExit($1);
	if(!strcmp(argType,"VAR\0")){
		argExistsOrExit($3);
		argType=strdup(getType($3));
	}
	//next code will get the callable and compare the requested arg type (from decleration) 
	//with given arg type (from call)
	idLinkedList *callable;
	int notFunc=find2($1,"Func\0");
	char *call;
	int vSize = 0;
	if(notFunc){
		callable=getIdLink($1,"Proc\0");
		call = strdup("PCALL\0");
	}else{
		callable=getIdLink($1,"Func\0");
		call = strdup("FCALL\0");
		vSize=getTypeSize(callable->returnType);
	}
	idLinkedList *arg=callable->args;
	if(strcmp(arg->type,argType)){
		printf("ERROR!(line %d) Called %s with %s (%s) instead of requested argument %s (%s).\n",yylineno,$1,$3,argType,arg->key,arg->type);
		exit(1);
	}

	//this "if" checks for missing arguments
	if(arg->args){
		char *missingArgs=strdup(stringMissingArgs(arg->args));
		printf("ERROR!(line %d) %s is missing args: %s.\n",yylineno,$1,missingArgs);
		exit(1);
	}
	$$=mknode2();$$->original=mknode(
		$1,
		mknode(
			$3,
			NULL,
			NULL
		),
		NULL
	);
	$$->clean=mknode(call,NULL,mknode("skip\0",mknode($1,NULL,NULL),mknode($3,NULL,NULL)));
	$$->clean->varsSize=vSize;}

	| idT '(' CALLARG CALLARGLIST ')' ';' {
	callableExistsOrExit($1);
	char *givenArgType=strdup(getTypeOfCallArg($3));
	if(!strcmp(givenArgType,"VAR\0")){
		argExistsOrExit($3);
		givenArgType=strdup(getType($3));
	}
	node *argsNode = mknode($3,NULL,NULL);
	//next code will get the callable and compare the requested arg type (from decleration) 
	//with given arg type (from call)
	idLinkedList *callable;
	int notFunc=find2($1,"Func\0");
	char *call;
	int vSize = 0;
	if(notFunc){
		callable=getIdLink($1,"Proc\0");
		call = strdup("PCALL\0");
	}else{
		callable=getIdLink($1,"Func\0");
		call = strdup("FCALL\0");
		vSize=getTypeSize(callable->returnType);
	}
	if(callable->args==NULL){
		printf("ERROR!(line %d) Callable %s was given arguments when it does not receive any, or was defined recursively.\n",yylineno,$1);
		exit(1);
	}
	idLinkedList *declaredArg=callable->args;
	if(strcmp(declaredArg->type,givenArgType)){
		printf("ERROR!(line %d) Called %s with %s (%s) instead of requested argument %s (%s).\n",yylineno,$1,$3,givenArgType,declaredArg->key,declaredArg->type);
		exit(1);
	}

	char *list=strdup($4);
	char *nextGivenArg = strtok (list," ");
	char *type2;
	idLinkedList *nextDeclaredArg=declaredArg->args;
	while(nextGivenArg != NULL){
		type2=strdup(getTypeOfCallArg(nextGivenArg));
		if(!strcmp(type2,"VAR\0")){
			argExistsOrExit(nextGivenArg);
			givenArgType=getType(nextGivenArg);
		}else{
			givenArgType=type2;
		}
		if(nextDeclaredArg==NULL){
			printf("ERROR!(line %d) Too many arguments given.\n",yylineno);
			exit(1);
		}
		if(strcmp(nextDeclaredArg->type,givenArgType)){
			printf("ERROR!(line %d) Called %s with %s (%s) instead of requested argument %s (%s).\n",yylineno,$1,nextGivenArg,givenArgType,nextDeclaredArg->key,nextDeclaredArg->type);
			exit(1);
		}
		argsNode = mknode(nextGivenArg,NULL,argsNode);
		nextGivenArg = strtok(NULL," ");
		nextDeclaredArg=nextDeclaredArg->args;
	}
	if(nextDeclaredArg){
		char *missingArgs=strdup(stringMissingArgs(nextDeclaredArg));
		printf("ERROR!(line %d) %s is missing args: %s.\n",yylineno,$1,missingArgs);
		exit(1);
	}
	$$=mknode2();$$->original=mknode(
		$1,
		mknode(
			$3,
			NULL,
			NULL
		),
		mknode(
			$4,
			NULL,
			NULL
		)
	);
	$$->clean=mknode(call,NULL,mknode("skip\0",mknode($1,NULL,NULL),argsNode));
	$$->clean->varsSize = vSize;
					/*char *a2=strdup("(ARGS \0")
					strcat(a2,$3)strcat(a2,$4);
					strcat(a2,")\0");
					int funcNotExist=find2($1,"Func");
					int procNotExist=find2($1,"Proc");
					if(funcNotExist && procNotExist){
						printf("ERROR!(line %d) proc\\func %s does not exist\n",yylineno,$1);
					}
					char *a=strdup("(CALL \0");
					strcat(a,$1);
					$$=mknode2();$$->original=mknode("skip\0",mknode(a,mknode(a2,NULL,NULL),NULL),mknode(")\0",NULL,NULL));
					*/};


%%
#include "lex.yy.c"
main()
{
	return yyparse();
}
node *mknode(char *token,node *left,node *right)
{
	node *newnode = (node*)malloc(sizeof(node));
	char *newstr = (char*)malloc(sizeof(token) + 1);
	strcpy(newstr,token);
	newnode->left = left;
	newnode->right = right;
	newnode->token = newstr;
	return newnode;
}
node2 *mknode2()
{
	node2 *newnode = (node2*)malloc(sizeof(node2));
	return newnode;
}
void printtree(node *tree)
{
	char skip[5] = {'s','k','i','p','\0'};
	if(strcmp(skip,tree->token)){
		printtabs();
		printf("%s\n", tree->token);
	}
	if(tree->left){
		if(strcmp(skip,tree->token)){
			counter++;			
		}
		printtree(tree->left);
		if(strcmp(skip,tree->token))counter--;			
	}
	if(tree->right){
		if(strcmp(skip,tree->token)){
			counter++;			
		}
		printtree(tree->right);
		if(strcmp(skip,tree->token))counter--;			
	}
}
void printtreeAll(node *tree)
{
	if(1){
		printtabs();
		printf("%s\n", tree->token);
	}
	if(tree->left){
		if(1){
			counter++;			
		}
		printtreeAll(tree->left);
		if(1)counter--;			
	}else{
		counter++;
		printtabs();
		counter--;
		printf("NULL\n");
	}
	if(tree->right){
		if(1){
			counter++;			
		}
		printtreeAll(tree->right);
		if(1)counter--;			
	}else{
		counter++;
		printtabs();
		counter--;
		printf("NULL\n");
	}
}
node* leftMost(node *tree){
	node *temp=tree;
	while(temp->left){
		temp=temp->left;
	}
	return temp;
}
node* rightMost(node *tree){
	node *temp=tree;
	while(temp->right){
		temp=temp->right;
	}
	return temp;
}
char* freshLabel(){
	char num[9];
	num[8]='\0';
	sprintf(num,"%d",labelCounter);
	char *label = strdup("_L\0");
	strcat(label,num);
	labelCounter++;
	return label;
}
char* freshVar(){
	char num[9];
	num[8]='\0';
	sprintf(num,"%d",varCounter);
	char *var = strdup("_t\0");
	strcat(var,num);
	varCounter++;
	return var;
}
void labelNodes(node *tree){
	if(tree->left){
		labelNodes(tree->left);
	}
	if(tree->right){
		labelNodes(tree->right);
	}
	if(!strcmp(tree->token,"IF\0")){
		char *label = freshLabel();
		tree->right->left->falseLabel = label;
		tree->right->right->endLabel = label;
	}
	if(tree->left && tree->right){
		if(!strcmp(tree->left->token,"IF\0") && !strcmp(tree->right->token,"ELSE\0")){
			char *label = freshLabel();
			tree->left->right->right->nextLabel = label;
			tree->right->right->endLabel = label;
		}
		if(isNotKeyWord(tree->token) && strcmp(tree->token,"=\0")){
			tree->var = freshVar();
		}
	}else{
		if(0){
			node* callableStart = getFirstNonKeywordNode(tree);
			printf("+++%s %s\n",callableStart->token,tree->token);
			if(callableStart->startLabel){
				char *lb = strdup(tree->startLabel);
				strcat(lb,":\n");
				strcat(lb,callableStart->startLabel);
				callableStart->startLabel = lb;
			}else{
				callableStart->startLabel = strdup(tree->startLabel);
			}
			
			if(tree->varsSize){
				printf("@+++ %d %d\n",callableStart->varsSize,tree->varsSize);
				callableStart->varsSize=tree->varsSize;
			}
			free(tree->startLabel);tree->startLabel=NULL;
			node* callableEnd = getLastNonKeywordNode(tree);
			callableEnd->endFunc = 1;
		}else if(tree->right && isNotKeyWord(tree->token) && strcmp(tree->token,"RETURN\0") && strcmp(tree->token,"PCALL\0")){
			tree->var = freshVar();
		}else{
			tree->var = tree->token;
		}
	}
	if(!strcmp(tree->token,"WHILE\0")){
		char *label = freshLabel();
		tree->right->left->startLabel = label;
		tree->nextLabel = label;
		char *label2 = freshLabel();
		tree->right->left->falseLabel = label2;
		tree->endLabel = label2;
	}
}
node* getFirstNonKeywordNode(node* tree){
	node* temp = tree;
	while(1){
		if(temp->left){
			temp = temp->left;
		}else if(temp->right){
			temp = temp->right;
		}else{
			return temp;
		}
	}
}

node* getLastNonKeywordNode(node *tree){
	node *temp=tree;
	if(tree->right)temp=tree->right;
	while(1){
		if(!strcmp(temp->token,"skip\0") && temp->right){
			temp=temp->right;
		}else if(!strcmp(temp->token,"skip\0") && temp->left){
			temp=temp->left;
		}else{
			return temp;
		}
	}
}
int isNotKeyWord(char *word){
	return (strcmp(word,"skip\0") && strcmp(word,"IF\0") && strcmp(word,"ELSE\0") && strcmp(word,"WHILE\0") && strcmp(word,"PROC\0") && strcmp(word,"FUNC\0"));
}
int getTypeSize(char *type){
	if(!strcmp(type,"INT\0")){
		return 4;
	}else if(!strcmp(type,"CHAR\0") || !strcmp(type,"BOOL\0")){
		return 1;
	}else if(!strcmp(type,"REAL\0") || !strcmp(type,"REALPOINTER\0") || !strcmp(type,"INTPOINTER\0") || !strcmp(type,"CHARPOINTER\0")){
		return 8;
	}else{
		return 4;
	}
}
int getSizeOfCallableVars(char* callable, node *tree){
	int size = 0;
	if(!strcmp(tree->token,"(FUNC\0") || !strcmp(tree->token,"(PROC\0")){
		if(!strcmp(tree->left->left->token,callable)){
			varsFinderCounter = 0;
		}
	}
	if(varsFinderCounter==0 && strlen(tree->token)>=8){
		char *temp=strdup("\0");
		strncpy(temp,tree->token,4);
		if(!strcmp(temp,"(VAR\0")){
			if(tree->token[5]=='I'){
				if(tree->token[8]=='P'){
					size+=8;
				}else{
					size+=4;
				}
			}else if(tree->token[5]=='C'){
				if(tree->token[9]=='P'){
					size+=8;
				}else{
					size+=1;
				}
			}else if(tree->token[5]=='R'){
				size+=8;
			}else{
				size+=4;
			}
		}
		free(temp);
	}
	if(tree->left){
		if(varsFinderCounter==0){
			if(strcmp(tree->left->token,"(PROC\0") && strcmp(tree->left->token,"(FUNC\0")){
				if(tree->left->left){
					if(strcmp(tree->left->left->token,"(PROC\0") && strcmp(tree->left->left->token,"(FUNC\0")){
						size+=getSizeOfCallableVars(callable,tree->left);
					}
				}
			}
		}else{
			size+=getSizeOfCallableVars(callable,tree->left);
		}
	}
	if(tree->right){
		if(varsFinderCounter==0){
			if(strcmp(tree->right->token,"(PROC\0") && strcmp(tree->right->token,"(FUNC\0")){
				if(tree->right->left){
					if(strcmp(tree->right->left->token,"(PROC\0") && strcmp(tree->right->left->token,"(FUNC\0")){
						size+=getSizeOfCallableVars(callable,tree->right);
					}
				}
			}
		}else{
			size+=getSizeOfCallableVars(callable,tree->right);
		}
	}
}
node* getMinimalTree(node *left,node *right){
	if(!left && !right)return NULL;
	if(left && right)return mknode("skip\0",left,right);
	if(left){
		return left;
	}else{
		return right;
	}
}

void genCode(node *tree)
{
	if(!strcmp(tree->token,"PROC\0") || !strcmp(tree->token,"FUNC\0")){
		printf("%s:\n\tBeginFunc %d;\n",tree->startLabel,tree->varsSize);
		tree->endFunc=1;
	}
	if(tree->left){
		genCode(tree->left);
	}
	if(tree->right){
		genCode(tree->right);
	}
	if(isNotKeyWord(tree->token)){
		if(0){
			printf("%s:\n",tree->startLabel);
			if(searchScopes(firstScope,tree->startLabel,"Func\0") || searchScopes(firstScope,tree->startLabel,"Proc\0")){
				printf("\tBeginFunc %d;\n",tree->varsSize);
			}
		}

		if(tree->left){
			if(!strcmp(tree->token,"=\0")){
				printf("\t%s = %s;\n",tree->left->var,tree->right->var);
			}else{
				printf("\t%s = %s %s %s;\n",tree->var,tree->left->var,tree->token,tree->right->var);
			}
		}else{
			if(!strcmp(tree->token,"FCALL\0")){
				int i = 0;
				if(tree->right->right){
					node *arg = tree->right->right;
					while(arg){
						printf("\tPushParam %s;\n",arg->token);
						arg = arg->right;
					}					
				}
				printf("\t%s = LCall %s;\n",tree->var,tree->right->left->token);
				idLinkedList *callable = getIdLink(tree->right->left->token,"Func\0");
				idLinkedList *arg = callable->args;
				while(arg){
					i+=getTypeSize(arg->type);
					arg = arg->args;
				}
				if(i>0)printf("\tPopParams %d;\n",i);
			}else if(!strcmp(tree->token,"PCALL\0")){
				int i = 0;
				if(tree->right->right){
					i = 1;
					node *arg = tree->right->right;
					while(arg){
						printf("\tPushParam %s;\n",arg->token);
						arg = arg->right;
					}					
				}
				printf("\tLCall %s;\n",tree->right->left->token);
				idLinkedList *callable = getIdLink(tree->right->left->token,"Proc\0");
				idLinkedList *arg = callable->args;
				while(arg){
					i+=getTypeSize(arg->type);
					arg = arg->args;
				}
				if(i>0)printf("\tPopParams %d;\n",i);
			}else if(tree->right){
				if(!strcmp(tree->token,"RETURN\0")){
					printf("\tRETURN %s;\n",tree->right->var);
				}else if(!strcmp(tree->token,"-\0") || !strcmp(tree->token,"^\0") || !strcmp(tree->token,"&\0")){
					printf("\t%s = %s %s;\n",tree->var,tree->token,tree->right->var);
				}
			}
		}
		if(tree->falseLabel) printf("\tIFZ %s Goto %s;\n",tree->var,tree->falseLabel);


	}
	if(tree->nextLabel) printf("\tGoto %s;\n",tree->nextLabel);
	if(tree->endLabel) printf("%s:\n",tree->endLabel);
	if(tree->endFunc) printf("\tEndFunc;\n");
}
void printtabs(){
	int i = 0;
	while(i<counter){
		printf("  ");
		i++;
	}
}

int checkIfIdExistAtCurrentScope(char *name){
	idLinkedList *item = highestScope->id;
	while(item!=NULL){
		if(!(strcmp(item->key,name))){
			if(!strcmp(item->type,"Proc")) return 0;
			if(!strcmp(item->type,"Func")) return 0;
		}
		item = item->next;
	}
	return 1;
}

int checkIfVarExistAtCurrentScope(char *name){
	idLinkedList *item = highestScope->id;
	while(item!=NULL){
		if((!(strcmp(item->key,name))) && strcmp(item->type,"Proc") && strcmp(item->type,"Func")){
			return 0;
		}
		item = item->next;
	}
	return 1;
}

idLinkedList* declareId(char* name,char* type){
	//if(!checkIfIdExistAtCurrentScope(name)){return 0;}
	idLinkedList *newItem= (idLinkedList*)malloc(sizeof(struct idLinkedList));
	newItem->type = strdup(type);
	newItem->key = strdup(name);
	newItem->next = NULL;
	if(highestScope->id==NULL){
		highestScope->id = newItem;
		return newItem;
	}
	idLinkedList *item = highestScope->id;
	while(item->next!=NULL){
		item = item->next;
	}
	item->next = newItem;
	return newItem;
}
int find(scopeLinkedList *tree,char *name,char *type){
	idLinkedList *temp = tree->id;
	while(temp){
		if(!(strcmp(temp->key,name))){if(!(strcmp(temp->type,type)))return 0;}
		if(temp->nextscope){if(find(temp->nextscope,name,type)==0) return 0;}
		temp = temp->next;
	}
	return 1;
}

int find2(char *name,char *type){
	scopeLinkedList *t2 = highestScope;
	while(t2){
		idLinkedList *temp = t2->id;
		while(temp){
			if(!(strcmp(temp->key,name))){if(!(strcmp(temp->type,type)))return 0;}
			//if(temp->nextscope){if(find(temp->nextscope,name,type)==0) return 0;}
			temp = temp->next;
		}
		t2=t2->parent;
	}
	return 1;
}

int find3(char *name){
	scopeLinkedList *t2 = highestScope;
	while(t2){
		idLinkedList *temp = t2->id;
		while(temp){
			if(!(strcmp(temp->key,name))){return 0;}
			temp = temp->next;
		}
		t2=t2->parent;
	}
	return 1;
}

int searchScopes(scopeLinkedList *scope,char *name,char *type){
	if(scope){
		idLinkedList *temp = scope->id;
		while(temp){
			if(!(strcmp(temp->key,name))){if(!strcmp(temp->type,type))return 1;}
			if(temp->nextscope){
				if(searchScopes(temp->nextscope,name,type))return 1;
			}
			//if(temp->nextscope){if(find(temp->nextscope,name,type)==0) return 0;}
			temp = temp->next;
		}
	}
	return 0;
}

void addNewScope(){
		scopeLinkedList *newScope= (scopeLinkedList*)malloc(sizeof(struct scopeLinkedList));
		newScope->id = NULL;
		newScope->parent = highestScope;
		highestScope = newScope;
}

void removeLastScope(){
	/*//freeMemoryofDeclareations();
	scopeLinkedList *temp = highestScope;
	printscopes(highestScope);
	highestScope = highestScope->prev;
	//free(highestScope->next);
	highestScope->next = NULL; //TODO: improve the remove.
	free(temp);*/
	highestScope = highestScope->parent;
}
idLinkedList *getIdLink(char* name, char* type){
	scopeLinkedList *t2 = highestScope;
	while(t2){
		idLinkedList *temp = t2->id;
		while(temp){
			if(!strcmp(temp->key,name)){if(!strcmp(temp->type,type))return temp;}
			temp=temp->next;
		}
		t2=t2->parent;
	}
	return NULL;
}
void addTempArgs(idLinkedList* link){
	if(!currentArgs){
		currentArgs=1;
		tempArgs=link;
		return;
	}
	idLinkedList *temp=tempArgs;
	while(temp->args){
		temp=temp->args;
	}
	temp->args=link;
}
char* getType(char *name){
	scopeLinkedList *currentScope = highestScope;
	while(1){
		idLinkedList *item = currentScope->id;
		if(item!=NULL){
			while(1){
				if(!strcmp(item->key,name)){return item->type;}
				if(item->next==NULL){break;}
				item = item->next;
			}
		}
		if(currentScope->parent){
			currentScope=currentScope->parent;
		}else{
			return NULL;
		}
	}
}
int checkIdList(char arr[10][10], char* list){
	char *ptr = strtok(list, " ");
	int i=0;
	while(ptr!=NULL){
		//int len = strlen(ptr);
		//printf("LEN:%d\n",len);
		strcpy(arr[i],ptr);
		//arr[i][len]='\0';
		ptr = strtok(NULL," ");
		i++;
	}
	int j=0;
//	while(j<i){
//		printf("%s\n",arr[j]);
//		j++;
//	}
	return i;
}
void saveArgsData(idLinkedList *callable){
	if(currentArgs){
		idLinkedList *tArgs = tempArgs;
		idLinkedList *cArgs = callable;
		cArgs->args=tArgs;
		while(tArgs->args){
			tArgs=tArgs->args;
			cArgs=cArgs->args;
			cArgs->args=tArgs;
		}
		tempArgs=NULL;
		currentArgs=0;
	}
}

char* stringMissingArgs(idLinkedList *firstMissingArg){
	idLinkedList *temp=firstMissingArg;
	char *missingArgs=strdup(temp->key);
	strcat(missingArgs,"(\0");
	strcat(missingArgs,temp->type);
	strcat(missingArgs,")\0");
	while(temp->args){
		temp=temp->args;
		strcat(missingArgs," \0");
		strcat(missingArgs,temp->key);
		strcat(missingArgs,"(\0");
		strcat(missingArgs,temp->type);
		strcat(missingArgs,")\0");
	}
	return missingArgs;
}
int getNumFromStrType(char *strType){
	int i=0;
	char temp=strType[0];
	char *num=strdup("\0");
	while(strType[i]!='['){
		i=i+1;
	}
	i=i+1;
	while(strType[i]!=']'){		
		temp=strType[i];
		strncat(num,&temp,1);
		i=i+1;
	}
	int ans=atoi(num);
	return ans;
}
int typeIsString(char *type){
	if(strlen(type)<7){return 0;}
	char *typeStart=strdup("\0");
	strncpy(typeStart,type,6);
	if(!strcmp(typeStart,"STRING\0")){return 1;}
	return 0;
}
void callableExistsOrExit(char* callableName){
	int fNotExist=find2(callableName,"Func\0");
	int pNotExist=find2(callableName,"Proc\0");
	if(fNotExist && pNotExist){
		printf("ERROR!(line %d) no function or procedure with the id %s was found.\n",yylineno,callableName);
		exit(1);
	}
}
void argExistsOrExit(char* arg){
	int argNotExist=find3(arg);
	if(argNotExist){
		printf("ERROR!(line %d) argument %s was not found.\n",yylineno,arg);
		exit(1);
	}
}

char* getTypeOfCallArg(char* arg){
	char *type;
	if(!strcmp(arg,"TRUE\0") || !strcmp(arg,"FALSE\0")){
		type=strdup("BOOL\0");
		return type;
	}
	if(arg[0]=='\''){
		type=strdup("CHAR\0");
		return type;
	}
	if(arg[0]=='|'){
		type=strdup("INT\0");
		return type;
	}
	int i=0;
	while(arg[i]){
		if(arg[i]=='.'){
			type=strdup("REAL\0");
			return type;
		}
		i++;
	}
	if(arg[0]>=48 && arg[0]<=57){
		type=strdup("INT\0");
		return type;
	}
	type=strdup("VAR\0");
	return type;
}

void validSubExp(char *exp){
	char *type=strdup(getTypeOfCallArg(exp));
	if(strcmp(type,"VAR\0") && strcmp(type,"INT\0") && strcmp(type,"REAL\0")){
		printf("ERROR!(line %d) Type must be a number, not %s.\n",yylineno,type);
		exit(1);
	}
	if(!strcmp(type,"VAR\0")){
		type=strdup(getType(exp));
		if(!strcmp(type,"INT")) ;
		else if(!strcmp(type,"REAL")) isReal = true;
		else {
			printf("ERROR!(line %d) %s Type Is Not Int OR Real.\n",yylineno,type);
			exit(1);
		}
	}
}

void printscopes(scopeLinkedList *tree)
{
	idLinkedList *temp = tree->id;
	printcurrentscope(tree->id);
	printf("\n");
	while(temp) {if(temp->nextscope) printscopes(temp->nextscope); temp = temp->next;}
}

void printcurrentscope(idLinkedList *tree)
{
	printf("-%s   %s  ",tree->key,tree->type);
	if(tree->next){
		printcurrentscope(tree->next);			
	}
}

int yyerror(char *s)
{
	fprintf(stderr, "Syntax ERROR!(line %d)in line %d: %s: %s\n",yylineno, yylineno, s,yytext);
	return 0;
}
