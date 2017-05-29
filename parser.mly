%{


open Ast

%}

%token <string> Identifier
%token <int> Integ
%token <string> Filename
%token PlusS
%token IfS Then Else
%token New SkipS Letk In
%token ConnectS AcceptS From To As
%token OutputS InputS
%token NewPrinS RegisterS ReleaseS Encr
%token DecryptS 
%token LeftB RightB LeftP RightP LeftSB RightSB LeftA RightA
%token SC Colon Equals LessThan Comma Parallel BangS
%token Publ Bottom
%token ArrayType PrivKeyEncType EncrType IntegerType PublKeyType ChanType
%token EOF LoadS PrincipalS
%token DeviceS TypeCheckS ReduceS ExitS

%start main

%type <Ast.command> main

%%

main:
 | startcommand EOF { $1 }


startcommand:
 | command {$1}
 | LoadS PrincipalS Identifier From Integ SC command {Load($3,$5,$7)}
 | LoadS Identifier Colon baseType From Integ SC command {LoadVar($2,$6,$4,$8)}


command:
 | LeftB command RightB {$2}
 | IfS LeftP expr Equals expr RightP Then command elseBranch { If ($3,$5,$8,$9) }
 | IfS LeftP expr LessThan expr RightP Then command elseBranch { IfLess ($3,$5,$8,$9) }
 | New Identifier Colon baseType rights Equals expr SC command { NewVar($2,Type($4,$5),$7,$9) }
 | Identifier Colon Equals expr SC command { Assign($1,$4,$6)}
 | Identifier LeftSB expr RightSB Colon Equals expr SC command { AssignIndex($1,$3,$7,$9) }
 | Letk Identifier Equals expr In command { Deref($2,$4,$6) }
 | command Parallel command { Paral($1,$3) }
 | SkipS { Skip }
 | {Skip}
 | BangS command { Bang($2)}
 | ConnectS Identifier Colon chanType SC command { Connect(Ch($2),$4,0,$6)  }
 | AcceptS Identifier Colon chanType SC command {Accept(Ch($2),$4,0,$6) }
 | ConnectS Identifier Colon chanType To Identifier As Identifier SC command {  ConnectFor(Ch($2),$4,$6,$8,0,$10)}
 | AcceptS Identifier Colon chanType From Identifier As Identifier SC command {AcceptFor(Ch($2),$4,$6,$8,0,$10)}
 | OutputS Identifier LeftA expr RightA SC command { Output(Ch($2),$4,$7) }
 | InputS Identifier LeftP Identifier RightP SC command { Input(Ch($2),$4,$7)}
 | NewPrinS Identifier LeftB rightsList RightB SC command {NewPrin($2,$4,$7)}
 | DecryptS Identifier expr As Identifier Colon baseType rights Then command Else command { Decrypt($2,$3,$5,Type($7,$8),$10,$12)}
 | RegisterS Identifier expr As Identifier Then command Else command   {Register($2,$3,$5,$7,$9)}

elseBranch:
 | Else command {$2}
 | { Skip }

expr:
 | Identifier {Var($1)}
 | Publ LeftP Identifier RightP { PubOf($3) }
 | ReleaseS LeftP Identifier RightP { Release($3) }
 | Encr LeftB rightsList RightB LeftP expr RightP { Encrypt($3,$6) }
 | LeftB exprList RightB { TupleE($2) }
 | Identifier LeftSB expr RightSB { Element($1,$3) }
 | Integ {Int($1)}
 | expr PlusS expr {Plus($1,$3)}

baseType:
 | PublKeyType {Pubkey}
 | PrivKeyEncType {PrivKey}
 | IntegerType {Number}
 | EncrType LeftB baseType RightB {CipherType($3)}
 | ArrayType LeftB baseType RightB {Array($3)}

chanType:
 | ChanType LeftP baseType rights RightP rights {Chan(Type($3,$4),$6)}

rights: 
 | Bottom { Public}
 | LeftB rightsList RightB { Set($2) }

rightsList:
 | {[]}
 | right { [$1] }
 | right Comma rightsList { $1 :: $3}

right:
 | Identifier { Key($1)}
 | Publ LeftP Identifier RightP { Pub($3) }
 
exprList:
 | expr { [$1] }
 | expr Comma exprList { $1 :: $3}


%%
