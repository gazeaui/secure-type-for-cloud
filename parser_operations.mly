%{



open Printers
open Typechecker
open Reductions
open Ast

let processus = ref (Process([],CSet([]),[]))
let principals = ref []
let keyctx = ref []
let channels = ref []
let contexts = ref []
let labels = ref []
let count_intern = ref 0

let load_file filename =
  let file = open_in filename in
  let lexbuf = Lexing.from_channel file in
  try
    let cmd = (Parser.main Lexer.token lexbuf) in
    close_in file ;
	let Process(_,_,ds) = ! processus in 
	Printf.printf "> adding device %d : %s\n" (List.length ds) filename;
    processus := add_device !processus  cmd 

  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      Printf.printf "Syntax error at line %d, column %d!\n" line cnum ;
      exit 1 
%}

%token <string> Identifier
%token <int> Integ
%token <string> Filename
%token IfS Then Else
%token New SkipS 
%token ConnectS AcceptS From To As
%token OutputS InputS
%token NewPrinS RegisterS ReleaseS Encr
%token DecryptS 
%token LeftB RightB LeftP RightP LeftSB RightSB LeftA RightA
%token SC Colon Equals Comma Parallel BangS
%token Publ Bottom
%token ArrayType PrivKeyEncType EncrType IntegerType PublKeyType ChanType
%token EOF LoadS PrincipalS
%token DeviceS TypeCheckS ReduceS ExitS PrintS AllS SmallS SelectS ThreadS StopS AddS
%token AttackS PublicS With KeyS TraceS PlusS
%token FreshKeyS AlterS SecretS

%start main

%type <unit> main

%%

main:
 | operations_lst EOF { () }

operations_lst:
 | operation SC operations_lst { ()}
 |  ExitS { Printf.printf "bye \n"}

operation: 
 | AddS DeviceS Filename  { load_file $3}
 | TypeCheckS {
	Printf.printf "> type-checking: " ;
	try typecheck_all !principals !channels !keyctx !contexts !processus;
		 Printf.printf "All devices are well-typed !\n"
	with | Type_Failure(id) -> Printf.printf "\n \n Device %d does not type check !!! \n \n" id}
 | ReduceS { let(process,prin,ch,keys,ctx,move)= one_step true !channels !processus in
   begin 
   principals := prin @ !principals; 
   channels := ch @ !channels; 
   contexts := ctx @ !contexts; 
   keyctx := keys @ !keyctx;
   processus := process;
   count_intern := !count_intern + 1;
   Printf.printf "> %d-th internal reduction.\n" !count_intern;
   end}
 | PrintS AllS {print_processus !processus}
 | PrintS SmallS {print_processus_mini !processus}
 | SelectS DeviceS Integ {processus := device_on_top !processus $3;Printf.printf "> Now, device %d is reduced \n" $3}
 | StopS ThreadS {processus := thread_at_end !processus ;Printf.printf "> active thread at the end of the queue. \n"}
 | AttackS attackType {let(process,prin,ch,ctx,label)= attacker !channels !processus $2 in
 begin 
   labels := label :: !labels; 
   principals := prin @ !principals; 
   channels := ch @ !channels; 
   contexts := ctx @ !contexts; 
   processus := process;
   Printf.printf "> labelled reduction: %s .\n" (print_label label) end }
 | PrintS TraceS {print_trace !labels}

attackType:
 | PublicS {AttackPublic}
 | OutputS expr{AttackOutput($2)}
 | InputS  {AttackInput}


expr:
 | Identifier {AVar($1)}
 | Encr expr LeftP expr RightP { AEncrypt($2,$4) }
 | LeftB exprList RightB { ATupleE($2) }
 | expr LeftSB expr RightSB { AElement($1,$3) }
 | Integ {AInt($1)}
 | expr PlusS expr {APlus($1,$3)}
 | FreshKeyS LeftP Integ RightP {AFreshPrin($3)}
 | AlterS expr With expr {Alter($2,$4)}
 | SecretS From expr {ASecOf($3)}

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
