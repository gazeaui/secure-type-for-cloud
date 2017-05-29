open Lexer
open Parser
open Ast
open Printers



	

let ex1 = (
	NewPrin("Alice",[],NewPrin("Bob",[],
	NewVar("x",Type(Number,Set([Pub("Alice")])),Int(5),
	NewVar("y",Type(Number,Set([Pub("Alice");Pub("Bob")])),Int(7),
	Assign("x",Var("y"),Skip))))))

let ex2 = (
	NewPrin("Alice",[],
	NewPrin("Bob",[],NewVar("x",Type(Number,Set([Pub("Alice")])),Int(5),
	NewVar("y",Type(Number,Set([Pub("Alice");Pub("Bob")])),Int(7),
	If(Var("x"),Int(1),
		Assign("y",Int(1),Skip),
		Skip))))))

let alice =
	NewPrin("Alice",[],
	Connect(Ch("aFriend"),Chan(Type(Pubkey,Public),Public),0,
	Input(Ch("aFriend"),"friend",
	Output(Ch("aFriend"),PubOf("Alice"),
	Connect(Ch("myId"),Chan(Type(Array(Pubkey),Public),Public),1,
	Output(Ch("myId"),TupleE([PubOf("Alice");Var("friend")]),
	ConnectFor(Ch("upload"),Chan(Type(Number,Set([Pub("Alice");Key("friend");Key("srv")])),Public),"srv","Alice",2,
	NewVar("secret",Type(Number,Set([Pub("Alice");Key("friend");Key("srv")])),Int(42),
	Output(Ch("upload"),Var("secret"),
	Skip)))))))))
	
let bob =
	NewPrin("Bob",[],
	Accept(Ch("IamBob"),Chan(Type(Pubkey,Public),Public),0,
	Output(Ch("IamBob"),PubOf("Bob"),
	Input(Ch("IamBob"),"you",
	ConnectFor(Ch("download"),Chan(Type(Number,Set([Pub("Bob");Key("you");Key("srv")])),Public),"srv","Bob",3,
	Input(Ch("download"),"code",
	Skip))))))
	
let checkUsage = Skip

let serveClient client1 client2 client =
	Paral(
		(*Bang( *)
		AcceptFor(Ch("upload"),Chan(Type(Number,Set([Pub("Server");Key(client1);Key(client2)])),Public),client,"Server",2,
		If(Element("blocked",Var("accountID")),Int(0),
			Input(Ch("upload"),"z",
			AssignIndex("usage",Var("accountID"),Plus(Element("usage",Var("accountID")),Int(1)),
			Assign("data",Var("z"),
			Skip))),
			Skip)),
		(*Bang( *)
		AcceptFor(Ch("download"),Chan(Type(Number,Set([Pub("Server");Key(client1);Key(client2)])),Public),client,"Server",3,
		If(Element("blocked",Var("accountID")),Int(0),
			AssignIndex("usage",Var("accountID"),Plus(Element("usage",Var("accountID")),Int(1)),
			Output(Ch("download"),Var("data"),
			Skip)),
			Skip)))

let registerUsers = 
	(*Bang( *)
	Accept(Ch("newUsers"),Chan(Type(Array(Pubkey),Public),Public),1,
	Input(Ch("newUsers"),"cl1cl2",
	NewVar("client1",Type(Pubkey,Public),Element("cl1cl2",Int(0)),
	NewVar("client2",Type(Pubkey,Public),Element("cl1cl2",Int(1)),
	NewVar("accountID",Type(Number,Public),Var("nextId"),
	Assign("nextId",Plus(Var("nextId"),Int(1)),
	NewVar("data",Type(Number,Set([Pub("Server");Key("client1");Key("client2")])),Int(0),
	Paral(serveClient "client1" "client2" "client1", serveClient "client1" "client2" "client2"))))))))

let server = 
	NewVar("usage",Type(Array(Number),Public),TupleE([(Int(0));(Int(0));(Int(0))]), 
	NewVar("blocked",Type(Array(Number),Public),TupleE([(Int(0));(Int(0));(Int(0))]), 
	NewVar("nextId",Type(Number,Public),Int(0),
	Paral(registerUsers,checkUsage))))

        


(*let hard_tests ()=
	let prins =  ["Server"] in
	let chans =  [] in
	let ctx =  [("srv",Type(Pubkey,Public))] in
	let process= (Process([],(CSet([Pk(-1)])),[Dev([Loc("srv",Low,(PKey(Pk(-1)),Low))],[(bob,Low)],3);Dev([Loc("srv",Low,(PKey(Pk(-1)),Low))],[(alice,Low)],2);(Dev([Prin("Server",Principal(-2,Pk(-1),[]))],[(server,Low)],1))])) in
	reduce 10 prins chans ctx process*)
	
let usage = Printf.sprintf
  "Usage: %s [options] < specification-file.api"
  (Filename.basename Sys.argv.(0))

let command_line_options_list = [(*
  ("--verbose", Arg.Unit (fun () -> verbose_output := true),
   "Enable verbose output");
  ("-verbose", Arg.Unit (fun () -> verbose_output := true),
   "Enable verbose output");
  ("-debug", Arg.Unit (fun () -> debug_output := true),
   "Enable debug output");
  ("--debug", Arg.Unit (fun () -> debug_output := true),
   "Enable debug output");
  ("--output-dot", Arg.String (fun s -> dotfile := Some s),
   "<file>  Output statement graph to <file>");
  ("-j", Arg.Int (fun i -> jobs := i),
   "<n>  Use <n> parallel jobs (if supported)");
  ("--ac-compatible", Arg.Set ac_toolbox,
   "Use the AC-compatible toolbox even on non-AC theories (experimental, needs maude and tamarin)");
  ("--tamarin-variants", Arg.Set tamarin_variants,
   "Use tamarin-prover to compute variants in seed statements");
  ("--check-generalizations", Arg.Set check_generalizations,
   "Check that generalizations of kept statements are never dropped.")*)
]

(*let cmdlist =
  let collect arg = Printf.printf "%s\n" usage ; exit 1 in
  let _ = Arg.parse command_line_options_list collect usage in
  let lexbuf = Lexing.from_channel stdin in
  try
    Parser.main Lexer.token lexbuf
  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      Printf.printf "Syntax error at line %d, column %d!\n" line cnum ;
      exit 1*)

let run() =
  let collect arg = Printf.printf "%s\n" usage ; exit 1 in
  let _ = Arg.parse command_line_options_list collect usage in
  let lexbuf = Lexing.from_channel stdin in
  try
    Parser_operations.main Lexer_operations.token lexbuf
  with Parsing.Parse_error ->
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
      Printf.printf "Command error at line %d, column %d!\n" line cnum ;
      exit 1

let () = (*Printf.printf "%s" (print_command server)*)
(*reduce 10 [] [] [] (create_process [cmdlist])*)
	run()