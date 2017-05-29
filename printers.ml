open Ast

let rec print_type_of typ =
	match typ with
	| Number -> "Int"
	| Pubkey -> "PubKey"
	| CipherType(t) -> "Cipher{" ^ (print_type_of t) ^ "}"
	| PrivKey -> "PrivateKey"
	| Array(t) -> "Array{" ^ (print_type_of t) ^ "}"
	
let rec print_lst_rights lst =
	match lst with 
	| Key(k) :: n :: l ->  k ^", "^ (print_lst_rights (n::l))
	| Pub(p) :: n :: l ->  "pub("^p^"), "^ (print_lst_rights (n::l))
	| [Key(k)] -> k
	| [Pub(p)] -> "pub("^p^")"
	| [] -> ""

let rec print_rights rights =
	match rights with
	| Public -> "bot"
	| Set(l) -> "{"^(print_lst_rights l)^"}"

let rec print_concrete_public_key_list lst =
	match lst with
	| Pk(k) :: n :: q -> "PKey("^ (string_of_int k) ^ "), " ^ (print_concrete_public_key_list (n::q))
	| [Pk(k)] -> "PKey("^ (string_of_int k) ^ ") "
	| [] -> ""
	
let print_concrete_rights rights =
	match rights with
	| Anyone -> "Public"
	| CSet(l) -> (List.fold_left (fun i x -> match x with Pk(k) -> i ^ (string_of_int(k)) ^"; ") "{" l)^"}"
	
let print_type typ =
	let Type(s,r)=typ in (print_type_of s)^" "^(print_rights r)

let print_chan_type typ =
	let Chan(t,r)=typ in "Chan("^(print_type t)^") "^(print_rights r)



let rec print_ctx ctx =
	match ctx with
	| [] -> ".\n"
	| (x,t)::l -> x ^ " : " ^ (print_type t) ^ ", " ^ (print_ctx l)

let rec print_prins af =
	match af with
	| [] -> ".\n"
	| p::l -> p ^ ", " ^ (print_prins l)

let print_chan chan =
  match chan with
  | Ch(c) -> c
  | Active(c,_,_) -> c

let rec print_chan_ctx ctx =
	match ctx with
	| [] -> ".\n"
	| (x,t)::l ->(print_chan x) ^ " : " ^ (print_chan_type t) ^ ", " ^ (print_chan_ctx l)

let tag_to_string tag =
	if tag = Low then "Low"
	else "High"
	
let print_principal (Principal(Sk(s),Pk(k),r)) =
	Printf.sprintf "Principal(%d,%d,%s)" s k (print_concrete_public_key_list r)

let rec print_value value = 
	match value with 
	| Integer(i) -> Printf.sprintf "%i" i
	| NaV ->  "naV";
	| Tuple(l) -> (List.fold_left (fun i x -> i ^ (print_value x) ^"; ") "{" l)^"}"
	| Cipher(rs,n,(v,t)) -> Printf.sprintf "Cipher(%s, %d, %s (%s))" (print_concrete_public_key_list rs) n (print_value v) (tag_to_string t)
	| Encapsulation(rs,n,p) -> Printf.sprintf "Encaps(%s, %d, %s)" (print_concrete_public_key_list rs) n (print_principal p)
	| PKey(Pk(k)) -> Printf.sprintf "Key(%i)" k
	| SKey(Sk(k)) -> Printf.sprintf "Sec. Key(%i)" k

let rec print_erased_value value =
	match value with
	| Clear(v) -> print_value v
	| ErasedTuple(v) ->( List.fold_left (fun s v -> s ^ (print_erased_value v)) "{" v)^"}"
	| ObfuscatedCipher(rs,n) -> Printf.sprintf "Ciph(%s, %d, _)" (print_concrete_public_key_list rs) n
	| ClearCipher(rs,n,v) -> Printf.sprintf "Cipher(%s, %d, %s )" (print_concrete_public_key_list rs) n (print_erased_value v) 
	| ObfuscatedEncapsulation(rs,n) -> Printf.sprintf "Encaps(%s, %d, _)" (print_concrete_public_key_list rs) n
	| _ -> assert(false)
	
let rec print_expression exp =
	match exp with
	| Int(v) -> print_value (Integer(v))
	| Var(x) -> x
	| Plus(e1,e2) -> (print_expression e1) ^ "+" ^ (print_expression e2)
	| PubOf(v) -> v
	| Element(x,i) -> x ^ "[" ^ (print_expression i) ^ "]"
	| TupleE(t::l) -> (List.fold_left (fun i x -> i ^ ", " ^ (print_expression x) ) ("{"^(print_expression t)) l)^"}"
	| TupleE([]) -> "{}"
	| Encrypt(r,e) -> "enc "^(print_lst_rights r)^"("^(print_expression e)^")"
	| Release(p) ->  "release("^p^")"
	
let rec print_attacker_expression exp =
	match exp with
	| AInt(v) -> print_value (Integer(v))
	| AVar(x) -> x
	| APlus(e1,e2) -> (print_attacker_expression e1) ^ "+" ^ (print_attacker_expression e2)
	| APubOf(e) -> "pub("^(print_attacker_expression e)^")"
	| ASecOf(e) -> "pub("^(print_attacker_expression e)^")"
	| AElement(x,i) -> (print_attacker_expression x) ^ "[" ^ (print_attacker_expression i) ^ "]"
	| ATupleE(t::l) -> (List.fold_left (fun i x -> i ^ ", " ^ (print_attacker_expression x) ) ("{"^(print_attacker_expression t)) l)^"}"
	| ATupleE([]) -> "{}"
	| AEncrypt(r,e) -> "enc "^(print_attacker_expression r)^"("^(print_attacker_expression e)^")"
	
let rec print_command nbl tab cmd =
	let space=String.make tab '\t' in
	if nbl = 0 then space ^ "..." else
	space ^ (
	match cmd with
	| Skip -> ""
	| Paral(c1,c2) -> Printf.sprintf("{\n%s %s|\n%s\n%s}") (print_command (nbl-1)(tab+1) c1)space (print_command (nbl - 1) (tab+1) c2) space
	| Bang(c) -> Printf.sprintf("! %s ") (print_command (nbl - 1) tab c) 
	| If(e1,e2,c1,c2) -> (Printf.sprintf ("if (%s = %s ) then \n%s")(print_expression e1) (print_expression e2) (print_command (nbl - 1) (tab+1) c1) )^(if c2 != Skip then (Printf.sprintf "\n%selse\n%s" space (print_command (nbl - 1) (tab+1) c2)) else "")
	| IfLess(e1,e2,c1,c2) -> (Printf.sprintf ("if (%s <= %s ) then \n%s")(print_expression e1) (print_expression e2) (print_command (nbl - 1) (tab+1) c1) )^(if c2 != Skip then (Printf.sprintf "\n%selse\n%s" space (print_command (nbl - 1) (tab+1) c2)) else "")
	| NewPrin(p,r,c) -> Printf.sprintf("newPrin %s %s ; \n%s") p (print_rights (Set(r))) (print_command (nbl - 1) tab c) 
	| NewVar(z,t,e,c) -> Printf.sprintf("new %s : %s = %s ; \n%s") z (print_type t)(print_expression e)(print_command (nbl - 1) tab c) 
	| Assign(z,e,c) -> Printf.sprintf("%s := %s ; \n%s") z (print_expression e)(print_command (nbl - 1) tab c) 
	| AssignIndex(z,i,e,c) ->  Printf.sprintf("%s[%s] := %s ; \n%s") z (print_expression i)(print_expression e)(print_command (nbl - 1) tab c) 
	| Deref(k,e,c) -> Printf.sprintf("let %s = %s in \n%s") k (print_expression e)(print_command (nbl - 1) tab c) 
	| Decrypt(p,e,z,t,c1,c2) -> Printf.sprintf("decrypt %s %s as %s : %s \nthen %s \nelse %s")p z (print_expression e)(print_type t)(print_command (nbl - 1) (tab+1) c1) (print_command (nbl - 1) (tab+1) c2)
	| Connect(chan,t,port,c) -> Printf.sprintf("connect %s : %s ; \n%s")(print_chan chan) (print_chan_type t) (print_command (nbl - 1) tab c) 
	| Accept(chan,t,port,c) -> Printf.sprintf("accept %s : %s; \n%s") (print_chan chan) (print_chan_type t) (print_command (nbl - 1) tab c) 
	| ConnectFor(chan,t,sv,cl,port,c) -> Printf.sprintf("connect %s : %s to %s as %s ; \n%s") (print_chan chan) (print_chan_type t) sv cl (print_command (nbl - 1) tab c) 
	| AcceptFor(chan,t,cl,sv,port,c) -> Printf.sprintf("accept %s : %s from %s as %s ; \n%s") (print_chan chan)(print_chan_type t)cl sv (print_command (nbl - 1) tab c) 
	| Input(chan,z,c) -> Printf.sprintf("input %s (%s) ; \n%s") (print_chan chan) z (print_command (nbl - 1) tab c) 
	| Output(chan,z,c) -> Printf.sprintf("output %s <%s> ; \n%s") (print_chan chan)(print_expression z) (print_command (nbl - 1) tab c) 
	| Register(pw,e,p,c1,c2) -> Printf.sprintf("register %s %s as %s then\n%s %selse \n%s") pw (print_expression e) p (print_command (nbl - 1) (tab+1) c1)space (print_command (nbl - 1) (tab+1) c2)
	| Load(p,i,c) -> Printf.sprintf("load principal %s from %d ;\n%s")p i (print_command (nbl - 1) (tab) c)
	| LoadVar(x,i,t,c) -> Printf.sprintf("load %s : %s from %d; \n%s")x (print_type_of t) i (print_command (nbl - 1) (tab) c)
(*	| Compare(a,b,c,d) ->  Printf.sprintf("Compare")*)
)

let print_first_command cmd = print_command 1 0 cmd ;;
let print_n_command n cmd = print_command n 2 cmd ;;

let print_command cmd = print_command (-1) 2 cmd

let print_label lab =
	match lab with
	| LabConnect(chan) ->   Printf.sprintf "In(%s)" chan
	| LabAccept(chan) ->   Printf.sprintf "In(%s)" chan
	| LabOutput(chan,x) ->  Printf.sprintf "In(%s,%s)" chan x
	| LabInput(chan,f) ->  Printf.sprintf "Out(%s,%s)" chan (print_attacker_expression f)

let rec print_label_list l =
	match l with 
	| [] -> ""
	| [h] -> (print_label h)
	| h::q -> (print_label h)^" \n > "^(print_label_list q)

let print_trace l =
	Printf.printf "Trace seen by the attacker : \n > %s .\n"  (print_label_list (List.rev l))
	
let rec print_mem mem =
	match mem with
	| Loc(x,t,(v,tag))::m -> Printf.printf("\t%s (%s - %s) = %s; \n") x (tag_to_string t) (tag_to_string tag) (print_value v);print_mem m
	| Prin(x,Principal(Sk(s),Pk(p),k))::m  -> Printf.printf("\t%s : Prin(%i;%i;{%s}) ;\n") x s p (print_concrete_public_key_list k);print_mem m
	| [] -> Printf.printf( "\n")

let rec print_threads thds =
	match thds with
	| (cmd,tag) :: l -> Printf.printf("%s : \n%s\n") (if tag = Low then "\tPublic thread" else "\tHidden thread") (print_command cmd); print_threads l
	| [] -> Printf.printf("\n")

	
let rec print_devices devs =
	match devs with
	| Dev(mem,thds,id):: l -> Printf.printf("Device %i: \n") id; print_mem mem; print_threads thds; print_devices l
	| [] -> Printf.printf("\n")
	
	
let print_processus processus =
	let Process(k,refrights,devs) = processus in
	Printf.printf "Current process: \n";
	Printf.printf "R* = %s\n" (print_concrete_rights refrights);
	Printf.printf "K = "; (print_mem k);
	print_devices devs 

let rec print_threads_mini thds =
	match thds with
	| (cmd,tag) :: l -> Printf.printf("%s : \n%s\n") (if tag = Low then "\tPublic thread" else "\tHidden thread") (print_n_command 2 cmd); print_threads_mini l
	| [] -> Printf.printf("\n")

	
let rec print_devices_mini devs =
	match devs with
	| Dev(mem,thds,id):: l -> Printf.printf("Device %i: \n") id; print_mem mem; print_threads_mini thds; print_devices_mini l
	| [] -> Printf.printf("\n")
	
	
let print_processus_mini processus =
	let Process(k,refrights,devs) = processus in
	Printf.printf "Current process (summary):\n";
	Printf.printf "R* = %s\n" (print_concrete_rights refrights);
	Printf.printf "K = "; (print_mem k);
	print_devices_mini devs 
