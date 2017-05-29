open Ast 
open Printers

exception Bad_Type
exception Type_Error
exception Type_Failure of int

let add_prin actfor  prin =
	prin :: actfor
let add_var ctx var label =
	(var,label) :: ctx
let add_key keys key =
	key :: keys

let add_chan chans var label =
	(var,label) :: chans

let rights_intersect vprin r1 r2 =
	match (r1,r2) with
	| (Public,r) -> r
	| (r,Public)-> r
	| (Set(list1),Set(list2)) -> Set(List.filter (function x ->  List.mem x list2) list1)

let wfr prin keyctx right =
	match right with
	| Public -> true
	| Set(r) -> 
		let fail = List.exists (function 
			| Pub(p) -> not (List.exists (fun pr -> pr = p) prin)
			| Key(k) -> not (List.exists (fun key -> key = k) keyctx)) r in
		if not fail then true 
		else begin Printf.printf "The right '%s' contains unbounded variables (or type is not public key).\n"(print_rights right);
		raise Bad_Type end

let less_confidential_than vprin r1 r2 =
	match (r1,r2) with
	| (Public,r) -> true
	| (_,Public) -> false
	| (Set(list1),Set(list2)) ->
		begin let l= List.filter (function x -> not (List.mem x list1)) list2 in  
		match l with
			| [] -> true
			| Pub(p)::l -> begin Printf.printf "The principal '%s' breaks the condition %s less confidential than %s .\n" p (print_rights r1) (print_rights r2); false end 
			| Key(k)::l -> begin Printf.printf "The key '%s' breaks the confidentiality\n" k ; false end 
		end

let get_type ctx var =
	try
	let (v,sr) = List.find (fun (x,t) -> x = var) ctx in sr
	with Not_found -> begin Printf.printf "Variable \"%s\"  not present in the context %s \n" var (print_ctx ctx); raise Bad_Type end
	
let get_chan_type ctx var =
	try
	let (v,sr) = List.find (fun (x,t) -> x = var) ctx in sr
	with Not_found -> begin Printf.printf "Chan \"%s\"  not present in the chan context %s \n" (print_chan var) (print_chan_ctx ctx); raise Bad_Type end

let acting actfor var =
	if List.exists (fun x -> x = var) actfor
	then true 
	else begin Printf.printf "Principal \"%s\" is unknown in %s " var (print_prins actfor); raise Bad_Type end
let key_exists keys key =
	if List.exists (fun x -> x = key) keys
	then true 
	else begin Printf.printf "Key \"%s\" is unknown  " key;  raise Bad_Type end

let rec base_type_of v =
	match v with
	| Integer(n) -> Number
	| NaV  -> Number
	| PKey(n) -> Pubkey
	| Tuple([]) -> Number
	| Tuple(h::v) -> 
		if v = [] then Array(base_type_of h) else
		let type_of_v = base_type_of (Tuple(v)) in
		if type_of_v = Array(base_type_of h) 
		then Array(base_type_of h) 
		else begin Printf.printf "Inconsistent element for the array:  %s %s\n" (print_type_of type_of_v) (print_type_of (base_type_of h)) ; raise Bad_Type end
	| Cipher(r,n,(v,t)) -> CipherType(base_type_of v) 
	| Encapsulation(r,n,p) -> PrivKey
	| _ -> raise Bad_Type

let rec typecheck_exp vprin actfor keyctx ctx exp =
	match exp with
	| Int(v) -> Type(Number, Public)
	| Var(var) -> get_type ctx var
	| Plus(e1,e2) -> let Type(s1,r1) = typecheck_exp vprin actfor keyctx ctx e1 in
		let Type(s2,r2) = typecheck_exp vprin actfor keyctx ctx e2 in
		if s1 = Number && s2 = Number then
			Type(Number, rights_intersect vprin r1 r2)
		else begin Printf.printf "Addition of non numeric values\n";raise Bad_Type end
	| PubOf(p) -> acting actfor p; Type(Pubkey, Public)
	| Release(p) -> acting actfor p;Type(PrivKey, Public)
	| Encrypt(rs,e) -> begin wfr actfor keyctx (Set(rs)) ;let Type(s,r) = typecheck_exp vprin actfor keyctx ctx e  in
		if less_confidential_than vprin r (Set(rs)) 
		then Type(CipherType(s),Public) 
		else begin Printf.printf "wrong encryption\n" ; raise Bad_Type end  
		end
	| Element(x,i) -> let tarray = get_type ctx x in
		let ti = typecheck_exp vprin actfor keyctx ctx i in
		begin
		match (tarray,ti) with
		| (Type(Array(s),ra),Type(Number,ri)) -> Type(s,rights_intersect vprin ra ri)
		| _ -> begin Printf.printf "Extracting element of a non-array\n" ; raise Bad_Type end
		end
	| TupleE([]) -> Type(Array(Number),Public)
	| TupleE(h::v) -> let Type(s,r)= typecheck_exp vprin actfor keyctx ctx h in 
		if v = [] then Type(Array(s),r) 
		else
			let Type(s2,r2)=  typecheck_exp vprin actfor keyctx ctx (TupleE(v)) in
			if s2 = Array(s) 
			then Type(s2,rights_intersect vprin r r2) 
			else begin Printf.printf "Inconsistent element for the array:  %s %s\n" (print_type_of s) (print_type_of (s2)) ; raise Bad_Type end
	| _ -> raise Bad_Type


let rec typecheck_cmd vprin pc actfor chans keyctx ctx cmd =
	try 
	(match cmd with
	| Skip -> ()
	| Paral(c1,c2) ->
		(typecheck_cmd vprin pc actfor chans keyctx ctx c1) ; 
		(typecheck_cmd vprin pc actfor chans keyctx ctx c2)
	| Bang(c) -> 
		typecheck_cmd vprin pc actfor chans keyctx ctx c
	| NewPrin(pvar,rights,cmd) -> 
		wfr actfor keyctx (Set(rights));
		if pc = Public 
		then typecheck_cmd vprin pc (add_prin actfor pvar)chans keyctx ctx cmd 
		else begin Printf.printf "Attempt to create a principal with a non public pc"; raise Bad_Type end 
	| NewVar(var,Type(s1,r1),e,c) -> 
		wfr actfor keyctx r1;
		let Type(s2,r2) = typecheck_exp vprin actfor keyctx ctx e in 
		if s1 = s2  
		&& less_confidential_than vprin r2 (rights_intersect vprin r1 pc) 
		then
			typecheck_cmd vprin pc actfor chans keyctx (add_var ctx var (Type(s1,r1))) c
		else begin Printf.printf "Creation of %s: %s with an expression of type %s\n" var (print_type_of s1) (print_type_of s2); raise Bad_Type end
	| Assign(var,e,c) -> 
		let Type(s1,r1) = get_type ctx var in 
		let Type(s2,r2) = typecheck_exp vprin actfor keyctx ctx e in 
		if s1 = s2 
		&& less_confidential_than vprin (rights_intersect vprin r2 pc) r1 
		&& s1 != Pubkey
		then typecheck_cmd vprin pc actfor chans keyctx ctx c
		else begin Printf.printf "Assignement in %s : %s with a value of type %s. \n" var (print_type (Type(s1,r1)))(print_type (Type(s2,r2))); raise Bad_Type end
	| AssignIndex(var,i,e,c) -> 
		let Type(s1,r1) = get_type ctx var in 
		let Type(s2,r2) = typecheck_exp vprin actfor keyctx ctx e in 
		let Type(s3,r3) = typecheck_exp vprin actfor keyctx ctx i in 
		if s3 = Number 
		&& s1 = Array(s2) 
		&& less_confidential_than vprin (rights_intersect vprin r2 pc) r1 
		&& less_confidential_than vprin (rights_intersect vprin r3 pc) r1 
		then typecheck_cmd vprin pc actfor chans keyctx ctx c
		else begin Printf.printf "assignement in the array %s\n" var; raise Bad_Type end
	| Deref(key,e,c) -> 
		if  Type(Pubkey,Public) = typecheck_exp vprin actfor keyctx ctx e
			&& pc = Public
		then
			typecheck_cmd vprin pc actfor chans (add_key keyctx key) ctx c
		else begin Printf.printf "Declaration of %s but %s in not a public key\n" key (print_expression e); raise Bad_Type end
	| Decrypt(pvar,e,x,Type(s1,r1),c1,c2) -> 
		acting actfor pvar;
		wfr actfor keyctx r1;
		let Type(s2,r2) = typecheck_exp vprin actfor keyctx ctx e in
		if s1 = CipherType(s2) 
		&& less_confidential_than vprin (rights_intersect vprin r2 pc) r1 
		then begin 
			typecheck_cmd vprin (rights_intersect vprin r2 pc) actfor chans keyctx (add_var ctx x (Type(s1,r1))) c1 ; 
			typecheck_cmd vprin (rights_intersect vprin r2 pc) actfor chans keyctx ctx c2 end
		else begin Printf.printf "Decryption is stored at low level \n" ; raise Bad_Type end
	| Connect(cname,Chan(Type(s,r1),r2),port,c) -> 
		if pc = Public && r1 = Public && r2 = Public
		then typecheck_cmd vprin pc actfor (add_chan chans cname (Chan(Type(s,r1),r2))) keyctx ctx c 
		else begin Printf.printf "A public channel with a highpc\n" ;raise Bad_Type end 
	| Accept(cname,Chan(Type(s,r1),r2),port,c) ->
		if pc = Public && r1 = Public && r2 = Public
		then typecheck_cmd vprin pc actfor (add_chan chans cname (Chan(Type(s,r1),r2))) keyctx ctx c 
		else begin Printf.printf "A public channel with a highpc\n" ;raise Bad_Type end
	| ConnectFor(cname,Chan(Type(s,r1),r2),server,client,port,c) ->
		wfr actfor keyctx r1; wfr actfor keyctx r2;
		if acting actfor client 
		&& key_exists keyctx server
		&& less_confidential_than vprin pc r2 
		&& less_confidential_than vprin r2 r1 
		&& less_confidential_than vprin r1 (Set([Pub(client);Key(server)]))
		then typecheck_cmd vprin pc actfor (add_chan chans cname (Chan(Type(s,r1),r2))) keyctx ctx c 
		else begin Printf.printf "confidentiality broken in ConnectFor\n"; raise Bad_Type end
	| AcceptFor(cname,Chan(Type(s,r1),r2),client,server,port,c) ->
		wfr actfor keyctx r1; wfr actfor keyctx r2;
		if not (acting actfor server) then 
			begin Printf.printf "Device not acting for %s " server; raise Bad_Type end
		else if not (key_exists keyctx client ) then
			begin Printf.printf "The public key %s of the client is not public " server; raise Bad_Type end
		else if not (
		less_confidential_than vprin pc r2 
		&& less_confidential_than vprin r2 r1 
		&& less_confidential_than vprin r1 (Set([Pub(server);Key(client)])))
		then begin Printf.printf "Conditions for establishing a confidential channel are not satisfied \n"; raise Bad_Type end
		else
			typecheck_cmd vprin pc actfor (add_chan chans cname (Chan(Type(s,r1),r2))) keyctx ctx c 
	| Output(ch,e,c) ->  
		let Type(s1,r1) = typecheck_exp vprin actfor keyctx ctx e in
		let Chan(Type(s2,r2), r3) = get_chan_type chans ch in
		if s1 = s2
		&& less_confidential_than vprin  r1 r2 
		&& r3 = pc 
		then typecheck_cmd vprin pc actfor chans keyctx ctx c
		else  begin Printf.printf "Output in %s of type  %s => Ch[%s] \n" (print_chan ch) (print_type_of s1)(print_type_of s2); raise Bad_Type end
	| Input(ch,x,c) ->  
		let Chan(sr2, r3) = get_chan_type chans ch in
		if r3 = pc then 
			typecheck_cmd vprin pc actfor chans keyctx (add_var ctx x sr2) c
		else  begin Printf.printf "Input on a channel with an incorrect pc\n" ; raise Bad_Type end
	| If(e1,e2,c1,c2) -> 
		let Type(s1,r1) = typecheck_exp vprin actfor keyctx ctx e1 in
		let Type(s2,r2) = typecheck_exp vprin actfor keyctx ctx e2 in 
		let pc'= (rights_intersect vprin r1 (rights_intersect vprin r2 pc)) in
		if s1 = s2 then begin
			typecheck_cmd vprin pc' actfor chans keyctx ctx c1 ; 
			typecheck_cmd vprin pc' actfor chans keyctx ctx c2 end
		else begin Printf.printf "if..." ; raise Bad_Type end 
	| IfLess(e1,e2,c1,c2) -> 
		let Type(s1,r1) = typecheck_exp vprin actfor keyctx ctx e1 in
		let Type(s2,r2) = typecheck_exp vprin actfor keyctx ctx e2 in 
		let pc'= (rights_intersect vprin r1 (rights_intersect vprin r2 pc)) in
		if s1 = s2 && s1 = Number then begin
			typecheck_cmd vprin pc' actfor chans keyctx ctx c1 ; 
			typecheck_cmd vprin pc' actfor chans keyctx ctx c2 end
		else begin Printf.printf "if..." ; raise Bad_Type end 
	| Register(p2,e,p1,c1,c2) -> 
		if acting actfor p2 
		&& Type(PrivKey,Public) = typecheck_exp vprin actfor keyctx ctx e 
		&& pc = Public
		then begin
			typecheck_cmd vprin pc (add_prin actfor p1) chans keyctx ctx c1 ;
			typecheck_cmd vprin pc actfor chans keyctx ctx c2 end
		else begin Printf.printf "Register\n"; raise Bad_Type end
	| Load(p,i,c) -> typecheck_cmd vprin pc (add_prin actfor p) chans keyctx ctx c
	| LoadVar(x,i,b,c) -> typecheck_cmd vprin pc actfor chans keyctx  (add_var ctx x (Type(b,Public))) c
	)
	with Bad_Type -> begin Printf.printf (" at:\n %s") (print_first_command cmd);raise Type_Error end
		
let typecheck_all prins chans keyctx ctx processus =
	let Process(_,_,l) = processus in 
	List.iter( function (Dev(mem,thds,id)) -> List.iter 
		(function (cmd,tag) -> try
			typecheck_cmd [] (if tag = Low then Public else Public) prins (List.map (function (j,y,tt)-> (y,tt) )(List.filter (function (i,x,t) -> i=id)chans)) keyctx ctx cmd
			with | Type_Error -> raise (Type_Failure(id)) ) thds) l
