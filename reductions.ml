open Ast
open Typechecker
open Printers

exception Unbounded_Variable
exception Wrong_Reduction
exception No_More_Reduction
exception Run_Time_Error

let indexfresh = ref 0

let fresh name =
	indexfresh :=  !indexfresh + 1; Printf.sprintf "%s_%i" name (! indexfresh)

let fresh_key () =
	indexfresh :=  !indexfresh + 1; ! indexfresh

let rec get_val mem v =
	match mem with
	| [] -> raise Unbounded_Variable
	| Loc(x,t,y) :: m when x=v -> y
	| _ :: m -> get_val m v
	
let rec get_prin mem p =
	match mem with
	| [] -> raise Unbounded_Variable
	| Prin(x,t) :: m when x=p -> t
	| _ :: m -> get_prin m p

let is_key_pair (Sk(sk)) (Pk(pk)) = sk = pk 
	
let rec replace mem x v =
	match mem with
	| [] -> []
	| Loc(z,tag,_)::m when x=z -> Loc(z,tag,v)::m
	| h::m -> h::(replace m x v)

let rec get_prin mem v =
	match mem with
	| [] -> Printf.printf "No principal with such a name" ;raise Unbounded_Variable
	| Prin(x,y) :: m when x=v -> y
	| _ :: m -> get_prin m v

let rec eval_rights_list mem r =
	match r with
	| [] -> []
	| Key(v) :: m -> let (PKey(v),t)=get_val mem v in v :: (eval_rights_list mem m)
	| Pub(p) :: m -> let Principal(sec,pub,rights)= get_prin mem p in pub :: (eval_rights_list mem m)

let eval_rights mem r =
	match r with
	| Public -> Anyone
	| Set(l) -> CSet(eval_rights_list mem l)

let high t1 t2 =
	match (t1,t2) with
	| (Low,Low) -> Low
	| _ -> High

let less_conf_eval r1 r2 = 
	match (r1,r2) with
	| (Anyone,_) -> true
	| (_,Anyone) -> false
	| (CSet(r1),CSet(r2)) ->  List.for_all (function x -> List.mem x r1) r2

let rec eval_exp mem exp =
	match exp with 
	| Int(v) -> (Integer(v),Low)
	| Var(x) -> get_val mem x
	| Plus(e1,e2) -> 
		let (s1,tag1) = eval_exp mem e1 in
		let (s2,tag2) = eval_exp mem e2 in 
		begin match (s1,s2) with 
		| (Integer(n1),Integer(n2)) -> (Integer(n1+n2),high tag1 tag2)
		| (_,_) -> (NaV,high tag1 tag2) end
	| Element(x,i) -> 
		let (Integer(i),tag1) = eval_exp mem i in 
		let (Tuple(l),tag2) = get_val mem x in
		(List.nth l i, high tag1 tag2)
	| TupleE(l) -> 
		(List.fold_left (fun i e -> let (Tuple(value),tag) = i in let (v,t) = eval_exp mem e in (Tuple(v::value), high tag t)) (Tuple([]),Low) l) 
	| Encrypt(r,e) -> (Cipher(eval_rights_list mem r, fresh_key(), eval_exp mem e), Low)
	| Release(p) -> let Principal(s,p,r)= get_prin mem p in (Encapsulation(r,fresh_key(),Principal(s,p,r)),Low)
	| PubOf(p) -> let Principal(s,pb,r)= get_prin mem p in (PKey(pb),Low)

let valueToRights r =
	List.map (function PKey(k) -> k) r 
let rightsToValue r =
	List.map (function k ->  PKey(k)) r 

	(* attacker's expressions *)
let rec eval_att_exp mem exp =
	match exp with 
	| AInt(v) -> (Integer(v),Low)
	| AVar(x) -> get_val mem x
	| APlus(e1,e2) -> 
		let (s1,tag1) = eval_att_exp mem e1 in
		let (s2,tag2) = eval_att_exp mem e2 in 
		begin match (s1,s2) with 
		| (Integer(n1),Integer(n2)) -> (Integer(n1+n2),high tag1 tag2)
		| (_,_) -> (NaV,high tag1 tag2) end
	| AElement(x,i) -> 
		let (Integer(i),tag1) = eval_att_exp mem i in 
		let (Tuple(l),tag2) = eval_att_exp mem x in
		(List.nth l i, high tag1 tag2)
	| ATupleE(l) -> 
		(List.fold_left (fun i e -> let (Tuple(value),tag) = i in let (v,t) = eval_att_exp mem e in (Tuple(v::value), high tag t)) (Tuple([]),Low) l) 
	| AEncrypt(r,e) -> let (Tuple(rs),t)=  eval_att_exp mem r in
		let rs = valueToRights rs in
		(Cipher(rs, fresh_key(), eval_att_exp mem e), Low)
	| APubOf(p) -> let (PrincipalAsValue(s,pb,r),_)= eval_att_exp mem p in (PKey(pb),Low)
(* Attacker's specific expressions *)
	| ASecOf(p) -> let (PrincipalAsValue(s,pb,r),_)= eval_att_exp mem p in (SKey(s),Low)
	| ARightsOf(p) -> let (PrincipalAsValue(s,pb,r),_)= eval_att_exp mem p in (Tuple(rightsToValue r),Low)
	| AFreshPrin(i) -> if i < 0 then (NaV,Low) else (PrincipalAsValue(Sk(-100 - i),Pk(-100 - i),[]),Low)
	| Alter(p,r) -> begin match (eval_att_exp mem p,eval_att_exp mem r) with
		| ((PrincipalAsValue(sk,pk,r),_),(Tuple(lr),_)) -> (PrincipalAsValue(sk,pk,valueToRights lr),Low)
		| _ ->  (NaV,Low) end
	| ADecr(sec,e) -> 
		let (v,t) =  eval_att_exp mem e in 
		let (s,t) =  eval_att_exp mem sec in begin
		match (s,v) with
		| (SKey(Sk(k)), Cipher(r,i,(v',t))) -> if List.mem (Pk(k)) r then (v',Low) else (NaV,Low) 
		| _ -> (NaV,Low) end


let rec alpha_rename_set_rights r x y =
	match r with
	| Key(k)::l -> Key(if k=x then y else k)::(alpha_rename_set_rights l x y)
	| Pub(p)::l -> Pub(if p=x then y else p)::(alpha_rename_set_rights l x y)
	| [] -> []

let rec alpha_rename_rights r x y =
	match r with 
	| Public -> Public
	| Set(l) -> Set(alpha_rename_set_rights l x y)
	
let alpha_rename_type t x y =
	let Type(s,r)= t in Type(s,alpha_rename_rights r x y)

let alpha_rename_chan_type srr x y =
	let Chan(sr,r)=srr in Chan(alpha_rename_type sr x y,alpha_rename_rights r x y)

let rec alpha_rename_exp exp x y =
	match exp with
	| Int(v) -> Int(v)
	| Var(z) -> if z=x then Var(y) else Var(z)
	| Plus(e1,e2) -> Plus(alpha_rename_exp e1 x y,alpha_rename_exp e2 x y)
	| Element(z,i) -> Element((if z=x then y else z),alpha_rename_exp i x y)
	| TupleE(l) -> TupleE(List.map (fun e -> alpha_rename_exp e x y) l)
	| Encrypt(r,e) -> Encrypt(alpha_rename_set_rights r x y,alpha_rename_exp e x y )
	| Release(p) -> Release((if p = x then y else p))
	| PubOf(p) -> PubOf((if p = x then y else p))


let rec alpha_chan cmd x y =
	match cmd with
	| Skip -> Skip
	| Paral(c1,c2) -> Paral(alpha_chan c1 x y,alpha_chan c2 x y)
	| Bang(c) -> Bang(alpha_chan c x y)
	| If(e1,e2,c1,c2) -> If(e1,e2,alpha_chan c1 x y,alpha_chan c2 x y)
	| IfLess(e1,e2,c1,c2) -> IfLess(e1,e2,alpha_chan c1 x y,alpha_chan c2 x y)
	| NewPrin(p,r,c) -> NewPrin(p,r,alpha_chan c x y)
	| NewVar(z,t,e,c) -> NewVar(z,t,e,alpha_chan c x y)
	| Assign(z,e,c) -> Assign(z, e ,alpha_chan c x y)
	| AssignIndex(z,i,e,c) -> AssignIndex(z, i,e ,alpha_chan c x y)
	| Deref(z,e,c) -> Deref(z,e,alpha_chan c x y)
	| Decrypt(p,e,z,t,c1,c2) -> Decrypt(p,e,z,t,alpha_chan c1 x y,alpha_chan c2 x y)
	| Connect(chan,t,port,c) -> Connect((if chan = x then y else chan),t,port,alpha_chan c x y)
	| Accept(chan,t,port,c) -> Accept((if chan = x then y else chan),t,port,alpha_chan c x y)
	| ConnectFor(chan,t,cl,sv,port,c) -> ConnectFor((if chan = x then y else chan),t,cl,sv,port,alpha_chan c x y)
	| AcceptFor(chan,t,cl,sv,port,c) -> AcceptFor((if chan = x then y else chan),t,cl,sv,port,alpha_chan c x y)
	| Input(chan,z,c) -> Input((if chan = x then y else chan),z, alpha_chan c x y)
	| Output(chan,z,c) -> Output((if chan = x then y else chan),z, alpha_chan c x y)
	| Register(p2,e,p1,c1,c2)-> Register(p2,e,p1,alpha_chan c1 x y, alpha_chan c2 x y)
	| x -> x

let rec alpha_rename cmd x y =
	match cmd with
	| Skip -> Skip
	| Paral(c1,c2) -> Paral(alpha_rename c1 x y,alpha_rename c2 x y)
	| Bang(c) -> Bang(alpha_rename c x y)
	| If(e1,e2,c1,c2) -> If(alpha_rename_exp e1 x y,alpha_rename_exp e2 x y,alpha_rename c1 x y,alpha_rename c2 x y)
	| IfLess(e1,e2,c1,c2) -> IfLess(alpha_rename_exp e1 x y,alpha_rename_exp e2 x y,alpha_rename c1 x y,alpha_rename c2 x y)
	| NewPrin(p,r,c) -> NewPrin((if p = x then y else p),alpha_rename_set_rights r x y,alpha_rename c x y)
	| NewVar(z,t,e,c) -> NewVar((if z = x then y else z),alpha_rename_type t x y,alpha_rename_exp e x y,alpha_rename c x y)
	| Assign(z,e,c) -> Assign((if z = x then y else z),alpha_rename_exp e x y,alpha_rename c x y)
	| AssignIndex(z,i,e,c) -> AssignIndex((if z = x then y else z),alpha_rename_exp i x y,alpha_rename_exp e x y,alpha_rename c x y)
	| Deref(z,e,c) -> Deref((if z = x then y else z),alpha_rename_exp e x y,alpha_rename c x y)
	| Decrypt(p,e,z,t,c1,c2) -> Decrypt((if p = x then y else p),alpha_rename_exp e x y,(if z = x then y else z),alpha_rename_type t x y,alpha_rename c1 x y,alpha_rename c2 x y)
	| Connect(chan,t,port,c) -> Connect(chan,alpha_rename_chan_type t x y,port,alpha_rename c x y)
	| Accept(chan,t,port,c) -> Accept(chan,alpha_rename_chan_type t x y,port,alpha_rename c x y)
	| ConnectFor(chan,t,cl,sv,port,c) -> ConnectFor(chan,alpha_rename_chan_type t x y,(if cl = x then y else cl),(if sv = x then y else sv),port,alpha_rename c x y)
	| AcceptFor(chan,t,cl,sv,port,c) -> AcceptFor(chan,alpha_rename_chan_type t x y,(if cl = x then y else cl),(if sv = x then y else sv),port,alpha_rename c x y)
	| Input(chan,z,c) -> Input(chan,(if z = x then y else z), alpha_rename c x y)
	| Output(chan,e,c) -> Output(chan,alpha_rename_exp e x y, alpha_rename c x y)
	| Register(p2,e,p1,c1,c2)-> Register((if p2 = x then y else p2),alpha_rename_exp e x y,p1,alpha_rename c1 x y, alpha_rename c2 x y)
	| x -> x

let one_step addprin chansType process =
	match process with
	| Process(k,refrights,[]) -> 
		raise No_More_Reduction
	| Process(k,refrights,Dev(mem, [],id) :: d) -> 
		(Process(k,refrights, (*Dev(mem, [],id) ::*) d),[],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( Paral(c1,c2), a):: thr,id) ::d) -> 
		(Process(k,refrights, Dev(mem, ( (c1,a)::(c2,a) :: thr),id) ::d ),[],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( Bang(c),a)::thr,id) ::d ) -> 
		(Process(k,refrights, Dev(mem, (c,a)::( Bang(c),a)::thr, id) ::d),[],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( Skip,a):: thr,id) ::d) -> 
		(Process(k,refrights, Dev(mem, thr,id) ::d),[],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( If(e1,e2,c1,c2),a):: thr,id) ::d) ->
		let (v1,t1) = eval_exp mem e2 in
		let (v2,t2) = eval_exp mem e2 in
		(Process(k,refrights, Dev(mem, ((if v1 = v2 then c1 else c2),high a (high t1 t2))::thr,id) ::d),[],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( IfLess(e1,e2,c1,c2),a):: thr,id) ::d) ->
		let (v1,t1) = eval_exp mem e2 in
		let (v2,t2) = eval_exp mem e2 in
		(Process(k,refrights, Dev(mem, ((if v1 <= v2 then c1 else c2),high a (high t1 t2))::thr,id) ::d),[],[],[],[],0)
	| Process(k,CSet(refrights),Dev(mem, ( NewPrin(p,r,c), a):: thr,id) ::d) -> 
		let y = fresh p in 
		let pubk = fresh_key () in
		(Process(k,CSet(if addprin then (Pk(pubk))::refrights else refrights),Dev(Prin(y,Principal(Sk(pubk),Pk(pubk),eval_rights_list mem r)):: mem, (alpha_rename c p y,a) :: thr,id) ::d ),[y],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( NewVar(x,Type(s,r),e,c), a):: thr,id) ::d) -> 
		let y = fresh x in 
		let (v,t) = eval_exp mem e in
		let tag = if less_conf_eval refrights (eval_rights mem r) then High else Low in
		(Process(k,refrights,Dev((Loc(y,tag, (v, high tag t)))::mem, ( alpha_rename c x y, a):: thr,id) ::d),[],[],[],[(y,Type(s,r))],0)
	| Process(k,refrights,Dev(mem, ( Assign(x,e,c), a):: thr,id) ::d) -> 
		let v = eval_exp mem e in
		(Process(k,refrights,Dev(replace mem x v, (c, a):: thr,id) ::d),[],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( AssignIndex(x,i,e,c), a):: thr,id) ::d) -> 
		let (v,t) = eval_exp mem e in
		let (Integer(i),tagi) = eval_exp mem i in
		let (Tuple(v0),tag0) = get_val mem x in
		let v1 = List.mapi (fun j w -> if j=i then v else w) v0 in
		(Process(k,refrights,Dev(replace mem x (Tuple(v1), high (high t tag0) tagi), (c, a):: thr,id) ::d),[],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( Deref(k1,e,c), a):: thr,id) ::d) -> 
		let k2 = fresh k1 in 
		let (v,t) = eval_exp mem e in
		let tag = Low in
		(Process(k,refrights,Dev((Loc(k2,tag, (v, tag)))::mem, ( alpha_rename c k1 k2, a):: thr,id) ::d),[],[],[k2],[],0)
	| Process(k,refrights,Dev(mem, ( Decrypt(p,e,x,Type(s,Set(r)),c1,c2), a):: thr,id) ::d) -> 
		let y= fresh x in 
		let Principal(sec,pub,rig)= get_prin mem p in 
		let (Cipher(rs,n,v),t) = eval_exp mem e in
		let re = CSet(eval_rights_list mem r) in
		if less_conf_eval (CSet(rs)) (CSet([pub])) && less_conf_eval re (CSet(rs)) then
			(Process(k,refrights,Dev((Loc(y,(if less_conf_eval refrights (CSet(eval_rights_list mem r)) then High else Low),v))::mem, ( alpha_rename c1 x y, a):: thr,id) ::d),[],[],[],[(y,Type(s,Set(r)))],0)
		else
			(Process(k,refrights,Dev(mem, ( alpha_rename c2 x y, a):: thr,id) ::d),[],[],[],[],0)
	| Process(k,refrights,Dev(mem1, (Connect(Ch(chan1),(Chan(Type(s1,Public),Public)),port1,c1) , a1):: thr1,id1) :: Dev(mem2, (Accept(Ch(chan2),(Chan(Type(s2,Public),Public)),port2,c2) , a2):: thr2,id2) ::d) when s1 = s2  && port1 = port2 -> 
		let chan = Active(fresh (chan1 ^ "|" ^chan2 ),Low,Low) in
		(Process(k,refrights,Dev(mem1, (alpha_chan c1 (Ch(chan1)) chan, a1):: thr1,id1) :: Dev(mem2, (alpha_chan c2 (Ch(chan2)) chan, a2):: thr2,id2)::d),[],[(id1,chan,Chan(Type(s1,Public),Public));(id2,chan,Chan(Type(s1,Public),Public))],[],[],0)
	| Process(k,refrights,Dev(mem1, (ConnectFor(Ch(chan1),(Chan(Type(s1,rv1),rc1)),kc1,ks1,port1,c1) , a1):: thr1,id1) :: Dev(mem2, (AcceptFor(Ch(chan2),(Chan(Type(s2,rv2),rc2)),ks2,kc2,port2,c2) , a2):: thr2,id2) ::d) when s1 = s2  && port1 = port2 -> 
		let rv1c = eval_rights mem1 rv1 in
		let rv2c = eval_rights mem2 rv2 in
		let rc1c = eval_rights mem1 rc1 in
		let rc2c = eval_rights mem2 rc2 in
		if less_conf_eval rv1c rv2c 
		&& less_conf_eval rv2c rv1c 
		&& less_conf_eval rc1c rc2c 
		&& less_conf_eval rc2c rc1c then
			(*Verifier clés*)
			let tag=(if less_conf_eval refrights rc1c then High else Low) in
			let chan = Active(fresh (chan1 ^ "|" ^chan2),(if less_conf_eval refrights rv1c then High else Low),tag) in
			(Process(k,refrights,Dev(mem1, (alpha_chan c1 (Ch(chan1)) chan, high tag a1):: thr1,id1) :: Dev(mem2, (alpha_chan c2 (Ch(chan2)) chan, high tag a2):: thr2,id2)::d),[],[(id1,chan,Chan(Type(s1,rv1),rc1));(id2,chan,Chan(Type(s2,rv2),rc2))],[],[],0)
		else raise Wrong_Reduction
	| Process(k,refrights,Dev(mem1, ( Output(Active(chan1,tv1,tt1),e,c1), a1):: thr1,id1)
		:: Dev(mem2,(Input(Active(chan2,tv2,tt2),x,c2),a2):: thr2,id2)::d) when chan1 = chan2 -> 
		let y = fresh x in 
		let v= eval_exp mem1 e in 
		let Chan(sr,_) = Typechecker.get_chan_type (List.map (function (i,x,t) -> (x,t)) (List.filter (function (i,x,t) -> i=id2) chansType)) (Active(chan2,tv2,tt2)) in
		(Process(k,refrights,Dev(mem1,( c1, a1):: thr1,id1):: Dev((Loc(y,(tv2),v))::mem2,(alpha_rename c2 x y,a2):: thr2,id2)::d),[],[],[],[(y, sr)],0) 
	| Process(k,refrights,Dev(mem, ( Register(p2,e,p1,c1,c2), a):: thr,id) ::d) ->
		let newp = fresh p1 in
		let Principal(s,p,r) = get_prin mem p2 in 
		let (Encapsulation(r3,_,Principal(sk1,pk1,r1)),tag) = eval_exp mem e in (*r3 ?*) 
		if less_conf_eval (CSet(r3)) (CSet([p])) then 
			(Process(k,refrights,Dev(Prin(newp,Principal(sk1,pk1,r1))::mem, ((alpha_rename c1 p1 newp), a):: thr,id) ::d),[newp],[],[],[],0)
		else
			(Process(k,refrights,Dev(mem, (c2, a):: thr,id) ::d),[],[],[],[],0)
	| Process(k,CSet(refrights),Dev(mem, ( Load(p,i,c), a):: thr,id) ::d) -> 
		let y = fresh p in 
		let pubk = -i in
		(Process(k,CSet(if addprin then (Pk(pubk))::refrights else refrights),Dev(Prin(y,Principal(Sk(pubk),Pk(pubk),[])):: mem, (alpha_rename c p y,a) :: thr,id) ::d ),[y],[],[],[],0)
	| Process(k,refrights,Dev(mem, ( LoadVar(x,i,b,c), a):: thr,id) ::d) -> 
		let y = fresh x in 
		let (v,t) = ((if(b = Pubkey)then PKey(Pk(-i))else if (b=Number) then Integer(i)else assert false) ,Low) in
		let tag = Low in
		(Process(k,refrights,Dev((Loc(y,tag, (v, high tag t)))::mem, ( alpha_rename c x y, a):: thr,id) ::d),[],[],[],[(y,Type(b,Public))],0)
	| Process(k,refrights,Dev(mem, ( c, a):: thr,id) ::d) -> raise Wrong_Reduction

let rec erase refrights v =
	match refrights with
	| Anyone -> assert false
	| CSet(refrights)->
	match v with
	| Integer(n) -> Clear(Integer(n)) 
	| NaV -> Clear(NaV)
	| PKey(k) -> Clear(PKey(k))
	| Cipher(r,i,(v,t)) -> if List.for_all (fun k -> List.mem k refrights) r then 
		ObfuscatedCipher(r,i)
		else ClearCipher(r,i, erase (CSet(refrights)) v)
	| Encapsulation(r,i,p) -> if List.for_all (fun k -> List.mem k refrights) r then ObfuscatedEncapsulation(r,i) 
		else Clear(Encapsulation(r,i,p))
	| Tuple(lst) -> ErasedTuple(List.map (erase (CSet(refrights))) lst)

let attacker chansType process message =
	match (message,process) with
	| (_,Process(k,refrights,Dev(mem1, (Connect(Ch(chan1),(Chan(Type(s1,Public),Public)),port1,c1) , a1):: thr1,id1)::d))  -> 
		let channame = fresh ("att.|" ^ chan1) in 
		let chan = Active(channame,Low,Low) in
		(Process(k,refrights,Dev(mem1, (alpha_chan c1 (Ch(chan1)) chan, a1):: thr1,id1) ::d),[],[(id1,chan,Chan(Type(s1,Public),Public))],[],LabConnect(channame))
	| (_,Process(k,refrights, Dev(mem2, (Accept(Ch(chan2),(Chan(Type(s2,Public),Public)),port2,c2) , a2):: thr2,id2) ::d)) -> 
		let channame = fresh ("att.|" ^ chan2) in 
		let chan = Active(channame,Low,Low) in
		(Process(k,refrights, Dev(mem2, (alpha_chan c2 (Ch(chan2)) chan, a2):: thr2,id2)::d),[],[(id2,chan,Chan(Type(s2,Public),Public))],[],LabAccept(channame))
	| (AttackWith(expr),Process(k,refrights,Dev(mem1, (ConnectFor(Ch(chan1),(Chan(Type(s1,rv1),rc1)),kc1,ks1,port1,c1) , a1):: thr1,id1)  ::d)) -> 
		let rv1c = eval_rights mem1 rv1 in
		let rc1c = eval_rights mem1 rc1 in
		let (PKey(ks),_) = get_val mem1 ks1 in
		let (SKey(sk),_) = eval_att_exp k expr in
		if is_key_pair sk ks then
			let tag=(if less_conf_eval refrights rc1c then High else Low) in
			let channame = fresh ( "att.|" ^chan1) in 
			let chan = Active(channame,(if less_conf_eval refrights rv1c then High else Low),tag) in
			(Process(k,refrights,Dev(mem1, (alpha_chan c1 (Ch(chan1)) chan, high tag a1):: thr1,id1)::d),[],[(id1,chan,Chan(Type(s1,rv1),rc1))],[],LabConnect(channame))
		else raise Wrong_Reduction
	| (AttackWith(expr),Process(k,refrights,Dev(mem2, (AcceptFor(Ch(chan2),(Chan(Type(s2,rv2),rc2)),ks2,kc2,port2,c2) , a2):: thr2,id2) ::d)) -> 
		let rv2c = eval_rights mem2 rv2 in
		let rc2c = eval_rights mem2 rc2 in
		let (PKey(kc),_) = get_val mem2 kc2 in
		let (SKey(sk),_) = eval_att_exp k expr in
		if is_key_pair sk  kc then
			let tag=(if less_conf_eval refrights rc2c then High else Low) in
			let channame = fresh ( "att.|" ^chan2) in
			let chan = Active(channame,(if less_conf_eval refrights rv2c then High else Low),tag) in
			(Process(k,refrights,Dev(mem2, (alpha_chan c2 (Ch(chan2)) chan, high tag a2):: thr2,id2)::d),[],[(id2,chan,Chan(Type(s2,rv2),rc2))],[],LabAccept(channame))
		else raise Wrong_Reduction
	| (AttackInput, Process(k,refrights,Dev(mem1, ( Output(Active(chan1,tv1,tt1),e,c1), a1):: thr1,id1)::d))-> 
		if String.sub chan1 0 5 <> "att.|" then begin Printf.printf "Not a compromised channel: %s \n" chan1; raise Wrong_Reduction end
		else
		let (v,t)= eval_exp mem1 e in 
		let x = "m"^(string_of_int(List.length k)) in
		(Process(Loc(x,Low,(v,t) ):: k,refrights,Dev(mem1,( c1, a1):: thr1,id1)::d),[],[],[],LabOutput(chan1, x)) 
	| (AttackOutput(expr), Process(k,refrights,Dev(mem2,(Input(Active(chan2,tv2,tt2),x,c2),a2):: thr2,id2)::d))-> 
		if String.sub chan2 0 5 <> "att.|" then raise Wrong_Reduction
		else
		let y = fresh x in 
		let (v,t)= eval_att_exp k expr in 
		let Chan(sr,_) = Typechecker.get_chan_type (List.map (function (i,x,t) -> (x,t)) (List.filter (function (i,x,t) -> i=id2) chansType)) (Active(chan2,tv2,tt2)) in
		(Process(k,refrights,Dev((Loc(y,(tv2),(v,t)))::mem2,(alpha_rename c2 x y,a2):: thr2,id2)::d),[],[],[(y, sr)],LabInput(chan2,expr)) 
	| _ -> raise Wrong_Reduction



let add_device (Process(k,r,devs)) command =
	Process(k,r,Dev([],[command,Low],List.length devs)::devs)

let reduce prins chans keyctx ctx processus =
	let (Process(k,refrights, devs),addedPrin,addedChan,addedKeys,addedCtx,stp) = one_step true chans processus in
	((addedPrin @ prins), (addedChan @ chans), ( addedKeys @ keyctx) ,( addedCtx @ ctx) ,(Process(k,refrights, devs)))

let device_on_top (Process(k,r,devs)) n =
	let (a,b) = List.partition (function Dev(m,c,i) -> i = n) devs in Process(k,r,a @ b)
 
let thread_at_end (Process(k,r,Dev(m,t::thr,i):: devs)) =
	 Process(k,r,Dev(m,thr @ [t],i):: devs)
