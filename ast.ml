type variable = string
type pvariable = string

type pubkey = 
	| Key of variable
	| Pub of pvariable

type prights = pubkey list



type rights =
	| Set of prights
	| Public

type concrete_public_key = Pk of int

type concrete_rights = 
	| CSet of concrete_public_key list
	| Anyone

type base_type =
	| Number
	| CipherType of base_type
	| Array of base_type
	| Pubkey
	| PrivKey

type comparisonOfRights = LessThan of rights * rights

type label = Type of base_type * rights 

type chan_label = Chan of label * rights 

type tag = Low | High

type chanName = 
	| Active of string * tag * tag
	| Ch of string

type concrete_secret_key = Sk of int

type principal =  Principal of concrete_secret_key * concrete_public_key * (concrete_public_key list)


and value =
	| Integer of int
	| NaV
	| PKey of concrete_public_key
	| Cipher of (concrete_public_key list) * int * taggedValue
	| Encapsulation of (concrete_public_key list) * int *principal
	| Tuple of value list
	(* attacker only *)
	| SKey of concrete_secret_key 
	| PrincipalAsValue of concrete_secret_key * concrete_public_key * (concrete_public_key list)

and taggedValue =
	value * tag

type erasedValue = 
	| Clear of value
	| ErasedTuple of erasedValue list
	| ObfuscatedCipher of (concrete_public_key list) * int 
	| ClearCipher of (concrete_public_key list) * int * erasedValue
	| ObfuscatedEncapsulation of (concrete_public_key list) * int 

type expression =
	| Int of int
	| Var of variable
	| PubOf of pvariable
	| Release of pvariable
	| Encrypt of prights * expression
	| Element of variable * expression
	| Plus of expression * expression
	| TupleE of expression list

type attacker_expression =
	| AInt of int
	| AVar of variable
	| AEncrypt of attacker_expression * attacker_expression
	| AElement of attacker_expression * attacker_expression
	| APlus of attacker_expression * attacker_expression
	| ATupleE of attacker_expression list
	| Alter of attacker_expression * attacker_expression
	| AFreshPrin of int 
	| ADecr of attacker_expression * attacker_expression 
	| ASecOf of   attacker_expression
	| ARightsOf of attacker_expression
	| APubOf of attacker_expression

type command =
	| Load of pvariable * int * command
	| LoadVar of variable * int * base_type * command
	| If of expression * expression * command * command
	| IfLess of expression * expression * command * command
	| NewVar of variable * label * expression * command
	| Assign of variable * expression * command
	| AssignIndex of variable *  expression * expression * command
	| Deref of variable * expression * command
	| Skip
	| Bang of command
	| Paral of command * command
	| Connect of chanName * chan_label * int * command
	| Accept of chanName * chan_label * int * command
	| AcceptFor of chanName * chan_label * variable * pvariable * int * command
	| ConnectFor of chanName * chan_label * variable * pvariable * int * command
	| Output of chanName * expression * command
	| Input of chanName * variable * command
	| NewPrin of pvariable * prights * command
	| Decrypt of pvariable * expression * variable * label * command * command
	| Register of pvariable * expression * pvariable * command * command

type cell = 
	| Loc of variable * tag * taggedValue
	| Prin of pvariable * principal

type memory =  cell list


(*type context = Context of pvariable list * variable list *  ( variable, label) list * (variable, chan_label) list*)

type device = Dev of memory * ((command * tag ) list) * int

type process = Process of memory * (concrete_rights) * device list

type attackerMessage = 
	| AttackPublic 
	| AttackWith of attacker_expression
	| AttackInput 
	| AttackOutput of attacker_expression

type trace = 
	| LabInput of string * attacker_expression
	| LabOutput of string * variable
	| LabConnect of string
	| LabAccept of string