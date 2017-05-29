exception Bad_Type
exception Type_Error
exception Type_Failure of int
val add_prin : 'a list -> 'a -> 'a list
val add_var : ('a * 'b) list -> 'a -> 'b -> ('a * 'b) list
val add_chan : ('a * 'b) list -> 'a -> 'b -> ('a * 'b) list
val rights_intersect : 'a -> Ast.rights -> Ast.rights -> Ast.rights
val less_confidential_than : 'a -> Ast.rights -> Ast.rights -> bool
val get_type : (string * Ast.label) list -> string -> Ast.label
val get_chan_type : (Ast.chanName * Ast.chan_label) list -> Ast.chanName -> Ast.chan_label
val acting : string list -> string -> bool
val base_type_of : Ast.value -> Ast.base_type
val typecheck_exp :
  'a ->
  Ast.pvariable list ->
  Ast.variable list ->
  (Ast.variable * Ast.label) list -> Ast.expression -> Ast.label
val typecheck_cmd :
  Ast.comparisonOfRights list ->
  Ast.rights ->
  Ast.pvariable list ->
  (Ast.chanName * Ast.chan_label) list ->
  Ast.variable list ->
  (Ast.variable * Ast.label) list -> Ast.command -> unit
val typecheck_all :
  Ast.pvariable list ->
  (int * Ast.chanName * Ast.chan_label) list -> 
  Ast.variable list ->
  (Ast.variable * Ast.label) list -> Ast.process -> unit
