val print_type_of : Ast.base_type -> string
val print_lst_rights : Ast.pubkey list -> Ast.variable
val print_rights : Ast.rights -> string
val print_concrete_public_key_list : Ast.concrete_public_key list -> string
val print_concrete_rights : Ast.concrete_rights -> string
val print_type : Ast.label -> string
val print_chan_type : Ast.chan_label -> string
val print_ctx : (string * Ast.label) list -> string
val print_chan_ctx : (Ast.chanName * Ast.chan_label) list -> string
val print_prins : string list -> string
val print_chan : Ast.chanName -> string
val tag_to_string : Ast.tag -> string
val print_principal : Ast.principal -> string
val print_value : Ast.value -> string
val print_erased_value : Ast.erasedValue -> string
val print_label : Ast.trace -> string
val print_label_list : Ast.trace list -> string
val print_trace : Ast.trace list -> unit
val print_expression : Ast.expression -> Ast.variable
val print_first_command : Ast.command -> string
val print_n_command : int -> Ast.command -> string
val print_command : Ast.command -> string
val print_mem : Ast.cell list -> unit
val print_threads : (Ast.command * Ast.tag) list -> unit
val print_devices : Ast.device list -> unit
val print_processus : Ast.process -> unit
val print_threads_mini : (Ast.command * Ast.tag) list -> unit
val print_devices_mini : Ast.device list -> unit
val print_processus_mini : Ast.process -> unit
