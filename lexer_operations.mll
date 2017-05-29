{
  open Parser_operations

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
  ;;
}  
let digit = ['0' - '9']
let digits = digit +
let lower = ['a' - 'z']
let upper = ['A' - 'Z']
let letter = lower | upper
let letters = letter ((letter | digit) * )
let filename = (letters "/" ) * letters "." letters
rule token = parse
    | "if" { IfS}
    | "then" {Then}
    | "else" {Else}
    | "new" {New}
    | "skip" {SkipS}
    | "connect" {ConnectS}
    | "accept" {AcceptS}
    | "from" {From}
    | "to" {To}
    | "as" {As}
    | "output" {OutputS}
    | "input" {InputS}
    | "newPrin" {NewPrinS}
    | "decrypt" {DecryptS}
    | "enc" {Encr}
    | "register" {RegisterS}
    | "release" {ReleaseS}
    | "pub" {Publ}
    | "PubKey" {PublKeyType }
    | "Int" { IntegerType }
    | "Enc" {EncrType}
    | "PrivKeyEnc" {PrivKeyEncType}
    | "Array" {ArrayType}
    | "Chan" {ChanType}
    | "bot" {Bottom}
    | "load" {LoadS}
    | "principal" {PrincipalS}
    | "{" {LeftB }
    | "}" {RightB}
    | "(" { LeftP }
    | ")" { RightP }
    | "[" { LeftSB }
    | "]" { RightSB }
    | "<" { LeftA }
    | ">" { RightA }
    | ":" {Colon}
    | ";" { SC }
    | "," { Comma }
    | "|" {Parallel}
    | "!" {BangS}
    | "=" {Equals}
    | "+" {PlusS}
    | "add" {AddS}
    | "device" {DeviceS}
    | "typecheck" {TypeCheckS}
    | "reduce" {ReduceS}
    | "exit" {ExitS}
    | "print" {PrintS}
    | "all" {AllS}
    | "small" {SmallS}
    | "select" {SelectS}
    | "thread" {ThreadS}
    | "stop" {StopS}
    | "attacker" {AttackS}
    | "public" {PublicS}
    | "with" {With}
    | "key" {KeyS}
    | "trace" {TraceS}
    | "fresh" {FreshKeyS}
    | "alter" {AlterS}
    | "secret" {SecretS}
    | digits as n { Integ(int_of_string n) }
    | letters as s { Identifier s }
    | filename as f {Filename f}
    | '\n' { incr_linenum lexbuf; token lexbuf }
    | eof { EOF }
    | _ { token lexbuf }
and comment depth = parse
    | '\n' { incr_linenum lexbuf; comment depth lexbuf }
    | "/*" { comment (depth + 1) lexbuf }
    | "*/" { if depth = 1
      then token lexbuf
      else comment (depth - 1) lexbuf }
    | _ { comment depth lexbuf }
and line_comment = parse
    | '\n' { incr_linenum lexbuf; token lexbuf }
    | _ { line_comment lexbuf }
