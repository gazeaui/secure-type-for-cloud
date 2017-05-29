(****************************************************************************)
(*                                                                          *)
(* This program is free software; you can redistribute it and/or modify     *)
(* it under the terms of the GNU General Public License as published by     *)
(* the Free Software Foundation; either version 2 of the License, or        *)
(* (at your option) any later version.                                      *)
(*                                                                          *)
(* This program is distributed in the hope that it will be useful,          *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(* GNU General Public License for more details.                             *)
(*                                                                          *)
(* You should have received a copy of the GNU General Public License along  *)
(* with this program; if not, write to the Free Software Foundation, Inc.,  *)
(* 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.              *)
(****************************************************************************)

{
  open Parser

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
    | "let" {Letk}
    | "skip" {SkipS}
    | "connect" {ConnectS}
    | "accept" {AcceptS}
    | "from" {From}
    | "to" {To}
    | "as" {As}
    | "in" {In}
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
    | "<=" {LessThan}
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
    | digits as n { Integ(int_of_string n) }
    | letters as s { Identifier s }
    | filename as f {Filename f}
    | '\n' { incr_linenum lexbuf; token lexbuf }
    | eof { EOF }
    | _ { token lexbuf }
    | "device" {DeviceS}
    | "typecheck" {TypeCheckS}
    | "reduces" {ReduceS}
    | "exit" {ExitS}
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
