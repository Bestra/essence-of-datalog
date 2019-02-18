open Lib
open Core

let () =
  let file_name = Array.get Sys.argv 1 in
  let query_name = Array.get Sys.argv 2 in
  let file = In_channel.read_all file_name in
  let prog = Parser.parse_program file |> Result.ok_or_failwith in

  let res = query query_name prog in
  sexp_of_query_result res |> Sexp.to_string_hum |> Stdio.print_endline;