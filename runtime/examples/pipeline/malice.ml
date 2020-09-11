open PipelineLib.Code

open Lwt.Infix
open Comm

module type PROCESS =
  sig
    module PM : PipelineLib.Proc.ProcessMonad
    val proc : unit PM.t
end

let experiment (participants : conn_desc list) : unit Lwt.t =
  print_endline "VOO1" ;
  Comm.build_participant participants >>= fun mp ->
  let (module IMP) = mp in
  let (module Proc) = (module BOB (IMP) : PROCESS) in
  let result = Proc.PM.run Proc.proc in
  print_endline "VOO2" ;
  Lwt.return result

let ralice = 0
let rbob = 1
let rcarol = 2

let participants = [
    { role_from = rbob
    ; role_to = ralice
    ; spec =   Server(build_addr "127.0.0.1" 10001)
  }]


let () = print_endline "Implementation for the role of alice in the pipeline"
       ; let _ = experiment participants in ()
