open PipelineLib.Code

open Comm

module type PROCESS =
  sig
    module PM : PipelineLib.Proc.ProcessMonad
    val proc : unit -> unit
end

let experiment (participants : Comm.conn_desc list) : unit =
  let mp = Comm.build_participant participants in
  let (module IMP) = mp in
  let (module Proc) = (module CAROL (IMP) : PROCESS) in
  Proc.proc ()


let ralice = 0
let rbob = 1
let rcarol = 2

let participants = [
    { role_from = rcarol
    ; role_to = rbob
    ; spec =   Client(build_addr "127.0.0.1" 10002)
  }]



let () = print_endline "here we will have the implementation of pipeline"
       ; experiment participants
       ; Comm.perform ()
