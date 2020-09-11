open PipelineLib.Code

open Lwt.Infix


module type PROCESS =
  sig
    module PM : PipelineLib.Proc.ProcessMonad
    val proc : unit PM.t
end

let experiment () =
  let participants : Comm.conn_desc list = [] in
  Comm.build_participant participants >>= fun mp ->
  let (module IMP) = mp in
  let (module Proc) = (module BOB (IMP) : PROCESS) in
  let _ = Proc.proc in Lwt.return ()



let () = print_endline "here we will have the implementation of pipeline"
       ; Comm.perform ()
