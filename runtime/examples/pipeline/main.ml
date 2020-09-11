open PipelineLib.Code

open Lwt.Infix


module type PROCESS =
  sig
    module PM : PipelineLib.Proc.ProcessMonad
    val proc : unit PM.t
end

let experiment (participants : Comm.conn_desc list) : unit Lwt.t =
  Comm.build_participant participants >>= fun mp ->
  let (module IMP) = mp in
  let (module Proc) = (module BOB (IMP) : PROCESS) in
  let result = Proc.PM.run Proc.proc in
  Lwt.return result

let () = print_endline "here we will have the implementation of pipeline"
       ; (* let _ = experiment [] in *)
         Comm.perform ()
