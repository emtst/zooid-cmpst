(* Main file *)

let () =
  (* let _ = Log.create_log "Zooid Runtime" in *)
  print_endline "Zooid Runtime";
  Log.log_str "Run the zooid runtime" ;
  Comm.perform ()
