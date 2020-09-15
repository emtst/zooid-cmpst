


let log_name = ref ""


let log_channel : out_channel option ref = ref None

let max_logfiles = 100


let is_log_on () = !log_channel = None |> not

let close_log() : unit =
  match !log_channel with
  | Some ch -> close_out ch
  | None -> ()

let create_channel () =
  let rec f n =
    let fn = "log_" ^ string_of_int n ^ ".log" in
    try log_channel := Some (open_out_gen [Open_append ; Open_creat ; Open_excl ; Open_text] 0o644 fn)
    with Sys_error _ ->
      if n <= max_logfiles
      then f (n+1)
      else output_string stderr "Unable to open log file (TOO MANY?)"
  in
  close_log() ; f 0

let create_log (name : string) : bool =
  log_name := name ;
  create_channel () ;
  at_exit close_log ;
  is_log_on ()


let get_now () : string =
  let open Unix in
  let tod = Unix.gettimeofday () |> Unix.gmtime in
  string_of_int (1900 + tod.tm_year) ^ "/"
  ^ string_of_int tod.tm_mon ^ "/"
  ^ string_of_int tod.tm_mday ^ " "
  ^ string_of_int tod.tm_hour ^ ":"
  ^ string_of_int tod.tm_min ^ ":"
  ^ string_of_int tod.tm_sec

let log_str (msg: string) : unit =
  try
    match !log_channel with
    | Some ch ->
       let msg = !log_name ^ " : " ^ get_now() ^ " :: " ^ msg ^ "\n" in
       output_string ch msg ; flush ch
    | _ -> ()
  with _ ->
    output_string stderr "Unable to write to the log file"
