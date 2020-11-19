(* TCP/IP implementation of the communications module *)

open  GeneratedLib.Proc

open Unix (* using this TCP/IP sockets for now *)

open Lwt.Infix

type role = int

type lbl = int

type channel = Lwt_unix.file_descr

let max_message_length = 1024 * 1024 * 8 (* 8 MB *)

(* connection descriptor *)

type connection_spec = Server of sockaddr | Client of sockaddr

let show_sockaddr = function
  | ADDR_UNIX s -> "Unix: "^ s
  | ADDR_INET (ip, port) -> string_of_inet_addr ip ^ ":" ^ string_of_int port

let show_connection = function
  | Server sa -> "Server " ^ show_sockaddr sa
  | Client sa -> "Client " ^ show_sockaddr sa

type conn_desc = { role_to : role; spec : connection_spec }

let show_conn_desc c =
  "(" ^ string_of_int c.role_to
  ^ "|" ^ show_connection c.spec ^ ")"

let show_conn_descs cs = List.map show_conn_desc cs |> String.concat "**"

(* Zooid Monadic Runtime *)

module type PROCESS =
  sig
    module PM : ProcessMonad
    val proc : unit PM.t
end

module type PROCESS_FUNCTOR =  functor (MP : ProcessMonad) ->
    sig
      module PM :
        sig
          type 'x t = 'x MP.t
          val run : 'a1 t -> 'a1
          val send : role -> role -> 'a1 -> unit t
          val recv : role -> (role -> unit t) -> unit t
          val recv_one : role -> 'a1 t
          val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t
          val pure : 'a1 -> 'a1 t
          val loop : role -> (unit -> 'a1 t) -> 'a1 t
          val set_current : role -> unit t
        end
      val proc : unit MP.t
    end


(* simple dictionary *)

module Dict = Map.Make(Int)

let or_die = function Some v -> v | None -> failwith "or_die called with None"

(* Comm functions *)

let build_addr ip port = ADDR_INET (inet_addr_of_string ip, port)

(* server accepts a connection *)
let server_accept (sa : sockaddr) =
  Log.log_str "creating socket" ;
  let socket = Unix.socket PF_INET SOCK_STREAM 0 in
  Log.log_str "binding socket" ;
  Unix.bind socket sa ;
  Log.log_str "listening socket" ;
  Unix.listen socket 0;
  Log.log_str "accepting socket" ;
  let (ch, _) = Unix.accept socket in
  Log.log_str "closing socket" ;
  Unix.close socket ; ch

(* client requests a connection *)
let client_request addr =
  let socket = Unix.socket PF_INET SOCK_STREAM 0 in
  Unix.connect socket addr ; socket

(* Function that sets up the connection and implements the monad *)
let setup_channels (conns : conn_desc list) :
    channel Dict.t =
  let conn_desc_to_ch (conn : conn_desc) : (role * Unix.file_descr)=
    let s  = match conn.spec with
    | Server addr ->
       Log.log_str "setting up a server connection" ;
       server_accept addr
    | Client addr -> client_request addr
    in  (conn.role_to, s)
  in
  Log.log_str ("about to start connections: " ^ show_conn_descs conns) ;
  let cs = List.map conn_desc_to_ch conns in
  List.fold_left
    (fun dict (role, ch) -> Dict.add role (Lwt_unix.of_unix_file_descr ch) dict)
    Dict.empty cs

let build_participant (conn : conn_desc list) : (module ProcessMonad) =
  let size_buffer_len = 4 in
  let current_loop : int option ref = ref None in
  Log.log_str "about to setup channels" ;
  let part_to_ch = setup_channels conn in
  let ch_str = Seq.fold_left
                 (fun xs (x, _) -> string_of_int x ^ ", " ^ xs ) ""  (Dict.to_seq part_to_ch)
  in
  Log.log_str ("channels setup:" ^ ch_str);
  let send' role payload =
    let size_buff = Bytes.create size_buffer_len in
    let buff = Marshal.to_bytes payload [] in
    let l = Bytes.length buff in
    "about to send to: " ^ string_of_int role ^ " size: " ^ string_of_int l |> Log.log_str ;

    Bytes.set_int32_be size_buff 0 (Int32.of_int l) ;
    Lwt_unix.send (Dict.find role part_to_ch) size_buff 0 size_buffer_len [] >>= fun l' ->
    assert (l' = size_buffer_len) ;

    "sending payload" |> Log.log_str ;
    Lwt_unix.send (Dict.find role part_to_ch) buff 0 l [] >>= fun l' ->
    (if l' < 0 then
       Log.log_str @@ "send returned an error: l' = " ^ string_of_int l'
     else
       (if l != l' then Log.log_str @@ ">>>>>>>>>> l = " ^ string_of_int l ^ " l' = " ^ string_of_int l' else ()) ;
       assert (l = l'));
    Lwt.return l'
  in
  let rec recv_size ch buff offset msg_size =
    Lwt_unix.recv ch buff offset msg_size []
    >>= fun l ->
    if l < msg_size then recv_size ch buff l (msg_size - l) else Lwt.return (offset + l)
  in
  let recv' role =
    let size_buff = Bytes.create size_buffer_len in
    let buff = Bytes.create max_message_length in
    "about to recv size" |> Log.log_str;
    (* Lwt_unix.recv (Dict.find role part_to_ch) size_buff 0 size_buffer_len [] *)
    recv_size (Dict.find role part_to_ch) size_buff 0 size_buffer_len
    >>= fun l -> assert (l = size_buffer_len) ;
    let msg_size = Bytes.get_int32_be size_buff 0 |> Int32.to_int in
    "expecting a message size: " ^ string_of_int msg_size |> Log.log_str ;
    (* Lwt_unix.recv (Dict.find role part_to_ch) buff 0 msg_size [] *)
    recv_size (Dict.find role part_to_ch) buff 0 msg_size
    >>= fun l ->
    "recv' with length:" ^ string_of_int l |> Log.log_str ;
    Marshal.from_bytes buff 0 |> Lwt.return
  in
     (module struct
      type 'a t = 'a Lwt.t

      let run p = Log.log_str "running main" ; Lwt_main.run p

      (* communication primitives *)
      let send role lbl _payload =
        send' role lbl >>= fun _ ->
        send' role _payload >>= fun _ -> Lwt.return ()

      let recv role cont = recv' role >>= fun lbl' -> cont lbl'

      let recv_one = recv'

      (* monadic code *)
      let bind am af = Lwt.( >>= ) am af

      let pure x = Lwt.return x

      let string_of_current () =
        match !current_loop with
        | Some x -> string_of_int x
        | None -> "none"

      (* recursion *)
      let rec loop id proc =
        bind (Log.log_str "about to proc" ; proc ()) (fun x ->
            Log.log_str ("curent_loop: " ^ string_of_current ()) ;
            Log.log_str ("new loop: " ^ string_of_int id) ;
            if !current_loop = Some id then (
              current_loop := None;
              Log.log_str "about to loop again" ;
              loop id proc )
            else pure x)

      let set_current id =
        "set_current: " ^ string_of_int id  |> Log.log_str ;
        current_loop := Some id;
        pure ()
    end : ProcessMonad)


let execute_extracted_process (participants : conn_desc list) mpart : unit =
  Log.log_str "starting" ;
  let mp = build_participant participants in
  let (module Part : PROCESS_FUNCTOR) = mpart in
  Log.log_str "connections established" ;
  let (module IMP) = mp in
  let (module Proc) = (module Part (IMP) : PROCESS) in
  Log.log_str "running proc" ;
  Proc.proc |> Proc.PM.run
