(* TCP/IP implementation of the communications module *)

open Unix (* using this TCP/IP sockets for now *)
open Lwt.Infix


type role = string
type label = string
type channel = Lwt_unix.file_descr

let max_message_length = 8192

(* connection descriptor *)

type connection_spec = Server of sockaddr | Client of sockaddr

type conn_desc =
  { role_from : role
  ; role_to : role
  ; spec : connection_spec
  }

let get_my_addresses () =
  let hi = gethostname () |> gethostbyname in
  hi.h_addr_list |> Array.to_list

(* Zooid Monadic Runtime *)
module Equality =
  struct
  type sort = role
 end

module type MP =
 sig
  type 'a t

  val send : Equality.sort -> Equality.sort -> 'a1 -> unit t

  (* ALERT ROLE *)
  val recv : Equality.sort -> (Equality.sort -> unit t) -> unit t

  val recv_one : Equality.sort -> 'a1 t

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val pure : 'a1 -> 'a1 t

  val loop : int -> 'a1 t -> 'a1 t

  val set_current : int -> unit t
 end


(* simple dictionary *)

type ('a, 'b) dict = 'a -> 'b option

let empty_dict _ = None
let add_dict k v dict = fun k' -> if k' = k then Some v else dict k
let lookup_dict k dict = dict k
let or_die = function
    | Some v -> v
    | None -> failwith "or_die called with None"

(* Comm functions *)

let build_addr ip port =
  ADDR_INET (inet_addr_of_string ip, port)

(* server accepts a connection *)
let server_accept (sa : sockaddr) =
  let socket = Lwt_unix.socket PF_INET SOCK_STREAM 0 in
  Lwt_unix.bind socket sa >>= fun () ->
  Lwt_unix.listen socket 0 ;
  Lwt_unix.accept socket >>= fun (ch, _) ->
  Lwt_unix.close socket >>= fun () ->
  Lwt.return ch

(* client requests a connection *)
let client_request addr =
  let socket = Lwt_unix.socket PF_INET SOCK_STREAM 0 in
  Lwt_unix.connect socket addr >>= fun () ->
  Lwt.return socket

(* Function that sets up the connection and implements the monad *)
let setup_channels (conns : conn_desc list) :
      (channel list * (role, channel) dict) Lwt.t =
  let conn_desc_to_ch (conn : conn_desc) : (role * channel) Lwt.t =
    begin match conn.spec with
    | Server addr -> server_accept addr
    | Client addr -> client_request addr
    end >>= fun s -> Lwt.return (conn.role_to, s)
  in
  List.map conn_desc_to_ch conns |> Lwt.all >>= fun cs ->
  Lwt_list.fold_left_s
    (fun (chs, dict) (role, ch) -> Lwt.return (ch::chs, add_dict role ch dict))
    ([], empty_dict) cs


(* test for the channel setup function *)

let test_channel_setup () =
  print_endline "Testing channel setup (remove from finished code)" ;
  let cs : conn_desc list =
    [ { role_from = "A" ; role_to = "B" ; spec = Server (build_addr "127.0.0.1" 13245) }
    ; { role_from = "B" ; role_to = "A" ; spec = Client (build_addr "127.0.0.1" 13245) }
    ]
  in
  setup_channels cs >>= fun (chs, _d) ->
  Lwt_list.iter_s (fun _ch -> Lwt_unix.close _ch >>= fun () ->
                              Lwt.return ()) chs >>= fun () ->
  print_endline "Ok." ; Lwt.return ()


let build_participant (conn : conn_desc list) : (module MP) Lwt.t =
  let current_loop : int option ref = ref None in
  setup_channels conn >>= fun (_chs, part_to_ch) ->
  let recv' role =
    let buff = Bytes.create max_message_length in
    Lwt_unix.recv
      (part_to_ch role |> or_die)
      buff 0 max_message_length
      [] >>= fun _l ->
    Marshal.from_bytes buff 0 |> Lwt.return
  in
  Lwt.return
  (module struct

     type 'a t = 'a Lwt.t

     (* communication primitives *)
     let send role lbl _payload =
       let send' role payload =
         let buff = Marshal.to_bytes payload [] in
         let l = Bytes.length buff in
         Lwt_unix.send
           (part_to_ch role |> or_die)
           buff 0 l
           [] >>= fun l' ->
         assert (l = l') ; Lwt.return l'
       in
       send' role lbl >>= fun _ ->
       send' role _payload >>= fun _ ->
       Lwt.return ()

     let recv role cont =
       recv' role >>= fun lbl' ->
       cont lbl'

     let recv_one = recv'

     (* monadic code *)
     let bind am af = Lwt.(>>=) am af
     let pure x = Lwt.return x

     (* recursion *)
     let rec loop id proc =
       bind proc (fun x ->
           if !current_loop = Some id
           then (current_loop := None ; loop id proc)
           else pure x)

     let set_current id =
       current_loop := Some id ; pure ()
   end : MP)


let perform () =
  let addrs = get_my_addresses () |> List.map string_of_inet_addr in
  "Host: " ^ gethostname () ^ " IPs: " ^ String.concat ", " addrs
  |> print_endline ;
  test_channel_setup () |> Lwt_main.run


(* let toto = Pervasives.succ
 *
 * let run_something conn =
 *   build_participant conn >>= fun mp ->
 *   let (module MP) = mp in
 *   let _bob_mp =
 *     MP.loop 0
 *       (MP.recv 0 (fun l ->
 *            if eqn l (Pervasives.succ 0)
 *            then MP.bind (MP.recv_one 0) (fun x ->
 *                     MP.bind
 *                       (MP.send (Pervasives.succ (Pervasives.succ 0))
 *                          (Pervasives.succ 0)
 *                          (muln x (Pervasives.succ (Pervasives.succ 0)))) (fun _ ->
 *                         MP.set_current (subn (Pervasives.succ 0) 0)))
 *            else MP.pure ()))
 *   in
 *   Lwt.return () *)
