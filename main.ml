open Unix
open String
open Printf
open Scanf

open TFTP


let input_buf_size = 1024

let recv_timeout = 5.0

let send_timeout = 5.0


let str_to_list s = List.init (String.length s) (String.get s)

let list_to_str s = let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) s; Buffer.contents buf


let write_file desc = Printf.fprintf desc "%s"

let read_file filename =
  let ch = open_in filename in let s = really_input_string ch (in_channel_length ch) in
  close_in ch; s


let parse_args =
  let port = ref 69
  and hostname = ref None
  and filename = ref None
  and md = ref None
  in
  let speclist =
    [ ("-p", Arg.Int (fun x -> port := x), "Port of the server")
    ; ("-h", Arg.String (fun x -> hostname := Some x), "Hostname of the server")
    ; ("-m", Arg.String (fun x -> md :=
                            match x with "r" -> Some Read | "w" -> Some Write | _ -> None),
       "Mode – r for read, w for write")
    ]
  in Arg.parse speclist (fun s -> filename := Some s) "USAGE: -p [PORT] -h [HOSTNAME] -m [r|w] [FILENAME]";
     match (!port, !hostname, !filename, !md) with
       | (p, Some h, Some f, Some m) -> (p, h, f, m)
       | _ -> failwith "Bad params"


let create_socket () =
  let soc = socket PF_INET SOCK_DGRAM 0 in
  setsockopt_float soc SO_RCVTIMEO recv_timeout;
  setsockopt_float soc SO_SNDTIMEO send_timeout;
  soc


let send_packet desc hostname port data =
  let rec push (from : int) (amount : int) =
    let sent = sendto_substring desc data from amount [] (ADDR_INET ((inet_addr_of_string hostname), port))
    in if sent = amount then ()
    else if sent < 0 then failwith "Connection error"
    else push (from + sent) (amount - sent)
  in push 0 (String.length data)

let rec recv_packet desc =
  let input_buf = Bytes.create (input_buf_size + 1) in
  let (len, sender) = recvfrom desc input_buf 0 input_buf_size [] in
  if len = -1
  then UTimeout
  else if len < 0
  then failwith "Connection error"
  else
    let resp = Bytes.to_string (Bytes.sub input_buf 0 len)
    and snd_port = match sender with ADDR_INET (_, prt) -> prt | _ -> 0 in
    UPacket (n_of_int snd_port, (str_to_list resp))


let () =
  let (init_port, hostname, filename, md) = parse_args in
  let sock = create_socket () in

  match md with
  | Read ->
    let file_desc = open_out filename in
    let rec loop state =
      let event = recv_packet sock in
      let (new_state, mpack) = handle_unparsed_event_read event state in
      begin match mpack with
        | None -> ()
        | Some (msg, mport) -> send_packet sock hostname (match mport with Some p -> int_of_n p | None -> init_port) (list_to_str msg)
      end;
      begin match new_state with
        | ReadingInit (_, _) -> loop new_state
        | Reading (_, _, _, buf) ->
          write_file file_desc (list_to_str buf); loop new_state
        | ReadingFinished buf -> write_file file_desc (list_to_str buf); print_string "done."
        | ReadingError (er, msg) -> print_endline (list_to_str msg); exit 1
      end in
    send_packet sock hostname init_port (list_to_str (init_read_packet_serialized (str_to_list filename)));
    loop (init_read_state (str_to_list filename))

  | Write ->
    let data = read_file filename in
    let rec loop state =
      let event = recv_packet sock in
      let (new_state, mpack) = handle_unparsed_event_write event state in
      begin match mpack with
        | None -> ()
        | Some (msg, mport) -> send_packet sock hostname (match mport with Some p -> int_of_n p | None -> init_port) (list_to_str msg)
      end;
      begin match new_state with
        | WritingInit (_, _, _) -> loop new_state
        | Writing (_, _, _, _, _) -> loop new_state
        | writingFinished -> print_string "done."
        | WritingError (er, msg) -> print_endline (list_to_str msg); exit 1
      end in
    send_packet sock hostname init_port (list_to_str (init_write_packet_serialized (str_to_list filename)));
    loop (init_write_state (str_to_list filename) (str_to_list data))
