open Model

(* The driver loop ---------------------------------------------------------- *)

(* Taken from Xavier Leroy's Camlcoq library, which is part of CompCert under
   Gnu Public License version 2 or later.  *)
let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
    | [] -> r
    | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

(* We output the list of traces *)
type trace = string list

let emit c : trace = ["!" ^ camlstring_of_coqstring c]
let rcv  c : trace = ["?" ^ camlstring_of_coqstring c]
let synch : trace = ["τ"]

let bind (t : trace) (l2 : trace list) : trace list =
  List.map (fun t' -> t @ t') l2

let step m : trace list =
  let rec aux m : trace list =
    match observe m with
    (* Internal auxs compute as nothing *)
    | TauF x -> aux x

    (* We finished the computation *)
    | RetF _ ->  [[]]

    (* The only residual effect is Print, which carries just a string *)
    | VisF (Inl1 Plus, k) ->
      print_string "0 ";
      aux (k (Obj.magic true))
      @ aux (k (Obj.magic true))
    | VisF (Inl1 Sched, k) ->
      print_string "1 ";
      aux (k (Obj.magic Left))
      @ aux (k (Obj.magic Right))
      @ aux (k (Obj.magic Synchronize))

    | VisF (Inr1 (Inl1 (Send c)), k) ->
      print_string "2 ";
      bind (emit c) (aux (k (Obj.magic ())))
    | VisF (Inr1 (Inl1 (Rcv c)), k) ->
      print_string "3 ";
      bind (rcv c) (aux (k (Obj.magic ())))

    | VisF (Inr1 (Inr1 (Inl1 _)), k) ->
      print_string "4 ";
      bind (synch) (aux (k (Obj.magic ())))

    | VisF (Inr1 (Inr1 (Inr1 _)), _) ->
      print_string "5 ";
      [[]]
      
  in
  aux m 

(* Main *)

let print_trace (t : trace) : unit =
  List.iter (fun s -> print_string s; print_string " ; ") t;
  print_newline ()

let print_traces (ts : trace list) : unit =
  List.iter print_trace ts

let () = print_traces (step p)

