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
let sl : trace = ["L"]
let sr : trace = ["R"]
let s : trace = ["S"]


let bind (t : trace) (l2 : trace list) : trace list =
  List.map (fun t' -> t @ t') l2

let step m : trace list =
  let rec aux m : trace list =
    match observe m with
    (* Internal auxs compute as nothing *)
    | TauF x -> aux x

    (* We finished the computation *)
    | RetF _ ->
      (* print_string "DONE "; *)
      [[]]

    (* The only residual effect is Print, which carries just a string *)
    | VisF (Inl1 Plus, k) ->
      (* print_string "Plus "; *)
      aux (k (Obj.magic true))
      @ aux (k (Obj.magic true))
    | VisF (Inl1 Sched, k) ->
      (* print_string "Sched "; *)
      aux (k (Obj.magic Left))
      @ aux (k (Obj.magic Right))
      @ aux (k (Obj.magic Synchronize))
      (* bind sl (aux (k (Obj.magic Left)))
       * @ bind sr (aux (k (Obj.magic Right)))
       * @ bind s (aux (k (Obj.magic Synchronize))) *)

    | VisF (Inr1 (Inl1 (Send c)), k) ->
      (* print_string ("!" ^ camlstring_of_coqstring c ^ " "); *)
      bind (emit c) (aux (k (Obj.magic ())))
    | VisF (Inr1 (Inl1 (Rcv c)), k) ->
      (* print_string ("?" ^ camlstring_of_coqstring c ^ " "); *)
      bind (rcv c) (aux (k (Obj.magic ())))

    | VisF (Inr1 (Inr1 (Inl1 _)), k) ->
      (* print_string "τ "; *)
      bind (synch) (aux (k (Obj.magic ())))

    | VisF (Inr1 (Inr1 (Inr1 _)), _) ->
      (* print_string "DEAD "; *)
      [["dead"]]
      
  in
  let res = List.filter (
      fun t -> (t == []) || (List.hd (List.rev t) != "dead")) (aux m) in (* print_newline () ; *) res

(* Main *)

let print_trace (t : trace) : unit =
  List.iter (fun s -> print_string s; print_string " ; ") t;
  print_newline ()

let print_traces (ts : trace list) : unit =
  List.iter print_trace ts

let () =
  print_string "Run 1:\n";
  print_traces (step p1);
  print_string "Run 2:\n";
  print_traces (step p2);
  print_string "Run 3:\n";
  print_traces (step p3);
  print_string "Run 4:\n";
  print_traces (step p4);
  print_string "Run 5:\n";
  print_traces (step p5);
  print_string "Run 6:\n";
  print_traces (step p6);
  print_string "Run 7:\n";
  print_traces (step p7)


