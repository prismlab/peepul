module Nn_ctr

open FStar.List.Tot

type s = (Icounter1.s * Icounter1.s)

type op =
  | Inc
  | Dec : (option s) -> op

type o = (nat * op)

let get_id (id,_) = id
let get_op (_,op) = op


val incr: s1:s -> Tot (s0:s{s0 = (fst s1 + 1, snd s1)})
let incr s = (fst s + 1, snd s)

val decr: s1:s -> Tot (s0:option s{((fst s1 - snd s1 <= 0) ==> s0 = None) /\ ((fst s1 - snd s1 > 0) ==> s0 = Some (fst s1, snd s1 + 1))})
let decr s = if (fst s > snd s) then Some (fst s, snd s + 1) else None

val app_op: s1:s -> op0:o -> Tot (s0:option s{(Inc? (get_op op0) ==> s0 = Some (fst s1 + 1, snd s1)) /\
                                            (Dec? (get_op op0) /\ (fst s1 - snd s1 <= 0) ==> s0 = None) /\
                                            (Dec? (get_op op0) /\ (fst s1 - snd s1 > 0) ==> s0 = Some (fst s1, snd s1 + 1))})
let app_op st op = match op with
  | _, Inc -> Some (incr st)
  | _, Dec x -> decr st

val member : id:nat
           -> l:list o
           -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member n xs

val unique : l:list o
           -> Tot bool
let rec unique l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member id xs) && unique xs

noeq type ae =
     |A : vis:(o -> o -> Tot bool) -> l:list o {unique l} -> ae

assume val axiom_ae : l:ae
                   -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\
                           get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*) /\
                           (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                           (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*) ))
                           [SMTPat (unique l.l)]

val position_o : e:o
             -> s1:(list o) {mem e s1 /\ unique s1}
             -> Tot nat  (decreases (s1))
let rec position_o e s1 =
      match s1 with
      |x::xs -> if (e = x) then 0 else 1 + (position_o e xs)

val ord : e1:o
          -> e2:o {(fst e1) <> (fst e2)}
          -> s1:(list o) {mem e1 s1 /\ mem e2 s1 /\ unique s1}
          -> Tot (r:bool {(position_o e1 s1 < position_o e2 s1) <==> r = true})
let ord e1 e2 s1 = (position_o e1 s1 < position_o e2 s1)

val filter_op : f:(o -> bool)
           -> l:list o
           -> Tot (l1:list o {(forall e. mem e l1 <==> (mem e l /\ f e))})
let rec filter_op f l =
  match l with
  | [] -> []
  | hd::tl -> if f hd then hd::(filter_op f tl) else filter_op f tl

val forall_mem : #t:eqtype
             -> l:list t
             -> f:(t -> bool)
             -> Tot(b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forall_mem l f =
       match l with
       | [] -> true
       | hd::tl -> if f hd then forall_mem tl f else false

val exists_mem : #t:eqtype
            -> l:list t
            -> f:(t -> bool)
            -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true})
let rec exists_mem l f =
  match l with
  | [] -> false
  | hd::tl -> if f hd then true else exists_mem tl f

#set-options "--initial_fuel 10 --ifuel 10 --initial_ifuel 10 --fuel 10 --z3rlimit 10000000000"
val ctr : s0:s -> Tot (z:int{z = fst s0 - snd s0})
let ctr s = fst s - snd s

// val matched : i:o -> d:o -> tr:ae
//             -> Pure bool (requires (get_id i <> get_id d))
//                         (ensures (fun b -> (Inc? i /\ Dec? d /\ mem i tr.l /\ mem d tr.l /\ return d = Some (get_id e, get_ele e) /\ (tr.vis e d)) <==> (b = true)))
// let matched e d tr = (is_enqueue e && is_dequeue d && mem e tr.l && mem d tr.l && return d = Some (get_id e, get_ele e)) && (tr.vis e d)


// val sim0 : tr:ae
//          -> s0:s
//          -> Tot(b:bool{b = true <==>
//                        (forall i. fst s0 - snd s0 = mem i tr.l /\
//                                    (forall d. mem d tr.l /\ get_id i <> get_id d /\ Dec? d ==> (not (matched i d tr))))
//                        })



