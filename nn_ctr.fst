module Nn_ctr

open FStar.List.Tot

type s = (Icounter1.s * Icounter1.s)

type op =
  | Inc
  | Dec : (option nat) -> op 

type o = (nat * op)

let get_id (id,_) = id
let get_op (_,op) = op

val incr: s1:s -> Tot (s0:s{s0 = (fst s1 + 1, snd s1)})
let incr s = (fst s + 1, snd s)

val decr: s1:s -> Tot (s0:s{((fst s1 - snd s1 <= 0) ==> s0 = s1) /\ ((fst s1 - snd s1 > 0) ==> s0 = (fst s1, snd s1 + 1))})
let decr s = if (fst s > snd s) then (fst s, snd s + 1) else s

val app_op: s1:s -> op0:o -> Tot (s0:s{(Inc? (get_op op0) ==> s0 = (fst s1 + 1, snd s1)) /\
                                            (Dec? (get_op op0) /\ (fst s1 - snd s1 <= 0) ==> s0 = s1) /\
                                            (Dec? (get_op op0) /\ (fst s1 - snd s1 > 0) ==> s0 = (fst s1, snd s1 + 1))})
let app_op st op = match op with
  | _, Inc -> incr st
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

val return : d:o{Dec? (snd d)} -> Tot (v:option nat{d = (get_id d, (Dec v))})
let return (_, Dec x) = x

val unopt : #t:eqtype -> x:option t{Some? x} -> Tot (y:t{x = Some y})
let unopt (Some x) = x

val matched : i:o -> d:o -> tr:ae
            -> Pure bool (requires (get_id i <> get_id d))
                        (ensures (fun b -> (Inc? (snd i) /\ Dec? (snd d) /\ mem i tr.l /\ mem d tr.l /\ Some? (return d) /\
                                    unopt (return d) = get_id i /\ (tr.vis i d)) <==>
                          (b = true)))
let matched i d tr = (Inc? (snd i) && Dec? (snd d)) && (mem i tr.l && mem d tr.l) && Some? (return d) &&
                           unopt (return d) = get_id i && (tr.vis i d)

val isum : l:(list o){forall i. mem i l ==> Inc? (snd i)}
        -> Tot nat (decreases %[l])
let rec isum l =
  match l with
  | [] -> 0
  | (_, Inc)::xs -> 1 + isum xs

val dsum : l:(list o){forall i. mem i l ==> Dec? (snd i)}
        -> Tot nat (decreases %[l])
let rec dsum l =
  match l with
  | [] -> 0
  | (_, Dec _)::xs -> 1 + dsum xs

val sim0 : tr:ae
         -> s0:s
         -> Tot (b:bool{b = true <==> (fst s0 = isum (filter_op (fun x -> Inc? (snd x)) tr.l)) /\
                                (snd s0 = dsum (filter_op (fun x -> Dec? (snd x) && Some? (return x) &&
                                  (exists_mem tr.l (fun y -> get_id x <> get_id y && Inc? (snd y) && matched y x tr))) tr.l))})

let sim0 tr s0 = (fst s0 = isum (filter_op (fun x -> Inc? (snd x)) tr.l)) &&
                                (snd s0 = dsum (filter_op (fun x -> Dec? (snd x) && Some? (return x) &&
                                  (exists_mem tr.l (fun y -> get_id x <> get_id y && Inc? (snd y) && matched y x tr))) tr.l))

val sim1 : tr:ae
         -> s0:s
         -> Tot (b:bool{b = true <==> ((fst s0 - snd s0) = isum (filter_op (fun x -> Inc? (snd x) &&
                           not (exists_mem tr.l (fun y -> get_id x <> get_id y && mem y tr.l && Dec? (snd y) && Some? (return y)
                             && matched x y tr))) tr.l))})

let sim1 tr s0 = (fst s0 - snd s0) = isum (filter_op (fun x -> Inc? (snd x) &&
                           not (exists_mem tr.l (fun y -> get_id x <> get_id y && mem y tr.l && Dec? (snd y) && Some? (return y)
                             && matched x y tr))) tr.l)

val sim : tr:ae
        -> s0:s
        -> Tot (b:bool{b = true <==> (fst s0 = isum (filter_op (fun x -> Inc? (snd x)) tr.l)) /\
                                (snd s0 = dsum (filter_op (fun x -> Dec? (snd x) && Some? (return x) &&
                                  (exists_mem tr.l (fun y -> get_id x <> get_id y && Inc? (snd y) && matched y x tr))) tr.l)) /\
                                ((fst s0 - snd s0) = isum (filter_op (fun x -> Inc? (snd x) &&
                                  not (exists_mem tr.l (fun y -> get_id x <> get_id y && mem y tr.l && Dec? (snd y) && Some? (return y)
                                  && matched x y tr))) tr.l))})

let sim tr s0 = sim0 tr s0 && sim1 tr s0

val convergence : tr:ae
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (a = b // (fst a - snd a = fst b = snd b) /\ (fst a - snd a > 0)
                        ))
let convergence tr a b = ()

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member (get_id op) tr.l)))
             (ensures (fun res -> true))
let append tr op =
  match tr with
  |(A _ []) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                           (mem o tr.l && o1 = op && get_id o <> get_id op)) (op::[]))
  |(A _ (x::xs)) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                               (mem o tr.l && o1 = op && get_id o <> get_id op)) (op::(x::xs)))

val prop_oper0 : tr:ae
              -> st:s
              -> op:o
              -> Lemma (requires (sim tr st) /\ (Inc? (snd op)) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim0 (append tr op) (app_op st op)))

let prop_oper0 tr st op = assert(forall x. mem x tr.l ==> (append tr op).vis x op);
                          assert(fst st + 1 = fst (app_op st op));
                          assert(snd st = snd (app_op st op));
                          assert(fst (app_op st op) = isum (filter_op (fun x -> Inc? (snd x)) (append tr op).l));
                          assert(forall d. Dec? (snd d) && mem d (append tr op).l ==> not (matched op d (append tr op)));
                          assert((append tr op).l = op::(tr.l));
                          assert(forall x. exists_mem (append tr op).l (fun y -> Dec? (snd y) && mem y (append tr op).l && x y) =
                                   exists_mem tr.l (fun y -> Dec? (snd y) && mem y tr.l && x y));

                          // assert((filter_op (fun x -> Dec? (snd x) && Some? (return x) &&
                          //         (exists_mem (append tr op).l (fun y -> get_id x <> get_id y && Inc? (snd y) && matched y x (append tr op)))
                          //     ) (append tr op).l)
                          //   = (filter_op (fun x -> Dec? (snd x) && Some? (return x) &&
                          //         (exists_mem tr.l (fun y -> get_id x <> get_id y && Inc? (snd y) && matched y x tr))
                          //   ) tr.l));

                          // assert(snd (app_op st op) = dsum (filter_op (fun x -> Dec? (snd x) && Some? (return x) &&
                          //   (exists_mem (append tr op).l (fun y -> Inc? (snd y) && x = (get_id x, Dec (Some (get_id y)))))) (append tr op).l));
                          admit(); ()

val prop_oper1 : tr:ae
              -> st:s
              -> op:o
              -> Lemma (requires (sim tr st) /\ (Dec? (snd op)) /\ (fst st > snd st) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim0 (append tr op) (app_op st op)))
let prop_oper1 tr st op = ()

