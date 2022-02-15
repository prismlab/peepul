module Log
open FStar.List.Tot

open Library

val mem_id_s : id:nat -> l:list (nat * string) -> Tot (b:bool {b = true <==> (exists m. mem (id,m) l)})
let rec mem_id_s id l =
  match l with
  |[] -> false
  |(id1,m)::xs -> id = id1 || mem_id_s id xs

val unique_s : l:list (nat * string) -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |(id,m)::xs -> not (mem_id_s id xs) && unique_s xs

val pos : id:(nat * string) -> l:list (nat * string) {mem id l /\ unique_s l} -> Tot nat
let rec pos id l =
  match l with
  |id1::xs -> if id = id1 then 0 else 1 + pos id xs

val ord : id:(nat * string)
        -> id1:(nat * string) {fst id <> fst id1} 
        -> l:list (nat * string){mem id l /\ mem id1 l /\ unique_s l} 
        -> Tot (b:bool {b = true <==> pos id l < pos id1 l})
let ord id id1 l = pos id l < pos id1 l 

val total_order : l:list (nat * string) {unique_s l}
                -> Tot (b:bool)
let rec total_order l =
  match l with
  |[] -> true
  |[(id,m)] -> true
  |(id, m)::(id1, m1)::xs -> id > id1 && total_order ((id1, m1)::xs)

type s = l: list (nat (*id*) * string (*message*)) {unique_s l /\ total_order l}

type op =
  |Append : string (*message*) -> op

val get_msg : op1:(nat * op) -> Tot (s:string {exists id. op1 = (id, (Append s))}) 
let get_msg (id, (Append m)) = m

val get_id : op1:(nat * op) -> Tot (id:nat {exists m. op1 = (id, (Append m))}) 
let get_id (id, (Append m)) = id

val fst : e:(nat * string) -> Tot (id:nat {exists m. e = (id, m)})
let fst (id, m) = id

val snd : e:(nat * string) -> Tot (m:string {exists id. e = (id, m)})
let snd (id, m) = m

val app_op : s1:s 
           -> op1:(nat * op)
           -> Pure s 
             (requires not (mem_id_s (get_id op1) s1) /\ (forall id. mem_id_s id s1 ==> get_id op1 > id))
             (ensures (fun r -> (forall e. mem e r <==> mem e s1 \/ e = (get_id op1, get_msg op1))))
let app_op s1 (id, (Append m)) = (id, m)::s1

(*)instance log : datatype s op = {
  Library.app_op = app_op
}*)

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> (forall e. mem e s1 <==> mem (fst e, (Append (snd e))) tr.l) /\
                                   (forall e e1. mem e s1 /\ mem e1 s1 /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 s1 <==>
                                      mem (fst e, (Append (snd e))) tr.l /\ mem (fst e1, (Append (snd e1))) tr.l /\
                             fst e <> fst e1 /\ fst e > fst e1 /\ tr.vis (fst e1, (Append (snd e1))) (fst e, (Append (snd e))))})

let sim tr s1 = admit()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (forall id. mem_id_s id st ==> get_id op > id) /\
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))
let prop_oper tr st op = ()

val convergence1 : tr:ae op
                    -> a:s
                    -> b:s
                    -> Lemma (requires (sim tr a /\ sim tr b))
                            (ensures (forall id. mem_id_s id a <==> mem_id_s id b) /\ (forall e. mem e a <==> mem e b) /\
                                     (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ ord e e1 a /\ fst e > fst e1 <==> 
                                              mem e b /\ mem e1 b /\ fst e <> fst e1 /\ ord e e1 b /\ fst e > fst e1))
                            [SMTPat (sim tr a /\ sim tr b)]
let convergence1 tr a b = ()

  val remove_st : ele:(nat * string) -> a:s
                -> Pure s
                  (requires (mem ele a))
                  (ensures (fun r -> (forall e. mem e r <==> mem e a /\ e <> ele) /\
                                  (forall id. mem_id_s id r <==> mem_id_s id a /\ id <> fst ele) /\
                                  (forall e e1. mem e r /\ mem e1 r /\ fst e <> fst e1 /\ ord e e1 r /\ fst e > fst e1 <==>
                                           mem e a /\ mem e1 a /\ fst e <> fst e1 /\ e <> ele /\ e1 <> ele /\ fst e > fst e1 /\ ord e e1 a) /\ List.Tot.length r = List.Tot.length a - 1))
  #set-options "--z3rlimit 10000"
  let rec remove_st ele a =
    match a with
    |ele1::xs -> if ele = ele1 then xs 
                  else ((assume (forall e. mem e xs ==> fst ele1 > fst e)); ele1::(remove_st ele xs))

val lem_len : a:s -> b:s
                     -> Lemma (requires (forall id. mem_id_s id a <==> mem_id_s id b) /\ (forall e. mem e a <==> mem e b) /\
                                      (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ ord e e1 a /\ fst e > fst e1 <==> 
                                               mem e b /\ mem e1 b /\ fst e <> fst e1 /\ ord e e1 b /\ fst e > fst e1))
                           (ensures (List.Tot.length a = List.Tot.length b))
let rec lem_len a b = 
  match a,b with
  |[],[] -> ()
  |x::xs, _ -> lem_len xs (remove_st x b)

val lem_same : a:s -> b:s
             -> Lemma (requires (forall id. mem_id_s id a <==> mem_id_s id b) /\ (forall e. mem e a <==> mem e b) /\
                                  (List.Tot.length a = List.Tot.length b) /\
                                  (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a <==> 
                                           mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b))
                       (ensures (forall e. mem e a /\ mem e b ==> pos e a = pos e b))

#set-options "--z3rlimit 10000000"
let rec lem_same a b = admit();
  match a, b with
  |[],[] -> ()
  |x::xs, _ -> lem_same xs (remove_st x b)

val lem_same1 : a:s -> b:s
               -> Lemma (requires (forall id. mem_id_s id a <==> mem_id_s id b) /\ (forall e. mem e a <==> mem e b) /\
                                    (List.Tot.length a = List.Tot.length b) /\
                                    (forall e e1. mem e a /\ mem e1 a /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 a <==> 
                                             mem e b /\ mem e1 b /\ fst e <> fst e1 /\ fst e > fst e1 /\ ord e e1 b) /\
                                             (forall e. mem e a /\ mem e b ==> pos e a = pos e b))
                                 (ensures a = b)

#set-options "--z3rlimit 10000000"
let rec lem_same1 a b =
    match a, b with
    |[],[] -> ()
    |x::xs, _ -> lem_same1 xs (remove_st x b)
    
val convergence : tr:ae op
                  -> a:s
                  -> b:s
                  -> Lemma (requires (sim tr a /\ sim tr b))
                          (ensures a = b)
                          [SMTPat (sim tr a /\ sim tr b)]
let convergence tr a b = 
  convergence1 tr a b;
  lem_len a b;
  lem_same a b; 
  lem_same1 a b;
  ()

val merge1 : l:s -> a:s -> b:s
           -> Pure s
             (requires true)
             (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b)))
let merge1 l a b = admit()

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (fun res -> res = merge1 l a b))

#set-options "--z3rlimit 10000"
let merge ltr l atr a btr b = 
  merge1 l a b

val prop_merge : ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> get_id e < get_id e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==> get_id e < get_id e1) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))
#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = ()



(*)instance _ : mrdt s op log = {
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence;
  Library.sim = sim;
  Library.prop_oper = prop_oper*)

