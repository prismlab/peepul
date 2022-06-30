module Lww
open FStar.List.Tot

open Library

type s = (nat (*timestamp*) * nat (*value*))

type rval = |Val : nat -> rval
            |Bot

type op = |Write : nat -> op
          |Rd

val opw : (nat * op) -> bool
let opw o =
  match o with
  |(_, Write _) -> true
  |(_, Rd) -> false

val opr : (nat * op) -> bool
let opr o = not (opw o)

val get_val : o:(nat * op){opw o} -> nat
let get_val (_, Write n) = n

val get_id_s : s -> nat
let get_id_s (t, v) = t
val get_ele_s : s -> nat
let get_ele_s (t, v) = v

let pre_cond_app_op s1 op = true
let pre_cond_prop_oper tr s1 op = true

val app_op : s1:s -> op:(nat * op) -> Tot (s2:(s * rval) {(opw op ==> s2 = (((get_id op), (get_val op)), Bot)) /\
                                                      (opr op ==> s2 = (s1, Val (get_ele_s s1)))})
let app_op s1 o =
  match o with
  |(t, Write n) -> ((t, n), Bot)
  |(_, Rd) -> (s1, Val (get_ele_s s1))

val mem_ele : v:nat
            -> l:list (nat * op)
            -> Tot (b:bool{(exists id. mem (id, Write v) l) <==> b=true})
let rec mem_ele n l =
  match l with
  |[] -> false
  |(_, Write v)::xs -> (n = v) || mem_ele n xs
  |(_, Rd)::xs -> mem_ele n xs

val init : s
let init = (0,0)

val gt : l:list (nat * op)
       -> init1:s
       -> Pure s
         (requires true)
         (ensures (fun r -> (mem ((get_id_s r), Write (get_ele_s r)) l \/ r = init1) /\
                         (forall e. mem e l /\ opw e ==> get_id_s r >= get_id e) /\ (get_id_s r >= get_id_s init1)))
         (decreases (length l))
#set-options "--z3rlimit 10000"
let rec gt l init1 =
  match l with
  |[] -> init1
  |(t, Write n)::xs -> if t > get_id_s init1 then (gt xs (t, n)) else (gt xs init1)
  |(t, Rd)::xs -> gt xs init1

val find : l:list (nat * op)
         -> id:nat
         -> Pure nat
           (requires (unique_id l) /\ mem_id id l /\ (exists v. mem (id, Write v) l))
           (ensures (fun v -> (mem (id, Write v) l) /\ mem_ele v l))
let rec find l id =
  match l with
  |(id1, Write v)::xs -> if id = id1 then v else find xs id
  |(_, Rd)::xs -> find xs id

val spec : o:(nat * op) -> tr:ae op -> rval
let spec o tr =
    match o with
    |(_, Write _) -> Bot
    |(_, Rd) -> Val (snd (gt tr.l init))

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> s1 = gt tr.l init} )
let sim tr s1 = 
  s1 = gt tr.l init

let pre_cond_merge l a b = true
let pre_cond_prop_merge ltr l atr a btr b = true

val merge : l:s
           -> a:s
           -> b:s
           -> Pure s (requires pre_cond_merge l a b)
                    (ensures (fun r -> (get_id_s a >= get_id_s b ==> r = a) /\
                                    (get_id_s a < get_id_s b ==> r = b)))
let merge l a b =
  if (get_id_s a >= get_id_s b) then a else b

val lemma : l:list (nat * op)
          -> Lemma (requires unique_id l)
                  (ensures (forall ele. mem_id (get_id ele) l /\ (exists id v. mem (id, Write v) l) ==> 
                           (mem (get_id ele, (get_op ele)) l) ==> (get_val ele = find l (get_id ele))))
                  (decreases (length l))
let rec lemma l = 
  match l with
  |[] -> ()
  |x::xs -> lemma xs 

val prop_merge : ltr:ae op
               -> l:s 
               -> atr:ae op
               -> a:s 
               -> btr:ae op
               -> b:s 
               -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                        (ensures (sim (absmerge ltr atr btr) (merge l a b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma (absmerge ltr atr btr).l;
  ()

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (get_rval (app_op st op) = spec op tr))
let prop_spec tr st op = ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (sim (append tr op) (get_st (app_op st op))))
let prop_oper tr st op = ()

val convergence : tr:ae op
                -> a:s
                -> b:s  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures a = b)
let convergence tr a b = ()

instance lww : mrdt s op rval = {
  Library.init = init;
  Library.spec = spec;
  Library.sim = sim;
  Library.pre_cond_app_op = pre_cond_app_op;
  Library.pre_cond_prop_oper = pre_cond_prop_oper;
  Library.pre_cond_merge = pre_cond_merge;
  Library.pre_cond_prop_merge = pre_cond_prop_merge;
  Library.app_op = app_op;
  Library.merge = merge;
  Library.prop_oper = prop_oper;
  Library.prop_merge = prop_merge;
  Library.prop_spec = prop_spec;
  Library.convergence = convergence
}

