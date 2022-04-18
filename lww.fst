module Lww
open FStar.List.Tot

open Library

type s = (nat (*timestamp*) * nat (*value*))

type op = nat (*value*)

val get_id_s : s -> nat
let get_id_s (t, v) = t
val get_ele_s : s -> nat
let get_ele_s (t, v) = v

let pre_cond_op s1 op = true

val app_op : s1:s -> op:(nat * op) -> Tot (s2:s {s2 = ((get_id op), (get_op op))})
let app_op (t, v) (t1, v1) = (t1, v1)

val mem_ele : v:nat
            -> l:list (nat * op)
            -> Tot (b:bool{(exists id. mem (id, v) l) <==> b=true})
let rec mem_ele n l =
  match l with
  |[] -> false
  |(_, v)::xs -> (n = v) || mem_ele n xs

val init : s
let init = (0,0)

val gt : l:list (nat * op)
       -> init1:s
       -> Pure s
         (requires true)
         (ensures (fun r -> (mem ((get_id_s r), (get_ele_s r)) l \/ r = init1) /\
                         (forall e. mem e l ==> get_id_s r >= get_id e) /\ (get_id_s r >= get_id_s init1)))
         (decreases (length l))
#set-options "--z3rlimit 10000"
let rec gt l init1 =
  match l with
  |[] -> init1
  |(t, n)::xs -> if t > get_id_s init1 then (gt xs (t,n)) else (gt xs init1)

val find : l:list (nat * op)
         -> id:nat
         -> Pure nat
           (requires (unique_id l) /\ mem_id id l)
           (ensures (fun v -> (mem (id, v) l) /\ mem_ele v l))
let rec find l id =
  match l with
  |(id1, v)::xs -> if id = id1 then v else find xs id

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s
        -> Tot (b:bool {b = true <==> s1 = gt tr.l init} )
let sim tr s1 = 
  s1 = gt tr.l init

let pre_cond_merge ltr l atr a btr b = true

val merge : ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s 
          -> btr:ae op
          -> b:s 
          -> Pure s (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                    (ensures (fun res -> ((get_id_s a >= get_id_s b) ==> res = a) /\
                                      ((get_id_s b > get_id_s a) ==> res = b) /\
                                      (get_id_s res >= get_id_s a /\ get_id_s res >= get_id_s b /\ 
                                       get_id_s res >= get_id_s l) /\ (res = a \/ res = b)))
#set-options "--z3rlimit 10000"
let merge ltr l atr a btr b = 
  assert ((get_id_s a = get_id_s b) ==> (get_id_s l = get_id_s a) /\ (get_id_s l = get_id_s b));
  if (get_id_s a >= get_id_s b) then a else b

val lemma : l:list (nat * op)
          -> Lemma (requires unique_id l)
                  (ensures (forall ele. mem_id (get_id ele) l ==> 
                           (mem (get_id ele, (get_op ele)) l) ==> (get_op ele = find l (get_id ele))))
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
                        (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma (absmerge ltr atr btr).l;
  ()

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ 
                                (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op))
                      (ensures (sim (append tr op) (app_op st op)))

let prop_oper tr st op = ()

val convergence : tr:ae op
                -> a:s
                -> b:s  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures a = b)
let convergence tr a b = ()

instance _ : mrdt s op = {
  Library.sim = sim;
  Library.pre_cond_op = pre_cond_op;
  Library.app_op = app_op;
  Library.prop_oper = prop_oper;
  Library.pre_cond_merge = pre_cond_merge;
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence
}
