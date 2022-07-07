module Alpha_map
open FStar.List.Tot

#set-options "--query_stats"

open Library

type op (alpha_op:eqtype) = 
  |Get : nat (*key*) -> alpha_op -> op (alpha_op)
  |Set : nat (*key*) -> alpha_op -> op (alpha_op)

val get_key : #o:eqtype -> op1:(nat * op o) -> Tot (k:nat {(exists id op2. op1 = (id, (Get k op2))) \/ 
                                                     (exists id op2. op1 = (id, (Set k op2)))})
let get_key op1 =
  match op1 with
  |(_, Get k _) -> k
  |(_, Set k _) -> k

val opget : #o:eqtype -> o1:(nat * (op o)) -> Tot (b:bool {b=true <==> (exists id k alphaop. (o1 = (id, (Get k alphaop))))})
let opget op1 =
    match op1 with
    |(_, (Get _ _)) -> true
    |_ -> false

val opset : #o:eqtype -> o1:(nat * (op o)) -> Tot (b:bool {b=true <==> (exists id k alphaop. (o1 = (id, (Set k alphaop))))})
let opset op1 = not (opget op1)

val get_alpha_op : #o:eqtype -> op1:(nat * op o) -> Tot (s:o {(exists id k. op1 = (id, (Get k s))) \/
                                                          (exists id k. op1 = (id, (Set k s)))})
let get_alpha_op op1 =
  match op1 with
  |(_, Get _ o) -> o
  |(_, Set _ o) -> o

val get_key_s : #st:eqtype -> s:(nat * st) -> Tot (s1:nat {(exists c. s = (s1,c))})
let get_key_s (k, _) = k

val mem_key_s : #st:eqtype 
              -> ele1:nat
              -> l:list (nat * st)
              -> Tot (b:bool {b=true <==> (exists c. mem (ele1,c) l) /\ (exists e. mem e l /\ get_key_s e = ele1)})
let rec mem_key_s ele1 l =
  match l with
  |[] -> false
  |x::xs -> get_key_s x = ele1 || mem_key_s ele1 xs

val unique_key : #st:eqtype -> list (nat * st) -> bool
let rec unique_key l =
  match l with
  |[] -> true
  |(ele,_)::xs -> not (mem_key_s ele xs) && unique_key xs

val get_val_s1 : #st:eqtype -> s:(nat * st) -> Tot (c:st {(exists i. s = (i,c))})
let get_val_s1 (_, c) = c

type s (alpha_st:eqtype) = l:list (nat * alpha_st) {unique_key l}

let init_a = []

val get_val_s : #st:eqtype -> #o:eqtype -> #r:eqtype -> {| mrdt st o r|}
                -> i:nat -> s1:s st -> Tot (c:st {(mem_key_s i s1 ==> mem (i,c) s1 /\ 
                                         (exists e. mem e s1 /\ e = (i,c) /\ c = get_val_s1 #st e)) /\ 
                                         (not (mem_key_s i s1) ==> c = init #st #o #r)})
let rec get_val_s #st #o #r i s1 =
  match s1 with
  |[] -> init #st #o #r
  |x::xs -> if get_key_s x = i then get_val_s1 x else get_val_s #st #o #r i xs

val mem_op : #o:eqtype -> ele1:op o
           -> l:list (nat * (op o))
           -> Tot (b:bool {b=true <==> (exists id. mem (id, ele1) l) })
let rec mem_op ele2 l =
  match l with
  |[] -> false
  |(_, ele1)::xs -> ele1 = ele2 || mem_op ele2 xs

val mem_key : #o:eqtype -> i:nat -> l:list (nat * op o) -> Tot (b:bool {b=true <==> (exists id op. mem (id, (Get i op)) l) \/
                                                                           (exists id op. mem (id, (Set i op)) l)})
let rec mem_key ele2 l =
  match l with
  |[] -> false
  |(_, (Get ele1 _))::xs -> ele1 = ele2 || mem_key ele2 xs
  |(_, (Set ele1 _))::xs -> ele1 = ele2 || mem_key ele2 xs

val filter_uni : #op:eqtype 
               -> f:((nat * op) -> bool)
               -> l:list (nat * op) 
               -> Lemma (requires (unique_id l ))
                       (ensures (unique_id (filter f l)))
                       [SMTPat (filter f l)]
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

val filtero : #o:eqtype 
            -> f:((nat * (op o)) -> bool)
            -> l:list (nat * (op o)) {unique_id l}
            -> Tot (l1:list (nat * (op o)) {(forall e. mem e l1 <==> mem e l /\ (f e)) /\ unique_id l1})
let rec filtero f l =
  match l with
  |[] -> []
  |hd::tl -> if (f hd) then hd::(filtero f tl) else filtero f tl

val forallo : #o:eqtype
            -> f:((nat * o) -> bool)
            -> l:list (nat * o)
            -> Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forallo f l =
  match l with
  |[] -> true
  |hd::tl -> if f hd then forallo f tl else false

val project_op : #o:eqtype 
               -> o1:(nat * (op o))
               -> Tot (o2:(nat * o) {(o2 = (get_id o1, get_alpha_op o1))})
let project_op op =
  match op with
  |(id, (Set k alpha_op)) -> (id, alpha_op)
  |(id, (Get k alpha_op)) -> (id, alpha_op)

val project1 : #o:eqtype
             -> i:nat
             -> l:ae (op o)
             -> Pure (list (nat * o))
                    (requires true)
                    (ensures (fun r -> (forall id. mem_id id r <==> (mem_id id l.l /\ get_key (get_eve id l.l) = i /\ 
                      opset (get_eve id l.l))) /\ unique_id r /\ (forall e ao. mem e l.l /\ get_op e = (Set i ao) ==> (exists e1. mem e1 r /\ e1 = (get_id e, ao))) /\ (forall e. mem e l.l /\ get_key e = i /\ opset e ==> mem (project_op e) r) /\
                    (forall e. mem (get_id e, (Set i (get_op e))) l.l <==> mem e r)))
               (decreases List.Tot.length l.l)

#set-options "--z3rlimit 100"
let rec project1 #o i l =
  match l.l with
  |[] -> []
  |x::xs -> if (get_key x = i && opset x) then (project_op x)::project1 i (A l.vis xs) else (project1 i (A l.vis xs))

val project : #o:eqtype
            -> i:nat
            -> l:ae (op o)
            -> Pure (ae o)
                   (requires true)
                   (ensures (fun r -> (forall id. mem_id id r.l <==> (mem_id id l.l /\ opset (get_eve id l.l) /\ get_key (get_eve id l.l) = i)) /\ 
                       unique_id r.l /\ (forall e ao. mem e l.l /\ get_op e = (Set i ao) ==> (exists e1. mem e1 r.l /\ e1 = (get_id e, ao))) /\ (forall e. mem e l.l /\ get_key e = i /\ opset e ==> mem (project_op e) r.l) /\
                   (forall e e1. (get_id e <> get_id e1 /\ mem (get_id e, (Set i (get_op e))) l.l /\ 
             mem (get_id e1, (Set i (get_op e1))) l.l /\ l.vis (get_id e, (Set i (get_op e))) (get_id e1, (Set i (get_op e1)))) <==> 
                   (get_id e <> get_id e1 /\ mem e r.l /\ mem e1 r.l /\ r.vis e e1))))

#set-options "--z3rlimit 100000"
let project i l =
  (A (fun o o1 -> (mem (get_id o, (Set i (get_op o))) l.l && mem (get_id o1, (Set i (get_op o1))) l.l && get_id o <> get_id o1 && l.vis (get_id o, (Set i (get_op o))) (get_id o1, (Set i (get_op o1))))) (project1 i l))

val pre_cond_do_a : #st1:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st1 o r|}
                  -> s1:s st1 -> op1:(nat * op o)
                  -> Tot (b:bool {b = true <==> pre_cond_do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) s1) (project_op op1)})
let pre_cond_do_a #st1 #o #r s1 op = 
    pre_cond_do #st1 #o #r (get_val_s #st1 #o #r (get_key op) s1) (project_op op)

val pre_cond_prop_do_a : #st1:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st1 o r|} 
                       -> tr:ae (op o)
                       -> st:s st1
                       -> op1:(nat * (op o)) 
                       -> Pure bool
                         (requires (not (mem_id (get_id op1) tr.l) /\
                                   (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0))
                      (ensures (fun b -> (b=true <==> pre_cond_prop_do #st1 #o #r (project (get_key op1) (abs_do tr op1))
                                     (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))))
let pre_cond_prop_do_a #st1 #o #r tr st op1 =
  pre_cond_prop_do #st1 #o #r (project (get_key op1) (abs_do tr op1))
    (get_val_s #st1 #o #r (get_key op1) st) (project_op op1)

val update : #st1:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st1 o r|}
           -> st:s st1
           -> k:nat
           -> v:st1
           -> Pure (s st1)
                  (requires mem_key_s k st)
                  (ensures (fun res -> unique_key res /\ (forall e. mem_key_s e st <==> mem_key_s e res) /\
                    (forall ch. ch <> k ==> (get_val_s #st1 #o #r ch st = get_val_s #st1 #o #r ch res)) /\
                      ((v = get_val_s #st1 #o #r k res))))
#set-options "--z3rlimit 1000"
let rec update #st1 #o #r st k v = 
  match st with
  |(k1,v1)::xs -> if k = k1 then (k1,v)::xs else (k1,v1)::update #st1 #o #r xs k v

val do_a : #st1:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st1 o r|}
         -> st:s st1 -> op1:(nat * op o)
         -> Pure ((s st1) * r)
           (requires pre_cond_do_a #st1 #o #r st op1)
           (ensures (fun res -> (opget op1 ==> (get_rval res = get_rval (do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))) /\ (get_st res = st)) /\
                           (opset op1 ==> (get_rval res = get_rval (do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))) /\ (forall k. k <> get_key op1 ==> (get_val_s #st1 #o #r k st = get_val_s #st1 #o #r k (get_st res))) /\ (not (mem_key_s (get_key op1) st) ==> (forall e. mem e (get_st res) <==> mem e st \/ e = (get_key op1, (get_st ((do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))))))) /\
               (mem_key_s (get_key op1) st ==> (forall e. mem e (get_st res) <==> mem e (update #st1 #o #r st (get_key op1) (get_st (do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1)))))) /\
                          (forall k. mem_key_s k (get_st res) <==> mem_key_s k st \/ k = get_key op1) /\ mem_key_s (get_key op1) (get_st res) /\ (get_val_s #st1 #o #r (get_key op1) (get_st res) = 
                    (get_st (do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))))) /\ unique_key (get_st res)))

#set-options "--z3rlimit 1000"
let do_a #st1 #o #r st op1 = 
  match op1 with
  |(_, Get k ao) -> let (_, ret) = (do #st1 #o #r (get_val_s #st1 #o #r k st) (project_op op1)) in (st, ret)
  |(_, Set k ao) -> let (v, ret) = (do #st1 #o #r (get_val_s #st1 #o #r k st) (project_op op1)) in (if mem_key_s (get_key op1) st then (update #st1 #o #r st (get_key op1) v, ret) else ((get_key op1, v)::st, ret))

val unique_keys : list nat -> Tot bool
let rec unique_keys l =
    match l with
    |[] -> true
    |x::xs -> not (mem x xs) && unique_keys xs

val get_lst : #st: eqtype -> m:s st -> Pure (list nat)
                     (requires true)
                     (ensures (fun r -> (forall i. mem i r <==> mem_key_s i m) /\ unique_keys r))
let rec get_lst m =
  match m with
  |[] -> []
  |(i,x)::xs -> i::get_lst xs

val spec_a : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
           -> o1:(nat * (op o))
           -> tr:ae (op o)
           -> Pure r
             (requires opget o1)
             (ensures (fun res -> res = (spec #st #o #r) (project_op o1) (project (get_key o1) tr)))
let spec_a #st #o #r o1 tr = (spec #st #o #r) (project_op o1) (project (get_key o1) tr)

val sim_a : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
          -> tr:ae (op o)
          -> s1:s st
          -> Tot (b:bool {(b = true) <==> (forall e1. mem e1 s1 ==> (exists e. mem e tr.l /\ get_key e = get_key_s e1 /\ opset e)) /\
            (forall k. mem_key_s k s1 ==> (sim #st #o #r) (project k tr) (get_val_s #st #o #r k s1)) /\
            (forall e. mem e tr.l /\ opset e ==> (exists e1. mem e1 s1 /\ get_key e = get_key_s e1))})

#set-options "--z3rlimit 1000"
let sim_a #st #o #r tr s1 =
  forallb (fun e -> (existsb (fun e1 -> get_key e1 = get_key_s e && opset e1) tr.l)) s1 &&
  forallb (fun e -> (sim #st #o #r) (project (get_key_s e) tr) (get_val_s #st #o #r (get_key_s e) s1)) s1 &&
  forallb (fun e -> (existsb (fun e1 -> get_key e = get_key_s e1) s1)) (filter (fun e -> opset e) tr.l)

class alpha_map (st:eqtype) (o:eqtype) (r:eqtype) (m:mrdt st o r) = {

  lemma4 : tr:ae (op o) -> s1:s st
         -> Lemma (requires (sim_a #st #o #r) tr s1)
                 (ensures (forall i. (sim #st #o #r) (project i tr) (get_val_s #st #o #r i s1)));

  lemma1 : tr:ae (op o)
         -> s1:s st
         -> op1:(nat * (op o))
         -> Lemma (requires ((sim_a #st #o #r) tr s1) /\ (not (mem_id (get_id op1) tr.l)) /\
                           (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                           pre_cond_do #st #o #r (get_val_s #st #o #r (get_key op1) s1) (project_op op1))
                 (ensures (forall i. mem_key_s i (get_st (do_a #st #o #r s1 op1)) /\ i <> get_key op1 ==>
                   ((forall e. mem e (project i (abs_do tr op1)).l <==> mem e (project i tr).l) /\
                   (forall e e1. mem e (project i (abs_do tr op1)).l /\ mem e1 (project i (abs_do tr op1)).l /\ 
                        get_id e <> get_id e1 /\ (project i (abs_do tr op1)).vis e e1 <==> 
                 mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1) /\
                   (get_val_s #st #o #r i (get_st (do_a #st #o #r s1 op1)) = (get_val_s #st #o #r i s1))) ==>
                     (sim #st #o #r) (project i (abs_do tr op1)) (get_val_s #st #o #r i (get_st (do_a #st #o #r s1 op1)))));

  lemma7 : tr:ae o -> s1:st -> tr1:ae o
         -> Lemma (requires (sim #st #o #r) tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                           (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                    mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                 (ensures ((sim #st #o #r) tr1 s1));

  lemma2 : s1:s st
         -> Lemma (requires true)
                 (ensures (forall e. mem e s1 ==> (get_val_s #st #o #r (get_key_s e) s1 = get_val_s1 #st e)))
}

val convergence_a1 : #st:eqtype -> #o:eqtype -> #r:eqtype -> {| mrdt st o r|} 
                   -> tr:ae (op o)
                   -> a:s st
                   -> b:s st
                   -> Lemma (requires ((sim_a #st #o #r) tr a /\ (sim_a #st #o #r) tr b))
                         (ensures (forall e. mem_key_s e a <==> mem_key_s e b))
let convergence_a1 tr a b = ()

val lem_oper1 : #o:eqtype
              -> tr:ae (op o)
              -> op:(nat * (op o))
              -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (opset op ==> (forall e. mem e (project (get_key op) (abs_do tr op)).l <==>
                                      mem e (abs_do (project (get_key op) tr) (project_op op)).l)))
#set-options "--z3rlimit 1000"
let lem_oper1 tr op = ()

val lem_oper2 : #o:eqtype
              -> tr:ae (op o)
              -> op:(nat * (op o))
              -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (opset op ==> (forall e e1. mem e (project (get_key op) (abs_do tr op)).l /\
                        mem e1 (project (get_key op) (abs_do tr op)).l /\ (get_id e <> get_id e1) /\
                        (project (get_key op) (abs_do tr op)).vis e e1  <==> 
                        mem e (abs_do (project (get_key op) tr) (project_op op)).l /\
                    mem e1 (abs_do (project (get_key op) tr) (project_op op)).l /\ get_id e <> get_id e1 /\
                        (abs_do (project (get_key op) tr) (project_op op)).vis e e1)))
#set-options "--z3rlimit 10000"
let lem_oper2 tr op = lem_oper1 tr op

val lem_oper3 : #o:eqtype
              -> tr:ae (op o)
              -> op:(nat * (op o))
              -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (forall i. i <> (get_key op) ==> (forall e. mem e (project i (abs_do tr op)).l <==> mem e (project i tr).l) /\
         (forall e e1. mem e (project i (abs_do tr op)).l /\ mem e1 (project i (abs_do tr op)).l /\ get_id e <> get_id e1 /\
                    (project i (abs_do tr op)).vis e e1 <==> 
        mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1)))
#set-options "--z3rlimit 1000"
let lem_oper3 tr op = 
  lem_oper1 tr op;
  lem_oper2 tr op

val lem_oper : #o:eqtype
             -> tr:ae (op o)
             -> op:(nat * (op o))
             -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                               (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                     (ensures (opset op ==> (forall e. mem e (project (get_key op) (abs_do tr op)).l <==> 
                                    mem e (abs_do (project (get_key op) tr) (project_op op)).l) /\
               (forall e e1. mem e (project (get_key op) (abs_do tr op)).l /\
                        mem e1 (project (get_key op) (abs_do tr op)).l /\ (get_id e <> get_id e1) /\
                        (project (get_key op) (abs_do tr op)).vis e e1  <==> 
                        mem e (abs_do (project (get_key op) tr) (project_op op)).l /\
                    mem e1 (abs_do (project (get_key op) tr) (project_op op)).l /\ get_id e <> get_id e1 /\
                        (abs_do (project (get_key op) tr) (project_op op)).vis e e1)) /\
         (forall i. i <> (get_key op) ==> (forall e. mem e (project i (abs_do tr op)).l <==> mem e (project i tr).l) /\
         (forall e e1. mem e (project i (abs_do tr op)).l /\ mem e1 (project i (abs_do tr op)).l /\ get_id e <> get_id e1 /\
                    (project i (abs_do tr op)).vis e e1 <==> 
        mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1)))

#set-options "--z3rlimit 1000"
let lem_oper tr op = 
  lem_oper1 tr op;
  lem_oper2 tr op;
  lem_oper3 tr op

val prop_do1 : #st1:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st1 o r|} 
             -> tr:ae (op o)
             -> st:s st1
             -> op1:(nat * (op o)) 
             -> Lemma (requires (sim_a #st1 #o #r tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                               (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                            pre_cond_do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1) /\
                            pre_cond_prop_do #st1 #o #r (project (get_key op1) (abs_do tr op1)) 
                                               (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))
                     (ensures (forall e. mem e (abs_do tr op1).l /\ opset e ==> (exists e1. mem e1 (get_st (do_a #st1 #o #r st op1)) /\ get_key e = get_key_s e1)))

#set-options "--z3rlimit 1000"
let prop_do1 tr st op = lem_oper tr op

val prop_do2 : #st1:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st1 o r|} 
             -> tr:ae (op o)
             -> st:s st1
             -> op1:(nat * (op o)) 
             -> Lemma (requires (sim_a #st1 #o #r tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                               (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                               pre_cond_do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1) /\
                               pre_cond_prop_do #st1 #o #r (project (get_key op1) (abs_do tr op1)) 
                                                  (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))
                     (ensures (forall e1. mem e1 (get_st (do_a #st1 #o #r st op1)) ==> (exists e. mem e (abs_do tr op1).l /\ get_key e = get_key_s e1 /\ opset e)))

#set-options "--z3rlimit 1000"
let prop_do2 #st1 #o #r tr st op =
  lem_oper tr op;
  prop_do1 #st1 #o #r tr st op

val prop_do3 : #st1:eqtype -> #o:eqtype -> #r:eqtype -> #m:(mrdt st1 o r) -> {|alpha_map st1 o r m|}
             -> tr:ae (op o)
             -> st:s st1
             -> op1:(nat * (op o)) 
             -> Lemma (requires (sim_a #st1 #o #r tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                               (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                               pre_cond_do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1) /\
                               pre_cond_prop_do #st1 #o #r (project (get_key op1) (abs_do tr op1)) 
                                                  (get_val_s #st1 #o #r (get_key op1) st) (project_op op1))
                     (ensures (forall k. mem_key_s k (get_st (do_a #st1 #o #r st op1)) /\ k <> get_key op1 ==>
   (sim #st1 #o #r) (project k (abs_do tr op1)) (get_val_s #st1 #o #r k (get_st (do_a #st1 #o #r st op1)))))

#set-options "--z3rlimit 1000"
let prop_do3 #st1 #o #r #m tr st op = 
  lem_oper tr op;
  prop_do1 #st1 #o #r tr st op;
  prop_do2 #st1 #o #r tr st op;
  lemma1 #st1 #o #r #m tr st op

val prop_do_a : #st1:eqtype -> #o:eqtype -> #r:eqtype -> #m:(mrdt st1 o r) -> {|alpha_map st1 o r m|}
              -> tr:ae (op o)
              -> st:s st1
              -> op1:(nat * (op o)) 
              -> Lemma (requires (sim_a #st1 #o #r tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                pre_cond_do #st1 #o #r (get_val_s #st1 #o #r (get_key op1) st) (project_op op1) /\
                                pre_cond_prop_do #st1 #o #r (project (get_key op1) (abs_do tr op1)) 
                                                   (get_val_s #st1 #o #r (get_key op1) st) (project_op op1) /\
     ((sim #st1 #o #r) (project (get_key op1) (abs_do tr op1)) (get_val_s #st1 #o #r (get_key op1) (get_st (do_a #st1 #o #r st op1)))))
                     (ensures (sim_a #st1 #o #r (abs_do tr op1) (get_st (do_a #st1 #o #r st op1))))

#set-options "--z3rlimit 1000"
let prop_do_a #st1 #o #r #m tr st op = 
  lem_oper tr op;
  prop_do1 #st1 #o #r tr st op;
  prop_do2 #st1 #o #r tr st op;
  prop_do3 #st1 #o #r #m tr st op

val get_key_lst : #st:eqtype 
                -> l:s st -> a:s st -> b:s st
                -> Pure (list nat)
                  (requires true)
                  (ensures (fun r -> (forall i. mem i r <==> mem_key_s i a \/ mem_key_s i b) /\ unique_keys r))
                  (decreases %[l;a;b])

let rec get_key_lst #st l a b =
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> get_key_lst xs a b
  |[],x::xs,_ -> if (mem_key_s (get_key_s x) b) then get_key_lst [] xs b else (get_key_s x)::(get_key_lst [] xs b)
  |[],[],x::xs -> (get_key_s x)::(get_key_lst [] [] xs)

val pre_cond_merge_a : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
                     -> l:s st -> a:s st -> b:s st 
                     -> Tot (b1:bool {b1=true <==> (forall e. mem_key_s e l ==> mem_key_s e a /\ mem_key_s e b) /\
                        (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                pre_cond_merge #st #o #r (get_val_s #st #o #r ch l) (get_val_s #st #o #r ch a) (get_val_s #st #o #r ch b))})
let pre_cond_merge_a #st #o #r l a b =
  forallb (fun e -> mem_key_s (get_key_s #st e) a && mem_key_s (get_key_s #st e) b) l &&
  forallb (fun ch -> pre_cond_merge #st #o #r (get_val_s #st #o #r ch l) 
             (get_val_s #st #o #r ch a) (get_val_s #st #o #r ch b)) (get_key_lst l a b)

val remove_key : #st:eqtype 
               -> ch:nat
               -> a:s st
               -> Pure (s st)
                 (requires (mem_key_s ch a))
                 (ensures (fun r -> (forall i. mem_key_s i r <==> mem_key_s i a /\ ch <> i) /\
                                 (forall e. mem e r <==> mem e a /\ get_key_s e <> ch)))
let rec remove_key #st ch a =
  match a with
  |(ch1,v)::xs -> if ch = ch1 then xs else (ch1,v)::remove_key ch xs

val merge2 : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
           -> l:s st
           -> a:s st
           -> b:s st
           -> lst:list nat
           -> Pure (s st)
                (requires pre_cond_merge_a #st #o #r l a b /\ unique_keys lst /\
                          (forall ch. mem ch lst ==> mem_key_s ch a \/ mem_key_s ch b))
                (ensures (fun res -> (forall ch. mem_key_s ch res <==> mem ch lst) /\ unique_key res /\
                         (forall ch. mem ch lst ==> (get_val_s #st #o #r ch res) =
                         (merge #st #o #r (get_val_s #st #o #r ch l) (get_val_s #st #o #r ch a) (get_val_s #st #o #r ch b)))))
                (decreases lst)

#set-options "--z3rlimit 1000" 
let rec merge2 #st #o #r l a b lst =
  match lst with
  |[] -> []
  |x::xs -> (x, merge #st #o #r (get_val_s #st #o #r x l) (get_val_s #st #o #r x a) (get_val_s #st #o #r x b))::merge2 #st #o #r l a b xs

val merge_a : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
             -> l:s st
             -> a:s st
             -> b:s st
             -> Pure (s st)
               (requires pre_cond_merge_a #st #o #r l a b)
               (ensures (fun res -> (forall ch. mem_key_s ch res <==> mem_key_s ch a \/ mem_key_s ch b) /\ unique_key res /\
                               (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> (get_val_s #st #o #r ch res) =
                      (merge #st #o #r (get_val_s #st #o #r ch l) (get_val_s #st #o #r ch a) (get_val_s #st #o #r ch b)))))

let merge_a #st #o #r l a b = 
 let lst = get_key_lst l a b in
 merge2 #st #o #r l a b lst

val lem_merge1 : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
               -> ltr:ae (op o)
               -> l:s st
               -> atr:ae (op o)
               -> a:s st
               -> btr:ae (op o)
               -> b:s st
               -> lst:list nat
               -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
               (sim_a #st #o #r ltr l /\ sim_a #st #o #r (union ltr atr) a /\ sim_a #st #o #r (union ltr btr) b) /\
                                 (forall ch. mem ch lst <==> mem_key_s ch a \/ mem_key_s ch b) /\ unique_keys lst)
                       (ensures (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b))

#set-options "--z3rlimit 1000"
let lem_merge1 ltr l atr a btr b lst = ()

val pre_cond_prop_merge_a : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
            -> ltr:ae (op o) -> l:s st -> atr:ae (op o) -> a:s st -> btr:ae (op o) -> b:s st
            -> Tot bool
let pre_cond_prop_merge_a ltr l atr a btr b = true

val lemma6 : #o:eqtype 
           -> l:ae (op o)
           -> a:ae (op o)
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                   (ensures (forall e. mem_op e (union l a).l <==> mem_op e l.l \/ mem_op e a.l))
                   (decreases %[l.l;a.l])

#set-options "--z3rlimit 1000"
let rec lemma6 #o l a = 
  match l,a with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma6 (A l.vis xs) a
  |(A _ []), (A _ (x::xs)) -> lemma6 l (A a.vis xs)

val lemma61 : #o:eqtype 
            -> l:ae (op o)
            -> a:ae (op o)
            -> b:ae (op o)
                 -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)) /\
                                   (forall e. mem e a.l ==> not (mem_id (get_id e) b.l)) /\
                                   (forall e. mem e l.l ==> not (mem_id (get_id e) b.l)))
                         (ensures (forall e. mem_op e (abs_merge l a b).l <==> 
                                        mem_op e l.l \/ mem_op e a.l \/ mem_op e b.l))
                         (decreases %[l.l;a.l;b.l])

#set-options "--z3rlimit 10000000"
let rec lemma61 #o l a b = 
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma61 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma61 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma61 l a (A b.vis xs)

val lemma8 : #o:eqtype 
           -> ltr:ae (op o)
           -> atr:ae (op o)
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i atr).l)))
                   (ensures (forall i e. mem e (union (project i ltr) (project i atr)).l <==>
                                    mem e (project i (union ltr atr)).l) /\
                            (forall i. (forall e e1. (mem e (union (project i ltr) (project i atr)).l /\ 
             mem e1 (union (project i ltr) (project i atr)).l /\ get_id e <> get_id e1 /\ 
                    (union (project i ltr) (project i atr)).vis e e1) <==>
            (mem e (project i (union ltr atr)).l /\ mem e1 (project i (union ltr atr)).l /\ get_id e <> get_id e1 /\
                   (project i (union ltr atr)).vis e e1))))

#set-options "--z3rlimit 10000000"
let lemma8 #o ltr atr = ()

val lemma9 : #o:eqtype
           -> ltr:ae (op o)
           -> atr:ae (op o)
           -> btr:ae (op o)
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l))/\
                             (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i atr).l)) /\
                             (forall i e. mem e (project i atr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                             (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i btr).l)))
                   (ensures (forall i. (forall e. mem e (abs_merge (project i ltr) (project i atr) (project i btr)).l <==>
                             mem e (project i (abs_merge ltr atr btr)).l)) /\
             (forall i. (forall e e1. mem e (abs_merge (project i ltr) (project i atr) (project i btr)).l /\
                  mem e1 (abs_merge (project i ltr) (project i atr) (project i btr)).l /\ get_id e <> get_id e1 /\
                              (abs_merge (project i ltr) (project i atr) (project i btr)).vis e e1 <==>
                                mem e (project i (abs_merge ltr atr btr)).l /\ mem e1 (project i (abs_merge ltr atr btr)).l /\ get_id e <> get_id e1 /\ (project i (abs_merge ltr atr btr)).vis e e1)))

#set-options "--z3rlimit 10000000"
let lemma9 #o ltr atr btr = ()

val prop_merge1 : #st:eqtype -> #o:eqtype -> #r:eqtype -> #m:(mrdt st o r) -> {|alpha_map st o r m|}
                -> ltr:ae (op o)
                -> l:s st
                -> atr:ae (op o)
                -> a:s st
                -> btr:ae (op o)
                -> b:s st
                -> chs:list nat
                -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                  (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                  (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                                  (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i atr).l)) /\
                                  (forall i e. mem e (project i atr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                                  (forall i e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                    (sim_a #st #o #r ltr l /\ sim_a #st #o #r (union ltr atr) a /\ sim_a #st #o #r (union ltr btr) b) /\
                                  (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b) /\
                                  (forall i. mem i chs ==> mem_key_s i a \/ mem_key_s i b) /\
                                  pre_cond_merge_a #st #o #r l a b /\
                                  (forall i. mem_key_s i a \/ mem_key_s i b ==> 
                                  pre_cond_prop_merge #st #o #r (project i ltr) (get_val_s #st #o #r i l)
                                                           (project i atr) (get_val_s #st #o #r i a)
                                                           (project i btr) (get_val_s #st #o #r i b) /\
                                  (forall e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i atr).l)) /\
                                  (forall e. mem e (project i atr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                                  (forall e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                                  (sim #st #o #r (project i ltr) (get_val_s #st #o #r i l) /\ sim #st #o #r (union (project i ltr) (project i atr)) (get_val_s #st #o #r i a) /\ sim #st #o #r (union (project i ltr) (project i btr)) (get_val_s #st #o #r i b))) /\
                                  (forall i. mem i chs ==> mem_key_s i (merge_a #st #o #r l a b)))
                        (ensures (forall i. mem i chs ==> 
             ((sim #st #o #r) (project i (abs_merge ltr atr btr)) (get_val_s #st #o #r i (merge_a #st #o #r l a b)))))
                        (decreases chs)

#set-options "--z3rlimit 10000"
let rec prop_merge1 #st #o #r #m ltr l atr a btr b lst =
  match lst with
  |[] -> ()
  |i::is -> lemma4 #st #o #r #m ltr l; lemma4 #st #o #r #m (union ltr atr) a; lemma4 #st #o #r #m (union ltr btr) b;
          lemma8 #o ltr atr; lemma8 #o ltr btr; 
          lemma7 #st #o #r #m (project i (union ltr atr)) (get_val_s #st #o #r i a) (union (project i ltr) (project i atr));
          lemma7 #st #o #r #m (project i (union ltr btr)) (get_val_s #st #o #r i b) (union (project i ltr) (project i btr));
          (prop_merge #st #o #r) (project i ltr) (get_val_s #st #o #r i l) (project i atr) (get_val_s #st #o #r i a) (project i btr) (get_val_s #st #o #r i b);
          assert (sim #st #o #r (abs_merge (project i ltr) (project i atr) (project i btr)) (merge #st #o #r (get_val_s #st #o #r i l) (get_val_s #st #o #r i a) (get_val_s #st #o #r i b)));
          lemma9 #o ltr atr btr;
          assert ((sim #st #o #r) (abs_merge (project i ltr) (project i atr) (project i btr)) (get_val_s #st #o #r i (merge_a #st #o #r l a b))); 
          lemma7 #st #o #r #m (abs_merge (project i ltr) (project i atr) (project i btr)) 
                   (get_val_s #st #o #r i (merge_a #st #o #r l a b)) (project i (abs_merge ltr atr btr)); 
          assert ((sim #st #o #r) (project i (abs_merge ltr atr btr)) (get_val_s #st #o #r i (merge_a #st #o #r l a b)));
          prop_merge1 #st #o #r #m ltr l atr a btr b is

val prop_merge21 : #st:eqtype -> #o:eqtype -> #r:eqtype -> #m:(mrdt st o r) -> {|alpha_map st o r m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a #st #o #r ltr l /\ sim_a #st #o #r (union ltr atr) a /\ sim_a #st #o #r (union ltr btr) b) /\
                             pre_cond_merge_a #st #o #r l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_prop_merge #st #o #r (project ch ltr) (get_val_s #st #o #r ch l)
                                                      (project ch atr) (get_val_s #st #o #r ch a)
                                                      (project ch btr) (get_val_s #st #o #r ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o #r (project ch ltr) (get_val_s #st #o #r ch l) /\ sim #st #o #r (union (project ch ltr) (project ch atr)) (get_val_s #st #o #r ch a) /\ sim #st #o #r (union (project ch ltr) (project ch btr)) (get_val_s #st #o #r ch b))))
                  (ensures (forall e1. mem e1 (merge_a #st #o #r l a b) ==> (exists e. mem e (abs_merge ltr atr btr).l /\ get_key e = get_key_s e1 /\ opset e)))

#set-options "--z3rlimit 10000"
let prop_merge21 #st #o #r #m ltr l atr a btr b = 
  lemma2 #st #o #r #m (merge_a #st #o #r l a b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge22 : #st:eqtype -> #o:eqtype -> #r:eqtype -> #m:(mrdt st o r) -> {|alpha_map st o r m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a #st #o #r ltr l /\ sim_a #st #o #r (union ltr atr) a /\ sim_a #st #o #r (union ltr btr) b) /\
                             pre_cond_merge_a #st #o #r l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_prop_merge #st #o #r (project ch ltr) (get_val_s #st #o #r ch l)
                                                      (project ch atr) (get_val_s #st #o #r ch a)
                                                      (project ch btr) (get_val_s #st #o #r ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o #r (project ch ltr) (get_val_s #st #o #r ch l) /\ sim #st #o #r (union (project ch ltr) (project ch atr)) (get_val_s #st #o #r ch a) /\ sim #st #o #r (union (project ch ltr) (project ch btr)) (get_val_s #st #o #r ch b))))
                  (ensures (forall e. mem e (abs_merge ltr atr btr).l /\ opset e ==> (exists e1. mem e1 (merge_a #st #o #r l a b) /\ get_key e = get_key_s e1)))

#set-options "--z3rlimit 10000"
let prop_merge22 #st #o #r #m ltr l atr a btr b =
  lemma2 #st #o #r #m (merge_a #st #o #r l a b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge_a : #st:eqtype -> #o:eqtype -> #r:eqtype -> #m:(mrdt st o r) -> {|alpha_map st o r m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a #st #o #r ltr l /\ sim_a #st #o #r (union ltr atr) a /\ sim_a #st #o #r (union ltr btr) b) /\
                             pre_cond_merge_a #st #o #r l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_prop_merge #st #o #r (project ch ltr) (get_val_s #st #o #r ch l)
                                                      (project ch atr) (get_val_s #st #o #r ch a)
                                                      (project ch btr) (get_val_s #st #o #r ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o #r (project ch ltr) (get_val_s #st #o #r ch l) /\ sim #st #o #r (union (project ch ltr) (project ch atr)) (get_val_s #st #o #r ch a) /\ sim #st #o #r (union (project ch ltr) (project ch btr)) (get_val_s #st #o #r ch b))))
                 (ensures (sim_a #st #o #r (abs_merge ltr atr btr) (merge_a #st #o #r l a b)))

#set-options "--z3rlimit 10000"
let prop_merge_a #st #o #r #m ltr l atr a btr b = 
  prop_merge21 #st #o #r #m ltr l atr a btr b;
  prop_merge22 #st #o #r #m ltr l atr a btr b;
  let m1 = get_lst (merge_a #st #o #r l a b) in
  prop_merge1 #st #o #r #m ltr l atr a btr b m1

val prop_spec : #st:eqtype -> #o:eqtype -> #r:eqtype -> {|mrdt st o r|}
              -> tr:ae (op o)
              -> st1:(s st)
              -> op:(nat * (op o))
              -> Lemma (requires (sim_a #st #o #r tr st1) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures true (*get_rval (do st op)) = spec_a op tr*))
let prop_spec tr st op = ()

