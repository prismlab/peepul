module Alpha_map
open FStar.List.Tot

open Library

type op (alpha_op:eqtype) = (nat (*key*) * alpha_op)

val get_key : #o:eqtype -> op1:(nat * op o) -> Tot (k:nat {exists id op2. op1 = (id, (k, op2))})
let get_key (id, (k, _)) = k

val get_val : #o:eqtype -> op1:(nat * op o) -> Tot (s:o {exists id k. op1 = (id, (k, s))})
let get_val (id, (k, s)) = s

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

val get_val_s : #st:eqtype -> #o:eqtype -> {| mrdt st o |}
                -> i:nat -> s1:s st -> Tot (c:st {(mem_key_s i s1 ==> mem (i,c) s1 /\ 
                                         (exists e. mem e s1 /\ e = (i,c) /\ c = get_val_s1 #st e)) /\ 
                                         (not (mem_key_s i s1) ==> c = init #st #o)})
let rec get_val_s #st #o i s1 =
  match s1 with
  |[] -> init #st #o
  |x::xs -> if get_key_s x = i then get_val_s1 x else get_val_s #st #o i xs

val mem_op : #o:eqtype -> ele1:op o
           -> l:list (nat * (op o))
           -> Tot (b:bool {b=true <==> (exists id. mem (id, ele1) l) })
let rec mem_op ele2 l =
  match l with
  |[] -> false
  |(_, ele1)::xs -> ele1 = ele2 || mem_op ele2 xs

val mem_key : #o:eqtype -> i:nat -> l:list (nat * op o) -> Tot (b:bool {b=true <==> (exists id op. mem (id, (i, op)) l)})
let rec mem_key ele2 l =
  match l with
  |[] -> false
  |(_, (ele1, _))::xs -> ele1 = ele2 || mem_key ele2 xs

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

val project_op : #o:eqtype 
               -> o1:(nat * (op o))
               -> Tot (o2:(nat * o) {o2 = (get_id o1, get_val o1)})
let project_op op =
  match op with
  |(id, (k, value)) -> (id, value)

val project1 : #o:eqtype
             -> i:nat
             -> l:ae (op o)
             -> Pure (list (nat * o))
                    (requires true)
                    (ensures (fun r -> (forall id. mem_id id r <==> (mem_id id l.l /\ get_key (get_eve id l.l) = i)) /\ 
                                         unique_id r /\ (forall e. mem e l.l /\ get_key e = i ==> mem (project_op e) r)))
               (decreases List.Tot.length l.l)

#set-options "--z3rlimit 10000000"
let rec project1 i l =
  match l.l with
  |[] -> []
  |x::xs -> if (get_key x = i) then (project_op x)::project1 i (A l.vis xs) else (project1 i (A l.vis xs))

val project : #o:eqtype
            -> i:nat
            -> l:ae (op o)
            -> Pure (ae o)
                   (requires true)
                   (ensures (fun r -> (forall id. mem_id id r.l <==> (mem_id id l.l /\ get_key (get_eve id l.l) = i)) /\ 
                                     unique_id r.l /\ (forall e. mem e l.l /\ get_key e = i ==> mem (project_op e) r.l) /\
                   (forall e e1. (get_id e <> get_id e1 /\ mem (get_id e, (i, get_op e)) l.l /\ 
             mem (get_id e1, (i, get_op e1)) l.l /\ l.vis (get_id e, (i, get_op e)) (get_id e1, (i, get_op e1))) <==> 
                   (get_id e <> get_id e1 /\ mem e r.l /\ mem e1 r.l /\ r.vis e e1)) /\ not (mem_key i l.l) <==> r.l = []))
               (decreases length l.l)

#set-options "--z3rlimit 10000000"
let project i l =
    (A (fun o o1 -> (mem (get_id o, (i, get_op o)) l.l && mem (get_id o1, (i, get_op o1)) l.l &&  get_id o <> get_id o1 && l.vis (get_id o, (i, get_op o)) (get_id o1, (i, get_op o1)))) (project1 i l))

val pre_cond_op_a : #st1:eqtype -> #o:eqtype -> {|mrdt st1 o|}
                  -> s1:s st1 -> op1:(nat * op o)
                  -> Tot (b:bool {b = true <==> pre_cond_op #st1 #o (get_val_s #st1 #o (get_key op1) s1) (project_op op1)})
let pre_cond_op_a #st1 #o s1 op = 
    pre_cond_op #st1 #o (get_val_s #st1 #o (get_key op) s1) (project_op op)

val app_op_a : #st1:eqtype -> #o:eqtype -> {|mrdt st1 o|}
             -> st:s st1 -> op1:(nat * op o)
             -> Pure (s st1)
               (requires pre_cond_op_a #st1 #o st op1)
               (ensures (fun r -> (forall ch. mem_key_s ch r <==> mem_key_s ch st \/ ch = get_key op1) /\ unique_key r /\
                               (forall ch. ch <> get_key op1 ==> (get_val_s #st1 #o ch st = get_val_s #st1 #o ch r)) /\
                             (get_val_s #st1 #o (get_key op1) r = 
                                  (app_op #st1 #o (get_val_s #st1 #o (get_key op1) st) (project_op op1)))))

#set-options "--z3rlimit 10000000"
let rec app_op_a #st1 #o st op1 =
  match st with
  |[] -> [(get_key op1, (app_op (init #st1 #o) (project_op op1)))]
  |(ch, x)::xs -> if ch = get_key op1 then (ch, (app_op x (project_op op1)))::xs
                     else (ch, x)::app_op_a xs op1

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

#set-options "--query_stats"
val sim_a : #st:eqtype -> #o:eqtype -> {|mrdt st o|}
          -> tr:ae (op o)
          -> s1:s st
          -> Tot (b:bool {(b = true) <==> (forall ch. mem_key_s ch s1 <==> mem_key ch tr.l) /\
                          (forall ch. mem_key_s ch s1 ==> (sim #st #o) (project ch tr) (get_val_s #st #o ch s1)) /\
                                     (forall e. mem e tr.l ==> (exists e1. mem e1 s1 /\ get_key e = get_key_s e1))})

#set-options "--z3rlimit 10000000"
let sim_a #st #o tr s1 =
  forallb (fun e -> mem_key (get_key_s e) tr.l) s1 &&
  forallb (fun e -> mem_key_s (get_key e) s1) tr.l &&
  forallb (fun e -> (sim #st #o) (project (get_key_s e) tr) (get_val_s #st #o (get_key_s e) s1)) s1 &&
  forallb (fun e -> (existsb (fun e1 -> get_key e = get_key_s e1) s1)) tr.l

class alpha_map (st:eqtype) (o:eqtype) (m:mrdt st o) = {

  lemma4 : tr:ae (op o) -> s1:s st
         -> Lemma (requires sim_a tr s1)
                 (ensures (forall i. (sim #st #o) (project i tr) (get_val_s #st #o i s1)));

  lemma1 : tr:ae (op o)
         -> s1:s st
         -> op1:(nat * (op o))
         -> Lemma (requires (sim_a tr s1) /\ (not (mem_id (get_id op1) tr.l)) /\
                           (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                           pre_cond_op #st #o (get_val_s #st #o (get_key op1) s1) (project_op op1))
                 (ensures (forall i. mem_key_s i (app_op_a s1 op1) /\ i <> get_key op1 ==>
                   ((forall e. mem e (project i (append tr op1)).l <==> mem e (project i tr).l) /\
                   (forall e e1. mem e (project i (append tr op1)).l /\ mem e1 (project i (append tr op1)).l /\ 
                        get_id e <> get_id e1 /\ (project i (append tr op1)).vis e e1 <==> 
                 mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1) /\
                   (get_val_s #st #o i (app_op_a s1 op1) = (get_val_s #st #o i s1))) ==>
                     (sim #st #o) (project i (append tr op1)) (get_val_s #st #o i (app_op_a s1 op1))));

  lemma7 : tr:ae o -> s1:st -> tr1:ae o
         -> Lemma (requires sim tr s1 /\ (forall e. mem e tr1.l <==> mem e tr.l) /\
                           (forall e e1. mem e tr1.l /\ mem e1 tr1.l /\ get_id e <> get_id e1 /\ tr1.vis e e1 <==>
                                    mem e tr.l /\ mem e1 tr.l /\ get_id e <> get_id e1 /\ tr.vis e e1))
                 (ensures (sim tr1 s1));

  lemma2 : s1:s st
         -> Lemma (requires true)
                 (ensures (forall e. mem e s1 ==> (get_val_s #st #o (get_key_s e) s1 = get_val_s1 #st e)))
}

val convergence_a1 : #st:eqtype -> #o:eqtype -> {| mrdt st o |} 
                   -> tr:ae (op o)
                   -> a:s st
                   -> b:s st
                   -> Lemma (requires (sim_a tr a /\ sim_a tr b))
                         (ensures (forall e. mem_key_s e a <==> mem_key_s e b))
let convergence_a1 tr a b = ()

val lem_oper1 : #o:eqtype
              -> tr:ae (op o)
              -> op:(nat * (op o))
              -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (forall e. mem e (project (get_key op) (append tr op)).l <==> 
                                     mem e (append (project (get_key op) tr) (project_op op)).l))
#set-options "--z3rlimit 10000000"
let lem_oper1 tr op = ()

val lem_oper2 : #o:eqtype
              -> tr:ae (op o)
              -> op:(nat * (op o))
              -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (forall e e1. mem e (project (get_key op) (append tr op)).l /\
                        mem e1 (project (get_key op) (append tr op)).l /\ (get_id e <> get_id e1) /\
                        (project (get_key op) (append tr op)).vis e e1  <==> 
                        mem e (append (project (get_key op) tr) (project_op op)).l /\
                    mem e1 (append (project (get_key op) tr) (project_op op)).l /\ get_id e <> get_id e1 /\
                        (append (project (get_key op) tr) (project_op op)).vis e e1))
#set-options "--z3rlimit 10000000"
let lem_oper2 tr op = lem_oper1 tr op

val lem_oper3 : #o:eqtype
              -> tr:ae (op o)
              -> op:(nat * (op o))
              -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (forall i. i <> (get_key op) ==> (forall e. mem e (project i (append tr op)).l <==> mem e (project i tr).l) /\
         (forall e e1. mem e (project i (append tr op)).l /\ mem e1 (project i (append tr op)).l /\ get_id e <> get_id e1 /\
                    (project i (append tr op)).vis e e1 <==> 
        mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1)))
#set-options "--z3rlimit 10000000"
let lem_oper3 tr op = 
  lem_oper1 tr op;
  lem_oper2 tr op

val lem_oper : #o:eqtype
             -> tr:ae (op o)
             -> op:(nat * (op o))
             -> Lemma (requires (not (mem_id (get_id op) tr.l)) /\
                               (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                     (ensures (forall e. mem e (project (get_key op) (append tr op)).l <==> 
                                    mem e (append (project (get_key op) tr) (project_op op)).l) /\
               (forall e e1. mem e (project (get_key op) (append tr op)).l /\
                        mem e1 (project (get_key op) (append tr op)).l /\ (get_id e <> get_id e1) /\
                        (project (get_key op) (append tr op)).vis e e1  <==> 
                        mem e (append (project (get_key op) tr) (project_op op)).l /\
                    mem e1 (append (project (get_key op) tr) (project_op op)).l /\ get_id e <> get_id e1 /\
                        (append (project (get_key op) tr) (project_op op)).vis e e1) /\
         (forall i. i <> (get_key op) ==> (forall e. mem e (project i (append tr op)).l <==> mem e (project i tr).l) /\
         (forall e e1. mem e (project i (append tr op)).l /\ mem e1 (project i (append tr op)).l /\ get_id e <> get_id e1 /\
                    (project i (append tr op)).vis e e1 <==> 
        mem e (project i tr).l /\ mem e1 (project i tr).l /\ get_id e <> get_id e1 /\ (project i tr).vis e e1)))

#set-options "--z3rlimit 10000000"
let lem_oper tr op = 
  lem_oper1 tr op;
  lem_oper2 tr op;
  lem_oper3 tr op

val prop_oper1 : #st1:eqtype -> #o:eqtype -> {|mrdt st1 o|} 
               -> tr:ae (op o)
               -> st:s st1
               -> op1:(nat * (op o)) 
               -> Lemma (requires (sim_a tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                 (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                 pre_cond_op #st1 #o (get_val_s #st1 #o (get_key op1) st) (project_op op1))
                       (ensures (forall ch. mem_key_s ch (app_op_a st op1) <==> mem_key ch (append tr op1).l))
#set-options "--z3rlimit 10000000"
let prop_oper1 tr st op = lem_oper tr op

val prop_oper2 : #st1:eqtype -> #o:eqtype -> {|mrdt st1 o|} 
               -> tr:ae (op o)
               -> st:s st1
               -> op1:(nat * (op o)) 
               -> Lemma (requires (sim_a tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                 (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                 pre_cond_op #st1 #o (get_val_s #st1 #o (get_key op1) st) (project_op op1))
                       (ensures (forall e. mem e (append tr op1).l ==> (exists e1. mem e1 (app_op_a st op1) /\ get_key e = get_key_s e1)))

#set-options "--z3rlimit 10000000"
let prop_oper2 tr st op = 
  lem_oper tr op;
  prop_oper1 tr st op

val prop_oper3 : #st1:eqtype -> #o:eqtype -> #m:(mrdt st1 o) -> {|alpha_map st1 o m|}
               -> tr:ae (op o)
               -> st:s st1
               -> op1:(nat * (op o)) 
               -> Lemma (requires (sim_a tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                 (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                 pre_cond_op #st1 #o (get_val_s #st1 #o (get_key op1) st) (project_op op1))
                       (ensures (forall ch. mem_key_s ch (app_op_a st op1) /\ ch <> get_key op1 ==>
                         (sim #st1 #o) (project ch (append tr op1)) (get_val_s #st1 #o ch (app_op_a st op1))))

#set-options "--z3rlimit 10000000"
let prop_oper3 #st1 #o #m tr st op = 
  lem_oper tr op;
  prop_oper1 tr st op;
  prop_oper2 tr st op;
  lemma1 #st1 #o #m tr st op

val prop_oper_a : #st1:eqtype -> #o:eqtype -> #m:(mrdt st1 o) -> {|alpha_map st1 o m|}
                -> tr:ae (op o)
                -> st:s st1
                -> op1:(nat * (op o)) 
                -> Lemma (requires (sim_a tr st) /\ (not (mem_id (get_id op1) tr.l)) /\
                                  (forall e. mem e tr.l ==> get_id e < get_id op1) /\ get_id op1 > 0 /\
                                  pre_cond_op #st1 #o (get_val_s #st1 #o (get_key op1) st) (project_op op1) /\
     ((sim #st1 #o) (project (get_key op1) (append tr op1)) (get_val_s #st1 #o (get_key op1) (app_op_a st op1))))
                      (ensures (sim_a (append tr op1) (app_op_a st op1)))

#set-options "--z3rlimit 10000000"
let prop_oper_a #st1 #o #m tr st op = 
  lem_oper tr op;
  prop_oper1 tr st op;
  prop_oper2 tr st op;
  prop_oper3 #st1 #o #m tr st op

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

val pre_cond_merge1_a : #st:eqtype -> #o:eqtype -> {|mrdt st o|}
                      -> l:s st -> a:s st -> b:s st 
                      -> Tot (b1:bool {b1=true <==> (forall e. mem_key_s e l ==> mem_key_s e a /\ mem_key_s e b) /\
                        (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                pre_cond_merge1 #st #o (get_val_s #st #o ch l) (get_val_s #st #o ch a) (get_val_s #st #o ch b))})
let pre_cond_merge1_a #st #o l a b =
  forallb (fun e -> mem_key_s (get_key_s #st e) a && mem_key_s (get_key_s #st e) b) l &&
  forallb (fun ch -> pre_cond_merge1 #st #o (get_val_s #st #o ch l) 
             (get_val_s #st #o ch a) (get_val_s #st #o ch b)) (get_key_lst l a b)

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

val merge2 : #st:eqtype -> #o:eqtype -> {|mrdt st o|}
           -> l:s st
           -> a:s st
           -> b:s st
           -> lst:list nat
           -> Pure (s st)
                (requires pre_cond_merge1_a #st #o l a b /\ unique_keys lst /\
                          (forall ch. mem ch lst ==> mem_key_s ch a \/ mem_key_s ch b))
                (ensures (fun r -> (forall ch. mem_key_s ch r <==> mem ch lst) /\ unique_key r /\
                         (forall ch. mem ch lst ==> (get_val_s #st #o ch r) =
                         (merge1 #st #o (get_val_s #st #o ch l) (get_val_s #st #o ch a) (get_val_s #st #o ch b)))))
                (decreases lst)

#set-options "--z3rlimit 10000000" 
let rec merge2 #st #o l a b lst =
  match lst with
  |[] -> []
  |x::xs -> (x, merge1 #st #o (get_val_s #st #o x l) (get_val_s #st #o x a) (get_val_s #st #o x b))::merge2 #st #o l a b xs

val merge1_a : #st:eqtype -> #o:eqtype -> {|mrdt st o|}
             -> l:s st
             -> a:s st
             -> b:s st
             -> Pure (s st)
               (requires pre_cond_merge1_a #st #o l a b)
               (ensures (fun r -> (forall ch. mem_key_s ch r <==> mem_key_s ch a \/ mem_key_s ch b) /\ unique_key r /\
                               (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> (get_val_s #st #o ch r) =
                      (merge1 #st #o (get_val_s #st #o ch l) (get_val_s #st #o ch a) (get_val_s #st #o ch b)))))

#set-options "--z3rlimit 10000000" 
let merge1_a #st #o l a b = 
 let lst = get_key_lst l a b in
 merge2 #st #o l a b lst

val lem_merge1 : #st:eqtype -> #o:eqtype -> {|mrdt st o|}
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
                                 (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\
                                 (forall ch. mem ch lst <==> mem_key_s ch a \/ mem_key_s ch b) /\ unique_keys lst)
                       (ensures (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b))

#set-options "--z3rlimit 10000000"
let lem_merge1 ltr l atr a btr b lst = ()

val pre_cond_merge_a : #st:eqtype -> #o:eqtype -> {|mrdt st o|}
            -> ltr:ae (op o) -> l:s st -> atr:ae (op o) -> a:s st -> btr:ae (op o) -> b:s st
            -> Tot bool
let pre_cond_merge_a ltr l atr a btr b = true

val merge_a : #st:eqtype -> #o:eqtype -> {|mrdt st o|}
            -> ltr:ae (op o)
            -> l:s st
            -> atr:ae (op o)
            -> a:s st
            -> btr:ae (op o)
            -> b:s st
            -> Pure (s st) 
              (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                        (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                        (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                        (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\ pre_cond_merge1_a #st #o l a b /\
                        (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                        (pre_cond_merge #st #o (project ch ltr) (get_val_s #st #o ch l)
                                               (project ch atr) (get_val_s #st #o ch a)
                                               (project ch btr) (get_val_s #st #o ch b)) /\
                        (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                        (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                        (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                        (sim #st #o (project ch ltr) (get_val_s #st #o ch l) /\ sim #st #o (union (project ch ltr) (project ch atr)) (get_val_s #st #o ch a) /\ sim #st #o (union (project ch ltr) (project ch btr)) (get_val_s #st #o ch b))))

              (ensures (fun r -> (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b) /\
                              (forall i. mem_key_s i r <==> mem_key_s i a \/ mem_key_s i b) /\
                              (forall ch. mem_key_s ch r ==> (get_val_s #st #o ch r) =
                    (merge1 #st #o (get_val_s #st #o ch l) (get_val_s #st #o ch a) (get_val_s #st #o ch b))) /\
                         (forall ch. mem_key_s ch r ==> (get_val_s #st #o ch r) =
                  (merge #st #o (project ch ltr) (get_val_s #st #o ch l) (project ch atr) (get_val_s #st #o ch a) (project ch btr) (get_val_s #st #o ch b))) /\ (r = merge1_a #st #o l a b)))

let merge_a #st #o ltr l atr a btr b = 
  let keys = get_key_lst l a b in
  lem_merge1 ltr l atr a btr b keys;
  let r = merge1_a #st #o l a b in
  r

val lemma6 : #o:eqtype 
           -> l:ae (op o)
           -> a:ae (op o)
           -> Lemma (requires (forall e. mem e l.l ==> not (mem_id (get_id e) a.l)))
                   (ensures (forall e. mem_op e (union1 l a) <==> mem_op e l.l \/ mem_op e a.l))
                   (decreases %[l.l;a.l])

#set-options "--z3rlimit 10000000"
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
                         (ensures (forall e. mem_op e (absmerge1 l a b) <==> 
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
                   (ensures (forall i. (forall e. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l <==>
                             mem e (project i (absmerge ltr atr btr)).l)) /\
             (forall i. (forall e e1. mem e (absmerge (project i ltr) (project i atr) (project i btr)).l /\
                  mem e1 (absmerge (project i ltr) (project i atr) (project i btr)).l /\ get_id e <> get_id e1 /\
                              (absmerge (project i ltr) (project i atr) (project i btr)).vis e e1 <==>
                                mem e (project i (absmerge ltr atr btr)).l /\ mem e1 (project i (absmerge ltr atr btr)).l /\ get_id e <> get_id e1 /\ (project i (absmerge ltr atr btr)).vis e e1)))

#set-options "--z3rlimit 10000000"
let lemma9 #o ltr atr btr = ()

val prop_merge1 : #st:eqtype -> #o:eqtype -> #m:(mrdt st o) -> {|alpha_map st o m|}
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
                                  (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\
                                  (forall i. mem_key_s i l ==> mem_key_s i a /\ mem_key_s i b) /\
                                  (forall i. mem i chs ==> mem_key_s i a \/ mem_key_s i b) /\
                                  pre_cond_merge1_a #st #o l a b /\
                                  (forall i. mem_key_s i a \/ mem_key_s i b ==> 
                                  pre_cond_merge #st #o (project i ltr) (get_val_s #st #o i l)
                                                           (project i atr) (get_val_s #st #o i a)
                                                           (project i btr) (get_val_s #st #o i b) /\
                                  (forall e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i atr).l)) /\
                                  (forall e. mem e (project i atr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                                  (forall e. mem e (project i ltr).l ==> not (mem_id (get_id e) (project i btr).l)) /\
                                  (sim #st #o (project i ltr) (get_val_s #st #o i l) /\ sim #st #o (union (project i ltr) (project i atr)) (get_val_s #st #o i a) /\ sim #st #o (union (project i ltr) (project i btr)) (get_val_s #st #o i b))) /\
                                  (forall i. mem i chs ==> mem_key_s i (merge_a ltr l atr a btr b)))
                        (ensures (forall i. mem i chs ==> 
             ((sim #st #o) (project i (absmerge ltr atr btr)) (get_val_s #st #o i (merge_a ltr l atr a btr b)))))
                        (decreases chs)

#set-options "--z3rlimit 10000000"
let rec prop_merge1 #st #o #m ltr l atr a btr b lst =
  match lst with
  |[] -> ()
  |i::is -> lemma4 #st #o #m ltr l; lemma4 #st #o #m (union ltr atr) a; lemma4 #st #o #m (union ltr btr) b;
          lemma8 #o ltr atr; lemma8 #o ltr btr; 
          lemma7 #st #o #m (project i (union ltr atr)) (get_val_s #st #o i a) (union (project i ltr) (project i atr));
          lemma7 #st #o #m (project i (union ltr btr)) (get_val_s #st #o i b) (union (project i ltr) (project i btr));
          (prop_merge #st #o) (project i ltr) (get_val_s #st #o i l) (project i atr) (get_val_s #st #o i a) (project i btr) (get_val_s #st #o i b);
          assert (sim #st #o (absmerge (project i ltr) (project i atr) (project i btr)) (merge #st #o (project i ltr) (get_val_s #st #o i l) (project i atr) (get_val_s #st #o i a) (project i btr) (get_val_s #st #o i b)));
          lemma9 #o ltr atr btr;
          assert ((sim #st #o) (absmerge (project i ltr) (project i atr) (project i btr)) (get_val_s #st #o i (merge_a ltr l atr a btr b))); 
          lemma7 #st #o #m (absmerge (project i ltr) (project i atr) (project i btr)) 
                 (get_val_s #st #o i (merge_a ltr l atr a btr b)) (project i (absmerge ltr atr btr)); 
          assert ((sim #st #o) (project i (absmerge ltr atr btr)) (get_val_s #st #o i (merge_a ltr l atr a btr b)));
          prop_merge1 #st #o #m ltr l atr a btr b is

val prop_merge21 : #st:eqtype -> #o:eqtype -> #m:(mrdt st o) -> {|alpha_map st o m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\
                             pre_cond_merge1_a #st #o l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_merge #st #o (project ch ltr) (get_val_s #st #o ch l)
                                                   (project ch atr) (get_val_s #st #o ch a)
                                                   (project ch btr) (get_val_s #st #o ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o (project ch ltr) (get_val_s #st #o ch l) /\ sim #st #o (union (project ch ltr) (project ch atr)) (get_val_s #st #o ch a) /\ sim #st #o (union (project ch ltr) (project ch btr)) (get_val_s #st #o ch b))))
                  (ensures (forall e. mem e (merge_a ltr l atr a btr b) ==> mem_key (get_key_s e) (absmerge ltr atr btr).l))

#set-options "--z3rlimit 10000000"
let prop_merge21 #st #o #m ltr l atr a btr b = 
  lemma2 #st #o #m (merge_a ltr l atr a btr b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge22 : #st:eqtype -> #o:eqtype -> #m:(mrdt st o) -> {|alpha_map st o m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\
                             pre_cond_merge1_a #st #o l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_merge #st #o (project ch ltr) (get_val_s #st #o ch l)
                                                   (project ch atr) (get_val_s #st #o ch a)
                                                   (project ch btr) (get_val_s #st #o ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o (project ch ltr) (get_val_s #st #o ch l) /\ sim #st #o (union (project ch ltr) (project ch atr)) (get_val_s #st #o ch a) /\ sim #st #o (union (project ch ltr) (project ch btr)) (get_val_s #st #o ch b))))
                   (ensures (forall e. mem e (absmerge ltr atr btr).l ==> 
                                      mem_key_s (get_key e) (merge_a ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge22 #st #o #m ltr l atr a btr b = 
  lemma2 #st #o #m (merge_a ltr l atr a btr b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge2 : #st:eqtype -> #o:eqtype -> #m:(mrdt st o) -> {|alpha_map st o m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\
                             pre_cond_merge1_a #st #o l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_merge #st #o (project ch ltr) (get_val_s #st #o ch l)
                                                   (project ch atr) (get_val_s #st #o ch a)
                                                   (project ch btr) (get_val_s #st #o ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o (project ch ltr) (get_val_s #st #o ch l) /\ sim #st #o (union (project ch ltr) (project ch atr)) (get_val_s #st #o ch a) /\ sim #st #o (union (project ch ltr) (project ch btr)) (get_val_s #st #o ch b))))
                   (ensures (forall ch. mem_key_s ch (merge_a ltr l atr a btr b) <==> 
                                       mem_key ch (absmerge ltr atr btr).l))

#set-options "--z3rlimit 10000000"
let prop_merge2 #st #o #m ltr l atr a btr b = 
  prop_merge21 #st #o #m ltr l atr a btr b;
  prop_merge22 #st #o #m ltr l atr a btr b

val prop_merge31 : #st:eqtype -> #o:eqtype -> #m:(mrdt st o) -> {|alpha_map st o m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\
                             pre_cond_merge1_a #st #o l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_merge #st #o (project ch ltr) (get_val_s #st #o ch l)
                                                   (project ch atr) (get_val_s #st #o ch a)
                                                   (project ch btr) (get_val_s #st #o ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o (project ch ltr) (get_val_s #st #o ch l) /\ sim #st #o (union (project ch ltr) (project ch atr)) (get_val_s #st #o ch a) /\ sim #st #o (union (project ch ltr) (project ch btr)) (get_val_s #st #o ch b))) /\ (forall ch. mem_key_s ch (merge_a ltr l atr a btr b) <==> mem_key ch (absmerge ltr atr btr).l))
                    (ensures (forall e. mem e (absmerge ltr atr btr).l ==> 
                             (exists e1. mem e1 (merge_a ltr l atr a btr b) /\ get_key e = get_key_s e1)))

#set-options "--z3rlimit 10000000"
let prop_merge31 #st #o #m ltr l atr a btr b = 
  lemma2 #st #o #m (merge_a ltr l atr a btr b);
  lemma6 ltr atr; lemma6 ltr btr;
  lemma61 ltr atr btr

val prop_merge_a : #st:eqtype -> #o:eqtype -> #m:(mrdt st o) -> {|alpha_map st o m|}
          -> ltr:ae (op o)
          -> l:s st
          -> atr:ae (op o)
          -> a:s st
          -> btr:ae (op o)
          -> b:s st
          -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                            (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                            (sim_a ltr l /\ sim_a (union ltr atr) a /\ sim_a (union ltr btr) b) /\
                             pre_cond_merge1_a #st #o l a b /\
                            (forall ch. mem_key_s ch a \/ mem_key_s ch b ==> 
                            (pre_cond_merge #st #o (project ch ltr) (get_val_s #st #o ch l)
                                                   (project ch atr) (get_val_s #st #o ch a)
                                                   (project ch btr) (get_val_s #st #o ch b)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch atr).l)) /\
                            (forall e. mem e (project ch atr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (forall e. mem e (project ch ltr).l ==> not (mem_id (get_id e) (project ch btr).l)) /\
                            (sim #st #o (project ch ltr) (get_val_s #st #o ch l) /\ sim #st #o (union (project ch ltr) (project ch atr)) (get_val_s #st #o ch a) /\ sim #st #o (union (project ch ltr) (project ch btr)) (get_val_s #st #o ch b))))
                    (ensures (sim_a (absmerge ltr atr btr) (merge_a ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge_a #st #o #m ltr l atr a btr b = 
  prop_merge2 #st #o #m ltr l atr a btr b;
  prop_merge31 #st #o #m ltr l atr a btr b;
  let m1 = get_lst (merge_a ltr l atr a btr b) in
  prop_merge1 #st #o #m ltr l atr a btr b m1


