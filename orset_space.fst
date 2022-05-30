module Orset_space
open FStar.List.Tot

open Library

val member_id : id:nat 
              -> l:list (nat * nat)
              -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_id n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_id n xs

val unique_id : l:list (nat * nat)
              -> Tot bool
let rec unique_id l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_id id xs) && unique_id xs

val member_ele : ele:nat
               -> l:list (nat * nat)
               -> Tot (b:bool{(exists id. mem (id,ele) l) <==> b=true})
let rec member_ele ele l =
  match l with
  |[] -> false
  |(_,ele1)::xs -> (ele = ele1) || member_ele ele xs

val unique_ele : l:list (nat * nat)
               -> Tot bool
let rec unique_ele l =
  match l with
  |[] -> true
  |(_,ele)::xs -> not (member_ele ele xs) && unique_ele xs

type s = l:list (nat (*unique id*) * nat (*unique element*)) {unique_id l /\ unique_ele l}

val init : s
let init = []

val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat) 
               -> Lemma (requires (unique_id l /\ unique_ele l))
                       (ensures (unique_id (filter f l) /\ unique_ele (filter f l)))
                               [SMTPat (filter f l)]

#set-options "--z3rlimit 1000000"
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

type op =
  |Add : nat (*element*) -> op
  |Rem : nat (*element*) -> op

val get_ele : op1:(nat * op) -> Tot (ele:nat {(exists id. op1 = (id, Add ele) \/ op1 = (id, Rem ele))})
let get_ele op =
  match op with
  |(_, (Add ele)) -> ele
  |(_, (Rem ele)) -> ele

val opa : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id ele. op1 = (id, Add ele))})
let opa op1 =
  match op1 with
  |(_, Add _) -> true
  |_ -> false

val opr : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id ele. op1 = (id, Rem ele))})
let opr op1 = not (opa op1)

val update : s1:s
           -> ele:nat
           -> id:nat
           -> Pure s
               (requires (member_ele ele s1) /\ not (member_id id s1))
               (ensures (fun u -> (forall e. mem e s1 /\ snd e <> ele <==> mem e u /\ snd e <> ele) /\
                               (forall e. mem e u /\ fst e <> id /\ member_id (fst e) u <==> 
                                     mem e s1 /\ snd e <> ele /\ member_id (fst e) s1) /\
                                (forall e. member_ele e s1 <==> member_ele e u) /\
                                (forall e. mem e u /\ e <> (id,ele) <==> mem e s1 /\ snd e <> ele) /\ mem (id,ele) u))
                                (decreases s1)
let rec update s1 ele id =
  match s1 with
  |[] -> []
  |(id1,ele1)::xs -> if ele = ele1 then (id,ele1)::xs else (id1,ele1):: update xs ele id

val remove_ele : s1:s
                 -> ele:nat
                 -> Pure s
                 (requires (member_ele ele s1))
                 (ensures (fun u -> (forall e. mem e s1 /\ snd e <> ele <==> mem e u)))
                 (decreases s1)
let rec remove_ele s1 ele =
  match s1 with
  |[] -> []
  |(id1,ele1)::xs -> if ele = ele1 then xs else (id1,ele1):: remove_ele xs ele

let pre_cond_op s1 op = not (member_id (get_id op) s1)

val app_op : s1:s
           -> op:(nat * op)
           -> Pure s
             (requires pre_cond_op s1 op)
             (ensures (fun res -> (opa op ==> (forall e. mem e s1 /\ snd e <> get_ele op <==> mem e res /\ snd e <> get_ele op) /\
                                          (forall e. mem e res /\ fst e <> get_id op /\ member_id (fst e) res <==> mem e s1 /\ snd e <> get_ele op /\ member_id (fst e) s1) /\
                                          (forall e. member_ele e s1 \/ e = get_ele op <==> member_ele e res) /\
                                          (forall e. mem e res /\ e <> ((get_id op), (get_ele op)) <==> mem e s1 /\ snd e <> get_ele op) /\
                                            mem ((get_id op), (get_ele op)) res) /\
                               (opr op ==> (forall e. mem e res <==> mem e s1 /\ snd e <> get_ele op))))
let app_op s1 op =
  if (opa op) 
    then (if member_ele (get_ele op) s1 then (update s1 (get_ele op) (get_id op))
      else ((get_id op),(get_ele op))::s1) 
        else (if member_ele (get_ele op) s1 then (remove_ele s1 (get_ele op)) else s1)

val filter_uni1 : f:((nat * op) -> bool)
                -> l:list (nat * op) 
                -> Lemma (requires (Library.unique_id l))
                        (ensures (Library.unique_id (filter f l)))
                           [SMTPat (filter f l)]
let rec filter_uni1 f l = 
  match l with
  |[] -> ()
  |x::xs -> filter_uni1 f xs

val fst : nat * nat -> nat
let fst (id,ele) = id
val snd : nat * nat -> nat
let snd (id,ele) = ele

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s 
        -> Tot (b:bool {(b = true <==> (forall e. mem e s1 ==> (forall a. mem a tr.l /\ opa a /\ snd e = get_ele a ==>
                       (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                        not (tr.vis a r)) ==> fst e >= get_id a) /\ 
                       (mem ((fst e), Add (snd e)) tr.l /\
              (forall r. mem r tr.l /\ opr r /\ get_ele r = snd e ==> not (fst e <> get_id r && tr.vis ((fst e), Add (snd e)) r)))) /\
                 (forall a. mem a tr.l /\ opa a ==> (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not (tr.vis a r)) ==> member_ele (get_ele a) s1))})

#set-options "--z3rlimit 1000000"
let sim tr s1 = 
  let lsta = (filter (fun a -> opa a) tr.l) in
  let lstr = (filter (fun r -> opr r) tr.l) in
  let lst = filter (fun a -> not (existsb (fun r -> get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

  (forallb (fun e -> (forallb (fun a -> fst e >= get_id a) (filter (fun a -> get_ele a = snd e) lst)) &&
                  (mem ((fst e), Add (snd e)) tr.l && 
                  not (existsb (fun r -> tr.vis ((fst e), Add (snd e)) r ) 
                  (filter (fun r -> snd e = get_ele r && fst e <> get_id r) lstr)))) s1) &&
  (forallb (fun a -> member_ele (get_ele a) s1) lst)

val prop_oper : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (sim (append tr op) (app_op st op)))

#set-options "--z3rlimit 1000000"
let prop_oper tr st op = ()

val convergence : tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall e. mem e a <==> mem e b))
let convergence tr a b = ()

val remove : l:s 
           -> ele:(nat * nat)
           -> Pure s 
               (requires (mem ele l))
               (ensures (fun res -> (forall e. mem e res <==> mem e l /\ e <> ele) /\
                                 not (member_ele (snd ele) res) /\ not (member_id (fst ele) res) /\
                                 (forall e. member_id e res <==> member_id e l /\  e <> fst ele) /\
                                 (forall e. member_ele e res <==> member_ele e l /\ e <> snd ele)))
let rec remove l ele =
  match l with
  |[] -> []
  |x::xs -> if x = ele then xs else x::(remove xs ele)

val diff : a:s
         -> l:s
         -> Pure s
             (requires true)
             (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\
                             (forall e. mem e d /\ member_id (fst e) d <==> 
                                     mem e a /\ member_id (fst e) a /\ not (mem e l)) /\
                             (forall e. mem e d  /\ member_ele (snd e) d <==> 
                                        mem e a /\ member_ele (snd e) a /\ not (mem e l)) /\
                             (forall e. mem e a /\ mem e l ==> not (member_ele (snd e) d) /\ not (member_id (fst e) d))))
                             (decreases %[l;a])
#set-options "--z3rlimit 1000000"
let rec diff a l = 
  match a, l with
  |_,[] -> a
  |_,x::xs -> if (mem x a) then diff (remove a x) xs else diff a xs

val get_node : l:s 
             -> ele:nat
             -> Pure (nat * nat)
                 (requires (member_ele ele l))
                 (ensures (fun e -> mem e l /\ snd e = ele))
let rec get_node l ele =
  match l with
  |(id1,ele1)::xs -> if ele = ele1 then (id1,ele1) else get_node xs ele

val unionst : a:s
            -> b:s
            -> Pure s
              (requires (forall e. member_id e a ==> not (member_id e b)) /\
                        (forall e. member_ele e a ==> not (member_ele e b)))
              (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b) /\
                            (forall e. member_id e r <==> member_id e a \/ member_id e b) /\
                            (forall e. member_ele e r <==> member_ele e a \/ member_ele e b)))
let rec unionst a b =
  match a,b with
  |[],[] -> []
  |x::xs,_ -> x::unionst xs b
  |_ -> b

val lemma5 : a:s
           -> b:s
           -> Lemma (requires (forall e. member_id e a ==> not (member_id e b)))
                   (ensures (forall e e1. mem e a /\ not (member_ele (snd e) b) /\ 
                                     mem e1 a /\ member_ele (snd e1) b ==> fst e <> fst e1))
#set-options "--z3rlimit 100000000"
let rec lemma5 a b = 
  match a, b with
  |[],[] -> ()
  |x::xs,_ -> lemma5 xs b
  |[],_ -> ()

val pre_cond_merge1 : l:s -> a:s -> b:s
                    -> Tot (b1:bool {b1=true <==> (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))) /\
                        (forall e. (mem e l /\ mem e a /\ mem e b) ==> 
                              not (member_ele (snd e) (diff a l)) /\ not (member_ele (snd e) (diff b l)) /\
                              not (member_id (fst e) (diff a l)) /\ not (member_id (fst e) (diff b l))) /\
                        (forall e. mem e (diff a l) /\ member_ele (snd e) (diff b l) ==> 
                              fst (get_node a (snd e)) <> fst (get_node b (snd e))) /\
                        (forall e. mem e (diff b l) /\ member_ele (snd e) (diff a l) ==> 
                              fst (get_node b (snd e)) <> fst (get_node a (snd e)))})

#set-options "--z3rlimit 100000000"
let pre_cond_merge1 l a b =
  forallb (fun e -> not (member_id (fst e) (diff b l))) (diff a l) &&
  forallb (fun e -> not (member_ele (snd e) (diff a l)) && not (member_ele (snd e) (diff b l)) &&
                 not (member_id (fst e) (diff a l)) && not (member_id (fst e) (diff b l))) 
                 (filter (fun e -> mem e a && mem e b) l) &&
  forallb (fun e -> member_ele (snd e) b && member_ele (snd e) a && fst (get_node b (snd e)) <> fst (get_node a (snd e)))
                            (filter (fun e -> member_ele (snd e) (diff b l)) (diff a l)) &&
  forallb (fun e -> member_ele (snd e) b && member_ele (snd e) a && fst (get_node b (snd e)) <> fst (get_node a (snd e)))
                 (filter (fun e -> member_ele (snd e) (diff a l)) (diff b l))

val merge1 : l:s
           -> a:s 
           -> b:s 
           -> Pure s
            (requires pre_cond_merge1 l a b)
            (ensures (fun res -> (forall e. member_ele e res ==> member_ele e a \/ member_ele e b) /\ 
                             (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                         (mem e (diff a l) /\ member_ele (snd e) (diff a l) /\ not (member_ele (snd e) (diff b l))) \/
                         (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ not (member_ele (snd e) (diff a l))) \/
                           (mem e (diff a l) /\ member_ele (snd e) (diff a l) /\ member_ele (snd e) (diff b l) /\
                           fst (get_node a (snd e)) > fst (get_node b (snd e))) \/
                           (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ member_ele (snd e) (diff a l) /\
                           fst (get_node b (snd e)) > fst (get_node a (snd e))))))
                              (decreases %[(length l); (length a); (length b)])

#set-options "--z3rlimit 100000000"
let merge1 l a b = 
  let i = filter (fun e -> mem e a && mem e b) l in
  assert (forall e. mem e i <==> mem e l /\ mem e a /\ mem e b);
  assert (forall e. member_ele e i ==> member_ele e l /\ member_ele e a /\ member_ele e b);
  let la = diff a l in let lb = diff b l in
  let la1 = filter (fun e -> member_ele (snd e) la && not (member_ele (snd e) lb)) la in
  let lb1 = filter (fun e -> member_ele (snd e) lb && not (member_ele (snd e) la)) lb in
  let la2 = filter (fun e -> member_ele (snd e) la && member_ele (snd e) lb && 
                          fst (get_node a (snd e)) > fst (get_node b (snd e))) la in
  let lb2 = filter (fun e -> member_ele (snd e) la && member_ele (snd e) lb && 
                          fst (get_node b (snd e)) > fst (get_node a (snd e))) lb in
  lemma5 la lb;
  assert (forall e. member_id e la1 ==> not (member_id e la2));
  lemma5 lb la;
  assert (forall e. member_id e lb1 ==> not (member_id e lb2));
  let u1 = unionst i la1 in
  let u2 = unionst u1 lb1 in
  let u3 = unionst u2 la2 in
  unionst u3 lb2

val pre_cond_merge : ltr:ae op
                   -> l:s 
                   -> atr:ae op
                   -> a:s 
                   -> btr:ae op
                   -> b:s
                   -> Tot (r:bool {r = true <==> (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b)})
#set-options "--z3rlimit 10000000"
let pre_cond_merge ltr l atr a btr b =
  forallb (fun e -> not (mem_id (get_id e) atr.l)) ltr.l &&
  forallb (fun e -> not (mem_id (get_id e) btr.l)) ltr.l &&
  forallb (fun e -> not (mem_id (get_id e) btr.l)) atr.l &&
  sim ltr l && sim (union ltr atr) a && sim (union ltr btr) b

val lem_sim : tr:ae op
            -> s1:s
            -> Lemma (requires (sim tr s1))
                    (ensures (forall e. mem e s1 <==> (forall a. mem a tr.l /\ opa a /\ snd e = get_ele a ==>
                              (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                 not (tr.vis a r)) ==> fst e >= get_id a) /\ 
                                 (mem ((fst e), Add (snd e)) tr.l /\
             (forall r. mem r tr.l /\ opr r /\ get_ele r = snd e /\ fst e <> get_id r ==>
                       not (tr.vis ((fst e), Add (snd e)) r)))))

#set-options "--z3rlimit 10000000"
let lem_sim tr s1 = ()

val lemma1 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> a:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (pre_cond_merge ltr l atr a btr b))
                   (ensures (forall e. (mem e (diff a l)) ==> (mem ((fst e), Add (snd e)) atr.l)) /\
                            (forall e. (mem e (diff b l)) ==> (mem ((fst e), Add (snd e)) btr.l)))

#set-options "--z3rlimit 10000000"
let lemma1 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  ()

val lemma6 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> a:s 
           -> btr:ae op
           -> b:s
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                   (ensures (forall e. member_id e (diff a l) ==> not (member_id e (diff b l))))

#set-options "--z3rlimit 10000000"
let lemma6 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr a btr b; ()

val merge : ltr:ae op
          -> l:s 
          -> atr:ae op
          -> a:s 
          -> btr:ae op
          -> b:s 
          -> Pure s (requires (pre_cond_merge ltr l atr a btr b))
                   (ensures (fun res -> pre_cond_merge1 l a b /\ res = merge1 l a b))

#set-options "--z3rlimit 10000000"
let merge ltr l atr a btr b = 
  lemma6 ltr l atr a btr b;
  merge1 l a b 

val lemma12 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> a:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (pre_cond_merge ltr l atr a btr b))
                    (ensures (forall e. mem e (diff a l) ==> member_ele (snd e) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let lemma12 ltr l atr a btr b = 
  lemma6 ltr l atr a btr b

val lemma13 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> a:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (pre_cond_merge ltr l atr a btr b))
                    (ensures (forall e. mem e (diff b l) ==> member_ele (snd e) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let lemma13 ltr l atr a btr b =
  lemma6 ltr l atr a btr b

val lemma4 : ltr:ae op
           -> l:s
           -> atr:ae op
           -> aa:s
           -> btr:ae op
           -> b:s
           -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                             (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                   (ensures (forall e. mem e (merge ltr l atr aa btr b) ==>
                            (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\
                    (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele r = snd e /\ fst e <> get_id r ==> 
                                  not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) r)))))

#set-options "--z3rlimit 10000000"
let lemma4 ltr l atr a btr b = 
  lemma1 ltr l atr a btr b

val lemma31 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> aa:s
            -> btr:ae op
            -> b:s
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                              (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall e. mem e l /\ mem e aa /\ mem e b ==> 
                             (forall a. mem a (absmerge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
             (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                not ((absmerge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000000"
let lemma31 ltr l atr a btr b = ()

val lemma32 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> aa:s
            -> btr:ae op
            -> b:s
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                                (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall e. (mem e (diff aa l) /\ member_ele (snd e) (diff aa l) /\ 
                                   not (member_ele (snd e) (diff b l))) ==> 
                                  (forall a. mem a (absmerge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
             (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                  not ((absmerge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000000"
let lemma32 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr a btr b;
  lemma12 ltr l atr a btr b;
  lemma13 ltr l atr a btr b;
  ()

val lemma33 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> aa:s
            -> btr:ae op
            -> b:s
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                              (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall e. (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ 
                                not (member_ele (snd e) (diff aa l))) ==> 
                                    (forall a. mem a (absmerge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
           (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                    not ((absmerge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000000"
let lemma33 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr a btr b;
  lemma12 ltr l atr a btr b;
  lemma13 ltr l atr a btr b; 
  ()

val lemma34 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> aa:s
            -> btr:ae op
            -> b:s
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                              (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall e. (mem e (diff aa l) /\ member_ele (snd e) (diff aa l) /\ 
                                member_ele (snd e) (diff b l) /\
                                  fst (get_node aa (snd e)) > fst (get_node b (snd e))) ==> 
                                    (forall a. mem a (absmerge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
            (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                    not ((absmerge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000000"
let lemma34 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr a btr b;
  lemma12 ltr l atr a btr b;
  lemma13 ltr l atr a btr b;
  lemma4 ltr l atr a btr b;
  ()

val lemma35 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> aa:s
            -> btr:ae op
            -> b:s
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                              (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall e. (mem e (diff b l) /\ member_ele (snd e) (diff b l) /\ member_ele (snd e) (diff aa l) /\
                                  fst (get_node b (snd e)) > fst (get_node aa (snd e))) ==> 
                                    (forall a. mem a (absmerge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
           (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                    not ((absmerge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000000"
let lemma35 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr a btr b;
  lemma12 ltr l atr a btr b;
  lemma13 ltr l atr a btr b;
  lemma4 ltr l atr a btr b;
  ()

val lemma3 : ltr:ae op
           -> l:s
           -> atr:ae op
           -> aa:s
           -> btr:ae op
           -> b:s
           -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                             (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                   (ensures (forall e. mem e (merge ltr l atr aa btr b) ==> 
                                (forall a. mem a (absmerge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
       (forall r. mem r (absmerge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                not ((absmerge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000000"
let lemma3 ltr l atr a btr b =
  lemma31 ltr l atr a btr b;
  lemma32 ltr l atr a btr b;
  lemma33 ltr l atr a btr b;
  lemma34 ltr l atr a btr b;
  lemma35 ltr l atr a btr b; ()

#set-options "--z3rlimit 10000000"
val lemma21 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> aa:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                              (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall a. mem a ltr.l /\ opa a ==> (forall r. mem r (absmerge ltr atr btr).l /\ 
                               opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                               not ((absmerge ltr atr btr).vis a r)) 
                                   ==> member_ele (get_ele a) (merge ltr l atr aa btr b)))

#set-options "--z3rlimit 10000000"
let lemma21 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr a btr b;
  lemma12 ltr l atr a btr b;
  lemma13 ltr l atr a btr b;
  lemma6 ltr l atr a btr b;
  lemma3 ltr l atr a btr b;
  lemma4 ltr l atr a btr b;
  ()

val lemma22 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> aa:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                              (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall a. mem a atr.l /\ opa a ==> (forall r. mem r (absmerge ltr atr btr).l /\ 
                                 opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                 not ((absmerge ltr atr btr).vis a r)) 
                                       ==> member_ele (get_ele a) (merge ltr l atr aa btr b)))

#set-options "--z3rlimit 10000000"
let lemma22 ltr l atr aa btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) aa;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr aa btr b;
  lemma12 ltr l atr aa btr b;
  lemma13 ltr l atr aa btr b;
  assert (forall e e1. mem e l /\ mem e1 aa /\ snd e = snd e1 ==> fst e <= fst e1);
  assert (forall e e1. mem e l /\ mem e1 b /\ snd e = snd e1 ==> fst e <= fst e1);
  assert (forall a. mem a atr.l /\ opa a ==> (forall r. mem r (absmerge ltr atr btr).l /\ 
         opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((absmerge ltr atr btr).vis a r))
                  ==> member_ele (get_ele a) aa);
  assert (forall a. mem a atr.l /\ opa a ==> (forall r. mem r (absmerge ltr atr btr).l /\ 
         opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((absmerge ltr atr btr).vis a r)) 
                                     ==> not (mem (get_id a, get_ele a) l)); 
  ()

val lemma23 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> aa:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                              (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                    (ensures (forall a. mem a btr.l /\ opa a ==> (forall r. mem r (absmerge ltr atr btr).l /\ 
           opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((absmerge ltr atr btr).vis a r)) 
                                        ==> member_ele (get_ele a) (merge ltr l atr aa btr b)))

#set-options "--z3rlimit 10000000"
let lemma23 ltr l atr aa btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) aa;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr aa btr b;
  lemma12 ltr l atr aa btr b;
  lemma13 ltr l atr aa btr b;
  assert (forall e e1. mem e l /\ mem e1 aa /\ snd e = snd e1 ==> fst e <= fst e1);
  assert (forall e e1. mem e l /\ mem e1 b /\ snd e = snd e1 ==> fst e <= fst e1);
  assert (forall a. mem a btr.l /\ opa a ==> (forall r. mem r (absmerge ltr atr btr).l /\ 
        opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((absmerge ltr atr btr).vis a r)) 
                               ==> member_ele (get_ele a) b);
  assert (forall a. mem a btr.l /\ opa a ==> (forall r. mem r (absmerge ltr atr btr).l /\ 
      opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((absmerge ltr atr btr).vis a r)) 
                               ==> not (mem (get_id a, get_ele a) l)); 
  ()

val lemma2 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> aa:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (pre_cond_merge ltr l atr aa btr b) /\
                             (forall e. member_id e (diff aa l) ==> not (member_id e (diff b l))))
                   (ensures (forall a. mem a (absmerge ltr atr btr).l /\ opa a ==> 
                               (forall r. mem r (absmerge ltr atr btr).l /\ 
         opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((absmerge ltr atr btr).vis a r)) 
                                     ==> member_ele (get_ele a) (merge ltr l atr aa btr b)))

#set-options "--z3rlimit 10000000"
let lemma2 ltr l atr a btr b = 
  lemma21 ltr l atr a btr b;
  lemma22 ltr l atr a btr b;
  lemma23 ltr l atr a btr b; ()

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
  lemma6 ltr l atr a btr b;
  lemma2 ltr l atr a btr b;
  lemma3 ltr l atr a btr b;
  lemma4 ltr l atr a btr b;
  ()

instance _ : mrdt s op = {
  Library.init = init;
  Library.sim = sim;
  Library.pre_cond_op = pre_cond_op;
  Library.app_op = app_op;
  Library.prop_oper = prop_oper;
  Library.pre_cond_merge1 = pre_cond_merge1;
  Library.pre_cond_merge = pre_cond_merge;
  Library.merge1 = merge1;
  Library.merge = merge;
  Library.prop_merge = prop_merge;
  Library.convergence = convergence
}

