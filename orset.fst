module Orset
open FStar.List.Tot

open Library

val member_s : id:nat 
             -> l:list (nat * nat)
             -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_s n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_s n xs

val unique_s : l:list (nat * nat)
             -> Tot bool
let rec unique_s l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_s id xs) && unique_s xs

type s = l:list (nat (*unique id*) * nat (*element*)) {unique_s l}

type rval = |Val : list nat -> rval
            |Bot

val init : s
let init = []

val mem_ele_s : ele:nat -> s1:s -> Tot (b:bool {b = true <==> (exists id. mem (id,ele) s1)})
let rec mem_ele_s ele s =
  match s with
  |[] -> false
  |(_,ele1)::xs -> ele = ele1 || mem_ele_s ele xs

val filter_uni : f:((nat * nat) -> bool)
               -> l:list (nat * nat) 
               -> Lemma (requires (unique_s l))
                       (ensures (unique_s (filter f l)))
                               [SMTPat (filter f l)]

#set-options "--z3rlimit 1000000"
let rec filter_uni f l =
  match l with
  |[] -> ()
  |x::xs -> filter_uni f xs

type op =
  |Add : nat (*element*) -> op
  |Rem : nat (*element*) -> op
  |Rd

val opa : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id ele. op1 = (id, Add ele)) /\ get_op op1 <> Rd})
let opa op1 =
  match op1 with
  |(_, Add _) -> true
  |_ -> false

val opr : op1:(nat * op) -> Tot (b:bool {b = true <==> (exists id ele. op1 = (id, Rem ele)) /\ get_op op1 <> Rd})
let opr op1 =
  match op1 with
  |(_, Rem _) -> true
  |_ -> false

val mem_ele : ele:nat -> l:list (nat * op) -> Tot (b:bool {b = true <==> (exists id. mem (id, (Add ele)) l) \/ (exists id. mem (id, (Rem ele)) l)})
let rec mem_ele ele l =
  match l with
  |[] -> false
  |(_, (Add ele1))::xs -> ele = ele1 || mem_ele ele xs
  |(_, (Rem ele1))::xs -> ele = ele1 || mem_ele ele xs
  |(_, Rd)::xs -> mem_ele ele xs

val get_ele : op1:(nat * op){get_op op1 <> Rd} -> Tot (ele:nat {(exists id. op1 = (id, Add ele) \/ op1 = (id, Rem ele))})
let get_ele op =
  match op with
  |(_, (Add ele)) -> ele
  |(_, (Rem ele)) -> ele

val pre_cond_app_op : s1:s
             -> op:(nat * op)
             -> Tot (b:bool {b=true <==> not (member_s (get_id op) s1)})
let pre_cond_app_op s1 op = not (member_s (get_id op) s1)

let pre_cond_prop_oper tr s1 op = true

val get_set_s : s1:s -> Tot (l:list nat {(forall e. mem e l <==> mem_ele_s e s1)})
let rec get_set_s s1 = 
  match s1 with
  |[] -> []
  |(_,ele)::xs -> if mem_ele_s ele xs then get_set_s xs else ele::get_set_s xs

val app_op : s1:s
           -> op:(nat * op)
           -> Pure (s * rval)
                 (requires pre_cond_app_op s1 op)
                 (ensures (fun res -> (opa op ==> (get_rval res = Bot) /\ (forall e. mem e s1 \/ e = ((get_id op), (get_ele op)) <==> mem e (get_st res))) /\
                                   (opr op ==> (get_rval res = Bot) /\ (forall e. mem e (get_st res) <==> mem e s1 /\ snd e <> get_ele op)) /\ (not (opa op || opr op) ==> (get_rval res = Val (get_set_s s1)) /\ (get_st res = s1))))
let app_op s1 op1 =
  match op1 with
  |(id, Add ele) -> ((id, ele)::s1, Bot)
  |(id, Rem ele) -> (filter (fun e -> snd e <> ele) s1, Bot)
  |(_, Rd) -> (s1, Val (get_set_s s1))

val filter_uni1 : f:((nat * op) -> bool)
                -> l:list (nat * op) 
                -> Lemma (requires (unique_id l))
                        (ensures (unique_id (filter f l)))
                        [SMTPat (filter f l)]
let rec filter_uni1 f l = 
  match l with
  |[] -> ()
  |x::xs -> filter_uni1 f xs

val except : f:((nat * op) -> bool)
           -> l:list (nat * op) {unique_id l}
           -> Tot (l1:list (nat * op) {(forall e. mem e l1 <==> mem e l /\ not (f e)) /\ unique_id l1})
let rec except f l =
  match l with
  |[] -> []
  |hd::tl -> if not (f hd) then hd::(except f tl) else except f tl

val existsb : f:((nat * op) -> bool)
            -> l:list (nat * op)
            -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true})
let rec existsb f l =
    match l with
    |[] -> false
    |hd::tl -> if f hd then true else existsb f tl

val get_set : tr:list (nat * op){unique_id tr} -> Tot (s1:list nat {(forall e. mem e s1 <==> mem_ele e tr)})
let rec get_set l =
  match l with
  |[] -> []
  |(_, Add x)::xs -> if mem_ele x xs then get_set xs else x::(get_set xs)
  |(_, Rem x)::xs -> if mem_ele x xs then get_set xs else x::(get_set xs)
  |(_, Rd)::xs -> get_set xs

val extract : r:rval {exists v. r = Val v} -> list nat
let extract (Val s) = s

val forallo : f:((nat * op) -> bool)
            -> l:list (nat * op)
            -> Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forallo f l =
  match l with
  |[] -> true
  |hd::tl -> if f hd then forallo f tl else false

val spec : o:(nat * op) -> tr:ae op
         -> Tot (r:rval {(get_op o = Rd ==> r <> Bot /\ (forall e. mem e (extract r) <==> (exists id. mem (id, Add e) tr.l /\
                                    (forall r. mem r tr.l /\ id <> get_id r /\ opr r /\ e = get_ele r ==>
                                              not (tr.vis (id, Add e) r))))) /\
                       (opa o ==> r = Bot) /\ (opr o ==> r = Bot)})
let spec o tr =
  match o with
  |(_, Add _) -> Bot
  |(_, Rem _) -> Bot
  |(_, Rd) -> let lsta = (filter (fun a -> opa a) tr.l) in
  let lstr = (filter (fun r -> opr r) tr.l) in
  let lst = except (fun a -> get_op a <> Rd && opa a && (existsb (fun r -> get_op r <> Rd && get_op a <> Rd && opa a && opr r && get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in Val (get_set lst)

#set-options "--query_stats"
val sim : tr:ae op
        -> s1:s 
        -> Tot (b:bool {b = true <==> (forall a. mem a s1 <==> (mem ((fst a), Add (snd a)) tr.l /\
                                   (forall r. mem r tr.l /\ fst a <> get_id r /\ opr r /\ snd a = get_ele r ==>
                                         not (tr.vis ((fst a), Add (snd a)) r))))})
let sim tr s1 =
  let lsta = (filter (fun a -> opa a) tr.l) in
  let lstr = (filter (fun r -> opr r) tr.l) in
  let lst = except (fun a -> get_op a <> Rd && opa a &&  (existsb (fun r -> get_op r <> Rd && get_op a <> Rd && get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

  forallo (fun e -> get_op e <> Rd && mem ((get_id e), (get_ele e)) s1) lst &&
  forallb (fun e -> mem ((fst e), Add (snd e)) lst) s1

val diff2 : a:list (nat * nat)
          -> l:list (nat * nat)
          -> Pure (list (nat * nat))
            (requires (unique_s a /\ unique_s l))
            (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\ unique_s d )) (decreases %[l;a;l;a])
let diff2 a l = 
  filter (fun e -> not (mem e l)) a

val remove : l:s 
           -> ele:(nat * nat)
           -> Pure s 
             (requires true)
             (ensures (fun res -> (forall e. mem e res <==> mem e l /\ e <> ele)))
let remove l ele =
  filter (fun e -> e <> ele) l

val pre_cond_merge : l:s -> a:s -> b:s
                    -> Tot (b1:bool {b1=true <==> (forall e. mem e (diff2 a l) ==> not (member_s (fst e) b)) /\
                                               (forall e. mem e (diff2 b l) ==> not (member_s (fst e) a))})
let pre_cond_merge l a b =
  forallb (fun e -> not (member_s (fst e) b)) (diff2 a l) &&
  forallb (fun e -> not (member_s (fst e) a)) (diff2 b l)

let pre_cond_prop_merge ltr l atr a btr b = true

val merge : l:s
           -> a:s 
           -> b:s 
           -> Pure s 
             (requires pre_cond_merge l a b)
             (ensures (fun res -> (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                               (mem e (diff2 a l)) \/ (mem e (diff2 b l)))))    
                               (decreases %[l;a;b])
let rec merge l a b = 
  match l,a,b with
  |[],[],[] -> []
  |x::xs,_,_ -> if (mem x a && mem x b) then x::(merge xs (remove a x) (remove b x)) 
                 else if (mem x a) then (merge xs (remove a x) b)
                   else if (mem x b) then (merge xs a (remove b x))
                     else (merge xs a b)
  |[],x::xs,_ -> x::(merge [] xs b)
  |[],[],x::xs -> b

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
    assert ((forall e. mem e (diff2 a l) ==> not (member_s (fst e) b)) /\
            (forall e. mem e (diff2 b l) ==> not (member_s (fst e) a))); 
    assert (forall e. (mem e l /\ mem e a /\ mem e b) <==> (mem ((fst e), Add (snd e)) ltr.l /\ 
           (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\ opr r /\ snd e = get_ele r ==> 
           not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) r)))); 

    assert (forall e. (mem e (diff2 a l)) <==> (mem ((fst e), Add (snd e)) atr.l /\ (forall r. mem r atr.l /\ fst e <> get_id r /\
           opr r /\ snd e = get_ele r ==> not (atr.vis ((fst e), Add (snd e)) r)))); 

    assert (forall e. (mem e (diff2 b l)) <==> (mem ((fst e), Add (snd e)) btr.l /\ (forall r. mem r btr.l /\ fst e <> get_id r /\
           opr r /\ snd e = get_ele r ==> not (btr.vis ((fst e), Add (snd e)) r)))); 

    assert (forall e. (mem ((fst e), Add (snd e)) ltr.l /\ (forall r. mem r (absmerge ltr atr btr).l /\ fst e <> get_id r /\
           opr r /\ snd e = get_ele r ==> not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))) \/ 
           (mem ((fst e), Add (snd e)) atr.l /\ (forall r. mem r atr.l /\ fst e <> get_id r /\ 
           opr r /\ snd e = get_ele r ==> not (atr.vis ((fst e), Add (snd e)) r))) \/
           (mem ((fst e), Add (snd e)) btr.l /\ (forall r. mem r btr.l /\ fst e <> get_id r /\ 
           opr r /\ snd e = get_ele r ==> not (btr.vis ((fst e), Add (snd e)) r))) <==>
           (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ 
           fst e <> get_id r /\ opr r /\ snd e = get_ele r ==> not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))));

    assert (forall e. ((mem e l /\ mem e a /\ mem e b) \/ (mem e (diff2 a l)) \/ (mem e (diff2 b l))) <==> 
           (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ 
           fst e <> get_id r /\ opr r /\ snd e = get_ele r ==> not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))));

    assert (forall e. (mem e (merge l a b)) <==> 
           (mem ((fst e), Add (snd e)) (absmerge ltr atr btr).l /\ (forall r. mem r (absmerge ltr atr btr).l /\ 
           fst e <> get_id r /\ opr r /\ snd e = get_ele r ==> not ((absmerge ltr atr btr).vis ((fst e), Add (snd e)) r))));
    ()

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
                        (ensures (forall e. mem e a <==> mem e b))
let convergence tr a b = ()

val prop_spec : tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                      (ensures (get_op op = Rd ==> (forall e. mem e (extract (get_rval (app_op st op))) <==>
                                                mem e (extract (spec op tr)))) /\
                               (get_op op <> Rd ==> (get_rval (app_op st op) = spec op tr)))
#set-options "--z3rlimit 1000000"
let prop_spec tr st op = ()

instance orset : mrdt s op rval = {
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
