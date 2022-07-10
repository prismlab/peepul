module Orset_space
open FStar.List.Tot

#set-options "--query_stats"

open Library

val member_id_s : id:nat 
                -> l:list (nat * nat)
                -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
let rec member_id_s n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_id_s n xs

val unique_id_s : l:list (nat * nat)
                -> Tot bool
let rec unique_id_s l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member_id_s id xs) && unique_id_s xs

val member_ele_s : ele:nat
                 -> l:list (nat * nat)
                 -> Tot (b:bool{(exists id. mem (id,ele) l) <==> b=true})
let rec member_ele_s ele l =
  match l with
  |[] -> false
  |(_,ele1)::xs -> (ele = ele1) || member_ele_s ele xs

val unique_ele_s : l:list (nat * nat)
                 -> Tot bool
let rec unique_ele_s l =
  match l with
  |[] -> true
  |(_,ele)::xs -> not (member_ele_s ele xs) && unique_ele_s xs

type s = l:list (nat (*unique id*) * nat (*unique element*)) {unique_id_s l /\ unique_ele_s l}

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
               -> Lemma (requires (unique_id_s l /\ unique_ele_s l))
                       (ensures (unique_id_s (filter f l) /\ unique_ele_s (filter f l)))
                                  [SMTPat (filter f l)]

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

let pre_cond_do s1 op = not (member_id_s (get_id op) s1)

let pre_cond_prop_do tr s1 op = true

val get_set_s : s1:s -> Tot (l:list nat {(forall e. mem e l <==> mem_ele_s e s1)})
let rec get_set_s s1 = 
  match s1 with
  |[] -> []
  |(_,ele)::xs -> if mem_ele_s ele xs then get_set_s xs else ele::get_set_s xs

val update : s1:s
           -> ele:nat
           -> id:nat
           -> Pure s
               (requires (member_ele_s ele s1) /\ not (member_id_s id s1))
               (ensures (fun u -> (forall e. mem e s1 /\ snd e <> ele <==> mem e u /\ snd e <> ele) /\
                               (forall e. mem e u /\ fst e <> id /\ member_id_s (fst e) u <==> 
                                     mem e s1 /\ snd e <> ele /\ member_id_s (fst e) s1) /\
                                (forall e. member_ele_s e s1 <==> member_ele_s e u) /\
                                (forall e. mem e u /\ e <> (id,ele) <==> mem e s1 /\ snd e <> ele) /\ mem (id,ele) u))
                                (decreases s1)
let rec update s1 ele id =
  match s1 with
  |[] -> []
  |(id1,ele1)::xs -> if ele = ele1 then (id,ele1)::xs else (id1,ele1):: update xs ele id

val remove_ele : s1:s
                 -> ele:nat
                 -> Pure s
                 (requires (member_ele_s ele s1))
                 (ensures (fun u -> (forall e. mem e s1 /\ snd e <> ele <==> mem e u)))
                 (decreases s1)
let rec remove_ele s1 ele =
  match s1 with
  |[] -> []
  |(id1,ele1)::xs -> if ele = ele1 then xs else (id1,ele1):: remove_ele xs ele
  
val do : s1:s
       -> op:(nat * op)
       -> Pure (s * rval)
         (requires pre_cond_do s1 op)
         (ensures (fun res -> (opa op ==> (get_rval res = Bot) /\ (forall e. mem e s1 /\ snd e <> get_ele op <==> mem e (get_st res) /\ snd e <> get_ele op) /\
                           (forall e. mem e (get_st res) /\ fst e <> get_id op /\ member_id_s (fst e) (get_st res) <==> mem e s1 /\ snd e <> get_ele op /\ member_id_s (fst e) s1) /\
                           (forall e. member_ele_s e s1 \/ e = get_ele op <==> member_ele_s e (get_st res)) /\
                     (forall e. mem e (get_st res) /\ e <> ((get_id op), (get_ele op)) <==> mem e s1 /\ snd e <> get_ele op) /\
                                   mem ((get_id op), (get_ele op)) (get_st res)) /\
                     (opr op ==> (get_rval res = Bot) /\ (forall e. mem e (get_st res) <==> mem e s1 /\ snd e <> get_ele op)) /\ (get_op op = Rd ==> get_rval res = Val (get_set_s s1) /\ get_st res = s1)))

let do s1 op =
  match op with
  |(_, Add _) -> if member_ele_s (get_ele op) s1 then (update s1 (get_ele op) (get_id op), Bot)
                    else (((get_id op),(get_ele op))::s1, Bot)
  |(_, Rem _) -> if member_ele_s (get_ele op) s1 then (remove_ele s1 (get_ele op), Bot) else (s1, Bot)
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

val filtero : f:((nat * op) -> bool)
             -> l:list (nat * op) {unique_id l}
             -> Tot (l1:list (nat * op) {(forall e. mem e l1 <==> mem e l /\ (f e)) /\ unique_id l1})
let rec filtero f l =
  match l with
  |[] -> []
  |hd::tl -> if (f hd) then hd::(filtero f tl) else filtero f tl

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

val fst : (nat * nat) -> nat
let fst (id,ele) = id
val snd : (nat * nat) -> nat
let snd (id,ele) = ele

val sim : tr:ae op
        -> s1:s 
        -> Tot (b:bool {(b = true <==> (forall e. mem e s1 ==> (forall a. mem a tr.l /\ opa a /\ snd e = get_ele a ==>
                       (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                        not (tr.vis a r)) ==> fst e >= get_id a) /\ 
                       (mem ((fst e), Add (snd e)) tr.l /\
   (forall r. mem r tr.l /\ opr r /\ get_ele r = snd e /\ fst e <> get_id r ==> not (tr.vis ((fst e), Add (snd e)) r)))) /\
                 (forall a. mem a tr.l /\ opa a ==> (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not (tr.vis a r)) ==> member_ele_s (get_ele a) s1))})

#set-options "--z3rlimit 1000"
let sim tr s1 = 
  let lsta = (filtero (fun a -> opa a) tr.l) in
  let lstr = (filtero (fun r -> opr r) tr.l) in
  let lst = filtero (fun a -> get_op a <> Rd && opa a && not (existsb (fun r -> get_op r <> Rd && get_op a <> Rd && opa a && opr r && get_id a <> get_id r && get_ele r = get_ele a && tr.vis a r) lstr)) lsta in

  (forallb (fun e -> (forallo (fun a -> fst e >= get_id a) (filtero (fun a -> get_op a <> Rd && get_ele a = snd e) lst)) &&
                  (mem ((fst e), Add (snd e)) tr.l && 
                  not (existsb (fun r -> tr.vis ((fst e), Add (snd e)) r) 
                  (filtero (fun r -> get_op r <> Rd && snd e = get_ele r && fst e <> get_id r) lstr)))) s1) &&
  (forallo (fun a -> get_op a <> Rd && member_ele_s (get_ele a) s1) lst)

val prop_do : tr:ae op
            -> st:s
            -> op:(nat * op)
            -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                              (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                    (ensures (sim (abs_do tr op) (get_st (do st op))))

#set-options "--z3rlimit 1000"
let prop_do tr st op = ()

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
                                 not (member_ele_s (snd ele) res) /\ not (member_id_s (fst ele) res) /\
                                 (forall e. member_id_s e res <==> member_id_s e l /\  e <> fst ele) /\
                                 (forall e. member_ele_s e res <==> member_ele_s e l /\ e <> snd ele)))
let rec remove l ele =
  match l with
  |[] -> []
  |x::xs -> if x = ele then xs else x::(remove xs ele)

val diff : a:s
         -> l:s
         -> Pure s
             (requires true)
             (ensures (fun d -> (forall e. mem e d <==> mem e a /\ not (mem e l)) /\
                             (forall e. mem e d /\ member_id_s (fst e) d <==> 
                                     mem e a /\ member_id_s (fst e) a /\ not (mem e l)) /\
                             (forall e. mem e d  /\ member_ele_s (snd e) d <==> 
                                        mem e a /\ member_ele_s (snd e) a /\ not (mem e l)) /\
                             (forall e. mem e a /\ mem e l ==> not (member_ele_s (snd e) d) /\ not (member_id_s (fst e) d))))
                             (decreases %[l;a])
#set-options "--z3rlimit 100"
let rec diff a l = 
  match a, l with
  |_,[] -> a
  |_,x::xs -> if (mem x a) then diff (remove a x) xs else diff a xs

val get_node : l:s 
             -> ele:nat
             -> Pure (nat * nat)
                 (requires (member_ele_s ele l))
                 (ensures (fun e -> mem e l /\ snd e = ele))
let rec get_node l ele =
  match l with
  |(id1,ele1)::xs -> if ele = ele1 then (id1,ele1) else get_node xs ele

val unionst : a:s
            -> b:s
            -> Pure s
              (requires (forall e. member_id_s e a ==> not (member_id_s e b)) /\
                        (forall e. member_ele_s e a ==> not (member_ele_s e b)))
              (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b) /\
                            (forall e. member_id_s e r <==> member_id_s e a \/ member_id_s e b) /\
                            (forall e. member_ele_s e r <==> member_ele_s e a \/ member_ele_s e b)))
let rec unionst a b =
  match a,b with
  |[],[] -> []
  |x::xs,_ -> x::unionst xs b
  |_ -> b

val lemma5 : a:s
           -> b:s
           -> Lemma (requires (forall e. member_id_s e a ==> not (member_id_s e b)))
                   (ensures (forall e e1. mem e a /\ not (member_ele_s (snd e) b) /\ 
                                     mem e1 a /\ member_ele_s (snd e1) b ==> fst e <> fst e1))
#set-options "--z3rlimit 1000"
let rec lemma5 a b = 
  match a, b with
  |[],[] -> ()
  |x::xs,_ -> lemma5 xs b
  |[],_ -> ()

val pre_cond_merge : l:s -> a:s -> b:s
                   -> Tot (b1:bool {b1=true <==> (forall e. member_id_s e (diff a l) ==> not (member_id_s e (diff b l))) /\
                        (forall e. (mem e l /\ mem e a /\ mem e b) ==> 
                              not (member_ele_s (snd e) (diff a l)) /\ not (member_ele_s (snd e) (diff b l)) /\
                              not (member_id_s (fst e) (diff a l)) /\ not (member_id_s (fst e) (diff b l))) /\
                        (forall e. mem e (diff a l) /\ member_ele_s (snd e) (diff b l) ==> 
                              fst (get_node a (snd e)) <> fst (get_node b (snd e))) /\
                        (forall e. mem e (diff b l) /\ member_ele_s (snd e) (diff a l) ==> 
                              fst (get_node b (snd e)) <> fst (get_node a (snd e)))})

#set-options "--z3rlimit 1000"
let pre_cond_merge l a b =
  forallb (fun e -> not (member_id_s (fst e) (diff b l))) (diff a l) &&
  forallb (fun e -> not (member_ele_s (snd e) (diff a l)) && not (member_ele_s (snd e) (diff b l)) &&
                 not (member_id_s (fst e) (diff a l)) && not (member_id_s (fst e) (diff b l))) 
                 (filter (fun e -> mem e a && mem e b) l) &&
  forallb (fun e -> member_ele_s (snd e) b && member_ele_s (snd e) a && fst (get_node b (snd e)) <> fst (get_node a (snd e)))
                            (filter (fun e -> member_ele_s (snd e) (diff b l)) (diff a l)) &&
  forallb (fun e -> member_ele_s (snd e) b && member_ele_s (snd e) a && fst (get_node b (snd e)) <> fst (get_node a (snd e)))
                 (filter (fun e -> member_ele_s (snd e) (diff a l)) (diff b l))

val merge : l:s
           -> a:s 
           -> b:s 
           -> Pure s
            (requires pre_cond_merge l a b)
            (ensures (fun res -> (forall e. member_ele_s e res ==> member_ele_s e a \/ member_ele_s e b) /\ 
                             (forall e. mem e res <==> (mem e l /\ mem e a /\ mem e b) \/ 
                         (mem e (diff a l) /\ member_ele_s (snd e) (diff a l) /\ not (member_ele_s (snd e) (diff b l))) \/
                         (mem e (diff b l) /\ member_ele_s (snd e) (diff b l) /\ not (member_ele_s (snd e) (diff a l))) \/
                           (mem e (diff a l) /\ member_ele_s (snd e) (diff a l) /\ member_ele_s (snd e) (diff b l) /\
                           fst (get_node a (snd e)) > fst (get_node b (snd e))) \/
                           (mem e (diff b l) /\ member_ele_s (snd e) (diff b l) /\ member_ele_s (snd e) (diff a l) /\
                           fst (get_node b (snd e)) > fst (get_node a (snd e))))))
                              (decreases %[(length l); (length a); (length b)])

#set-options "--z3rlimit 100000"
let merge l a b = 
  let i = filter (fun e -> mem e a && mem e b) l in
  assert (forall e. mem e i <==> mem e l /\ mem e a /\ mem e b);
  assert (forall e. member_ele_s e i ==> member_ele_s e l /\ member_ele_s e a /\ member_ele_s e b);
  let la = diff a l in let lb = diff b l in
  let la1 = filter (fun e -> member_ele_s (snd e) la && not (member_ele_s (snd e) lb)) la in
  let lb1 = filter (fun e -> member_ele_s (snd e) lb && not (member_ele_s (snd e) la)) lb in
  let la2 = filter (fun e -> member_ele_s (snd e) la && member_ele_s (snd e) lb && 
                          fst (get_node a (snd e)) > fst (get_node b (snd e))) la in
  let lb2 = filter (fun e -> member_ele_s (snd e) la && member_ele_s (snd e) lb && 
                          fst (get_node b (snd e)) > fst (get_node a (snd e))) lb in
  lemma5 la lb;
  assert (forall e. member_id_s e la1 ==> not (member_id_s e la2));
  lemma5 lb la;
  assert (forall e. member_id_s e lb1 ==> not (member_id_s e lb2));
  let u1 = unionst i la1 in
  let u2 = unionst u1 lb1 in
  let u3 = unionst u2 la2 in
  unionst u3 lb2

let pre_cond_prop_merge ltr l atr a btr b = true

val lem_sim : tr:ae op
            -> s1:s
            -> Lemma (requires (sim tr s1))
                    (ensures (forall e. mem e s1 <==> (forall a. mem a tr.l /\ opa a /\ snd e = get_ele a ==>
                              (forall r. mem r tr.l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                 not (tr.vis a r)) ==> fst e >= get_id a) /\ 
                                 (mem ((fst e), Add (snd e)) tr.l /\
             (forall r. mem r tr.l /\ opr r /\ get_ele r = snd e /\ fst e <> get_id r ==>
                       not (tr.vis ((fst e), Add (snd e)) r)))))

#set-options "--z3rlimit 10000"
let lem_sim tr s1 = ()

val lemma1 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> a:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                             pre_cond_merge l a b /\ pre_cond_prop_merge ltr l atr a btr b)
                   (ensures (forall e. (mem e (diff a l)) ==> (mem ((fst e), Add (snd e)) atr.l)) /\
                            (forall e. (mem e (diff b l)) ==> (mem ((fst e), Add (snd e)) btr.l)))

#set-options "--z3rlimit 10000"
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
                   (ensures (forall e. member_id_s e (diff a l) ==> not (member_id_s e (diff b l))))

#set-options "--z3rlimit 10000"
let lemma6 ltr l atr a btr b = 
  lem_sim ltr l;
  lem_sim (union ltr atr) a;
  lem_sim (union ltr btr) b;
  lemma1 ltr l atr a btr b; ()

val lemma12 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> a:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                              pre_cond_merge l a b /\ pre_cond_prop_merge ltr l atr a btr b)
                    (ensures (forall e. mem e (diff a l) ==> member_ele_s (snd e) (merge l a b)))

#set-options "--z3rlimit 10000"
let lemma12 ltr l atr a btr b = 
  lemma6 ltr l atr a btr b

val lemma13 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> a:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b) /\
                              pre_cond_merge l a b /\ pre_cond_prop_merge ltr l atr a btr b)
                    (ensures (forall e. mem e (diff b l) ==> member_ele_s (snd e) (merge l a b)))

#set-options "--z3rlimit 10000"
let lemma13 ltr l atr a btr b =
  lemma6 ltr l atr a btr b

val lemma4 : ltr:ae op
           -> l:s
           -> atr:ae op
           -> aa:s
           -> btr:ae op
           -> b:s
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                             pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                             (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                   (ensures (forall e. mem e (merge l aa b) ==>
                            (mem ((fst e), Add (snd e)) (abs_merge ltr atr btr).l /\
                    (forall r. mem r (abs_merge ltr atr btr).l /\ opr r /\ get_ele r = snd e /\ fst e <> get_id r ==> 
                                  not ((abs_merge ltr atr btr).vis ((fst e), Add (snd e)) r)))))

#set-options "--z3rlimit 10000"
let lemma4 ltr l atr a btr b = 
  lemma1 ltr l atr a btr b

val lemma31 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> aa:s
            -> btr:ae op
            -> b:s
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                              pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\ 
                              (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall e. mem e l /\ mem e aa /\ mem e b ==> 
                             (forall a. mem a (abs_merge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
             (forall r. mem r (abs_merge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                not ((abs_merge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000"
let lemma31 ltr l atr a btr b = ()

val lemma32 : ltr:ae op
            -> l:s
            -> atr:ae op
            -> aa:s
            -> btr:ae op
            -> b:s
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                              pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                                (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall e. (mem e (diff aa l) /\ member_ele_s (snd e) (diff aa l) /\ 
                                   not (member_ele_s (snd e) (diff b l))) ==> 
                                  (forall a. mem a (abs_merge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
             (forall r. mem r (abs_merge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                  not ((abs_merge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000"
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
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                              pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                              (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall e. (mem e (diff b l) /\ member_ele_s (snd e) (diff b l) /\ 
                                not (member_ele_s (snd e) (diff aa l))) ==> 
                                    (forall a. mem a (abs_merge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
           (forall r. mem r (abs_merge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                    not ((abs_merge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000"
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
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                               pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                              (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall e. (mem e (diff aa l) /\ member_ele_s (snd e) (diff aa l) /\ 
                                member_ele_s (snd e) (diff b l) /\
                                  fst (get_node aa (snd e)) > fst (get_node b (snd e))) ==> 
                                    (forall a. mem a (abs_merge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
            (forall r. mem r (abs_merge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                    not ((abs_merge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000"
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
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                              pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                              (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall e. (mem e (diff b l) /\ member_ele_s (snd e) (diff b l) /\ member_ele_s (snd e) (diff aa l) /\
                                  fst (get_node b (snd e)) > fst (get_node aa (snd e))) ==> 
                                    (forall a. mem a (abs_merge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
           (forall r. mem r (abs_merge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                    not ((abs_merge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000"
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
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                             pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                             (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                   (ensures (forall e. mem e (merge l aa b) ==> 
                                (forall a. mem a (abs_merge ltr atr btr).l /\ opa a /\ snd e = get_ele a ==>
       (forall r. mem r (abs_merge ltr atr btr).l /\ opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                not ((abs_merge ltr atr btr).vis a r)) ==> fst e >= get_id a)))

#set-options "--z3rlimit 10000"
let lemma3 ltr l atr a btr b =
  lemma31 ltr l atr a btr b;
  lemma32 ltr l atr a btr b;
  lemma33 ltr l atr a btr b;
  lemma34 ltr l atr a btr b;
  lemma35 ltr l atr a btr b; ()

#set-options "--z3rlimit 10000"
val lemma21 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> aa:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                              pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                              (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall a. mem a ltr.l /\ opa a ==> (forall r. mem r (abs_merge ltr atr btr).l /\ 
                               opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                               not ((abs_merge ltr atr btr).vis a r)) ==> member_ele_s (get_ele a) (merge l aa b)))

#set-options "--z3rlimit 100000"
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
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                              pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                              (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall a. mem a atr.l /\ opa a ==> (forall r. mem r (abs_merge ltr atr btr).l /\ 
                                 opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> 
                                 not ((abs_merge ltr atr btr).vis a r)) ==> member_ele_s (get_ele a) (merge l aa b)))

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
  assert (forall a. mem a atr.l /\ opa a ==> (forall r. mem r (abs_merge ltr atr btr).l /\ 
         opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((abs_merge ltr atr btr).vis a r))
                  ==> member_ele_s (get_ele a) aa);
  assert (forall a. mem a atr.l /\ opa a ==> (forall r. mem r (abs_merge ltr atr btr).l /\ 
         opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((abs_merge ltr atr btr).vis a r)) 
                                     ==> not (mem (get_id a, get_ele a) l)); 
  ()

val lemma23 : ltr:ae op
            -> l:s 
            -> atr:ae op
            -> aa:s 
            -> btr:ae op
            -> b:s 
            -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                              (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                              (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                              pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                              (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                    (ensures (forall a. mem a btr.l /\ opa a ==> (forall r. mem r (abs_merge ltr atr btr).l /\ 
           opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((abs_merge ltr atr btr).vis a r)) 
                                        ==> member_ele_s (get_ele a) (merge l aa b)))

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
  assert (forall a. mem a btr.l /\ opa a ==> (forall r. mem r (abs_merge ltr atr btr).l /\ 
        opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((abs_merge ltr atr btr).vis a r)) 
                               ==> member_ele_s (get_ele a) b);
  assert (forall a. mem a btr.l /\ opa a ==> (forall r. mem r (abs_merge ltr atr btr).l /\ 
      opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((abs_merge ltr atr btr).vis a r)) 
                               ==> not (mem (get_id a, get_ele a) l)); 
  ()

val lemma2 : ltr:ae op
           -> l:s 
           -> atr:ae op
           -> aa:s 
           -> btr:ae op
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (mem_id (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (mem_id (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) aa /\ sim (union ltr btr) b) /\
                             pre_cond_merge l aa b /\ pre_cond_prop_merge ltr l atr aa btr b /\
                             (forall e. member_id_s e (diff aa l) ==> not (member_id_s e (diff b l))))
                   (ensures (forall a. mem a (abs_merge ltr atr btr).l /\ opa a ==> 
                               (forall r. mem r (abs_merge ltr atr btr).l /\ 
         opr r /\ get_ele a = get_ele r /\ get_id a <> get_id r ==> not ((abs_merge ltr atr btr).vis a r)) 
                                     ==> member_ele_s (get_ele a) (merge l aa b)))

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
                       (ensures  (pre_cond_merge l a b) /\ (sim (abs_merge ltr atr btr) (merge l a b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma6 ltr l atr a btr b;
  lemma2 ltr l atr a btr b;
  lemma3 ltr l atr a btr b;
  lemma4 ltr l atr a btr b;
  ()

val prop_spec : tr:ae op
                -> st:s
                -> op:(nat * op)
                -> Lemma (requires (sim tr st) /\ (not (mem_id (get_id op) tr.l)) /\
                                   (forall e. mem e tr.l ==> get_id e < get_id op) /\ get_id op > 0)
                         (ensures (get_op op = Rd ==> (forall e. mem e (extract (get_rval (do st op))) <==>
                                                  mem e (extract (spec op tr)))) /\
                                  (get_op op <> Rd ==> (get_rval (do st op) = spec op tr)))
#set-options "--z3rlimit 1000000"
let prop_spec tr st op = ()

instance orset_space : mrdt s op rval = {
  Library.init = init;
  Library.spec = spec;
  Library.sim = sim;
  Library.pre_cond_do = pre_cond_do;
  Library.pre_cond_prop_do = pre_cond_prop_do;
  Library.pre_cond_merge = pre_cond_merge;
  Library.pre_cond_prop_merge = pre_cond_prop_merge;
  Library.do = do;
  Library.merge = merge;
  Library.prop_do = prop_do;
  Library.prop_merge = prop_merge;
  Library.prop_spec = prop_spec;
  Library.convergence = convergence
}

