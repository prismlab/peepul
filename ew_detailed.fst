module Ew_detailed

open FStar.List.Tot

type op =
  |Enable
  |Disable

type o = (nat (*unique id*) * op)

let get_id (id,_) = id
let get_op (_,op) = op

type s = nat * bool

val app_op : s1:s -> op:o -> Tot (s2:s {(fst s2 > fst s1 ==> get_op op = Enable) /\
                                      (fst s1 = fst s2 ==> get_op op = Disable)})
let app_op (c,f) e = 
  match e with
  |(_,Enable) -> (c + 1, true)
  |(_,Disable) -> (c, false)

val member : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists op. mem (id,op) l) <==> b=true})
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
  |A : vis : (o -> o -> Tot bool)
     -> l:(list o) {(unique l) /\
                   (forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ get_id e <> get_id e' /\ get_id e' <> get_id e'' /\ get_id e <> get_id e''  /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\ 
                   (forall e e'. (mem e l /\ mem e' l /\ get_id e <> get_id e' /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                   (forall e. mem e l ==> not (vis e e) (*irreflexive*))}  
     -> ae

val forallb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a
            -> Tot(b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forallb #a f l =
  match l with
  |[] -> true
  |hd::tl -> if f hd then forallb f tl else false

val existsb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a 
            -> Tot (b:bool{(exists e. mem e l /\ f e) <==> b = true})
let rec existsb #a f l =
  match l with
  |[] -> false
  |hd::tl -> if f hd then true else existsb f tl

val filter : #a:eqtype
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ f e})
let rec filter #a f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

val sum : l:(list o)
        -> Tot nat (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_,Enable)::xs -> 1 + sum xs
  |(_,Disable)::xs -> sum xs

val flag : tr:ae 
         -> Tot (b:bool {((b = true) <==> ((exists e. (mem e tr.l /\ get_op e = Enable /\ 
                                       (forall d. (mem d tr.l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not (tr.vis e d)))))) /\
                       ((b = false) <==> ((forall e. (mem e tr.l /\ get_op e = Enable ==> 
                                        (exists d. mem d tr.l /\ get_id e <> get_id d /\ get_op d = Disable /\ tr.vis e d))) \/ (forall d. mem d tr.l ==> get_op d = Disable) \/ tr.l = []))})

let flag tr = if ((forallb (fun e -> (existsb (fun d -> (get_op d = Disable) && get_id e <> get_id d && tr.vis e d) tr.l))
                                  (filter (fun e -> (get_op e = Enable)) tr.l))
                 || (forallb (fun d -> (get_op d = Disable)) tr.l)
                 || tr.l = []) then false else true

#set-options "--query_stats"
val sim : tr:ae
        -> s1:s
        -> Tot (b:bool {b = true <==> ((fst s1 = sum tr.l) /\ (snd s1 = flag tr))})                  
let sim tr s1 = (s1 = (sum tr.l, flag tr))

val union1 : l:ae 
           -> a:ae
           -> Pure (list o)
             (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ (unique u))) (decreases %[l.l;a.l])
let rec union1 l a =
  match l,a with
  |(A _ []), (A _ []) -> []
  |(A _ (x::xs)), _ -> x::(union1 (A l.vis xs) a)
  |(A _ []), (A _ (x::xs)) -> x::(union1 l (A a.vis xs))

val union : l:ae 
          -> a:ae
          -> Pure ae
            (requires (forall e. (mem e l.l ==> not (member (get_id e) a.l))))
            (ensures (fun u -> (forall e e1. (mem e u.l /\ mem e1 u.l /\ get_id e <> get_id e1 /\ u.vis e e1) <==>
                                     (mem e l.l /\ mem e1 l.l /\ get_id e <> get_id e1 /\ l.vis e e1) \/
                                     (mem e a.l /\ mem e1 a.l /\ get_id e <> get_id e1 /\ a.vis e e1) \/
                                     (mem e l.l /\ mem e1 a.l /\ get_id e <> get_id e1)))) 
let union l a =
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1)) (union1 l a))

val absmerge1 : l:ae
              -> a:ae 
              -> b:ae
              -> Pure (list o)
                (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                          (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                          (forall e. mem e l.l ==> not (member (get_id e) b.l)))
                (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique u))) (decreases %[l.l;a.l;b.l])
let rec absmerge1 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> []
  |(A _ (x::xs)), _, _ -> x::(absmerge1 (A l.vis xs) a b)
  |(A _ []), (A _ (x::xs)), _ -> x::(absmerge1 l (A a.vis xs) b)
  |(A _ []), (A _ []), (A _ (x::xs)) -> x::(absmerge1 l a (A b.vis xs))

val absmerge : l:ae
             -> a:ae
             -> b:ae
             -> Pure ae 
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                         (forall e. mem e l.l ==> not (member (get_id e) b.l)))  
               (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                               (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2) <==> 
                                         (mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/ 
                                         (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ (union l a).vis e1 e2) \/
                                         (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ (union l b).vis e1 e2))))
#set-options "--z3rlimit 10000"
let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1 && (union l a).vis o o1) || 
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1 && (union l b).vis o o1)) (absmerge1 l a b))

val lemma1 : l:ae
           -> a:ae
           -> b:ae
           -> Lemma
             (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                       (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                       (forall e. mem e l.l ==> not (member (get_id e) b.l)))
             (ensures (forall e. mem e (absmerge1 l a b) <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                      (sum (absmerge1 l a b) = sum a.l + sum b.l + sum l.l) /\
                      (sum (absmerge l a b).l = sum a.l + sum b.l + sum l.l)) (decreases %[l.l;a.l;b.l])
let rec lemma1 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma1 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma1 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma1 l a (A b.vis xs)
  
val lemma3 : l:ae
           -> a:ae
           -> Lemma
             (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)))
             (ensures (forall e. mem e (union1 l a) <==> mem e l.l \/ mem e a.l) /\
                      (sum (union1 l a) = sum l.l + sum a.l) /\ (sum (union l a).l = sum l.l + sum a.l) /\
                      (sum a.l = sum (union1 l a) - sum l.l) /\ (sum a.l = sum (union l a).l - sum l.l) /\
                      (sum l.l = sum (union1 l a) - sum a.l) /\ (sum l.l = sum (union l a).l - sum a.l)) (decreases %[l.l;a.l])
let rec lemma3 l a =
  match l,a with
  |(A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _ -> lemma3 (A l.vis xs) a
  |(A _ []), (A _ (x::xs)) -> lemma3 l (A a.vis xs)

val lem_sum : l:list o 
            -> Lemma (requires (unique l))
                    (ensures (sum l > 0 <==> (exists e. mem e l /\ get_op e = Enable)) /\
                             (sum l = 0 <==> ((forall e. mem e l ==> get_op e = Disable /\ l <> []) \/ l = []))) (decreases l)
let rec lem_sum l = 
  match l with
  |[] -> ()
  |x::xs -> lem_sum xs

val merge_flag : l:s 
               -> a:s{fst a >= fst l}
               -> b:s{fst b >= fst l}
               -> Tot (b1:bool {(b1 = true <==> (snd a = true /\ snd b = true) \/ 
                                              (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                              (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                               (b1 = false <==> (snd a = false /\ snd b = false) \/ 
                                               (snd a = true /\ snd b = false /\ fst a = fst l) \/
                                               (snd b = true /\ snd a = false /\ fst b = fst l))}) 
let merge_flag l a b =
  let lc = fst l in
  let ac = fst a in
  let bc = fst b in
  let af = snd a in
  let bf = snd b in
  if af && bf then true
    else if not af && not bf then false
      else if af then ac - lc > 0
        else bc - lc > 0

val merge : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                    (ensures (fun res -> (snd res = true <==> (snd a = true /\ snd b = true) \/ 
                                                          (snd a = true /\ snd b = false /\ fst a > fst l) \/
                                                          (snd b = true /\ snd a = false /\ fst b > fst l)) /\
                                      (snd res = false <==> (snd a = false /\ snd b = false) \/
                                                          (snd a = true /\ snd b = false /\ fst a = fst l) \/ 
                                                          (snd b = true /\ snd a = false /\ fst b = fst l)))) 
#set-options "--z3rlimit 10000"
let merge ltr l atr a btr b = 
  lemma3 ltr atr; 
  lemma3 ltr btr;
  let c = fst a + fst b - fst l in
  let f = merge_flag l a b in
  c, f

val lemma4 : ltr: ae
           -> l:s 
           -> atr:ae
           -> a:s 
           -> btr:ae
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))

                   (ensures (flag (union ltr atr) = true /\ flag (union ltr btr) = false /\ sum (union ltr atr).l = sum ltr.l) ==> flag (absmerge ltr atr btr) = false)

#set-options "--z3rlimit 1000000"
let lemma4 ltr l atr a btr b = 
    lemma3 ltr atr;
    assert ((sum (union ltr atr).l = sum ltr.l + sum atr.l));
    assert (((sum (union ltr atr).l = sum ltr.l) ==> (sum ltr.l + sum atr.l = sum ltr.l)));
    assert ((sum (union ltr atr).l = sum ltr.l) ==> sum atr.l = 0);
    lem_sum atr.l;
    assert (sum atr.l = 0 <==> ((forall e. mem e atr.l ==> get_op e = Disable /\ atr.l <> []) \/ atr.l = []));
 
    assert ((forall e. mem e atr.l ==> get_op e = Disable) /\ atr.l <> [] ==> flag atr = false);
    assert ((forall e. mem e atr.l ==> get_op e = Disable) /\ atr.l <> [] /\ flag atr = false ==> flag (union ltr atr) = false);

    assert ((sum (union ltr atr).l = sum ltr.l /\ flag (union ltr atr) = true) ==> atr.l = []); 
    assert (atr.l = [] ==> (forall e. mem e (union ltr atr).l <==> mem e ltr.l)); 
    assert ((forall e. mem e (union ltr atr).l <==> mem e ltr.l) ==> (forall e. mem e (absmerge ltr atr btr).l <==> mem e (union ltr btr).l));
    assert ((forall e. mem e (absmerge ltr atr btr).l <==> mem e (union ltr btr).l) ==> (forall e. mem e (absmerge ltr atr btr).l <==> mem e (union ltr btr).l) /\ (forall e e1. mem e (absmerge ltr atr btr).l /\ mem e1 (absmerge ltr atr btr).l /\ get_id e <> get_id e1 /\ 
    (absmerge ltr atr btr).vis e e1 <==>  mem e (union ltr btr).l /\ mem e1 (union ltr btr).l /\ get_id e <> get_id e1 /\ (union ltr btr).vis e e1));

    assert ((flag (union ltr atr) = true /\ flag (union ltr btr) = false /\ sum (union ltr atr).l = sum ltr.l /\
             (forall e e1. mem e (absmerge ltr atr btr).l /\ mem e1 (absmerge ltr atr btr).l /\ get_id e <> get_id e1 /\ (absmerge ltr atr btr).vis e e1 <==>  mem e (union ltr btr).l /\ mem e1 (union ltr btr).l /\ get_id e <> get_id e1 /\ (union ltr btr).vis e e1)) ==> flag (absmerge ltr atr btr) = false);
    ()
(*42627 ms*)

val lemma5 : ltr: ae
           -> l:s 
           -> atr:ae
           -> a:s 
           -> btr:ae
           -> b:s 
           -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                             (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))

                   (ensures (flag (union ltr atr) = true /\ flag (union ltr btr) = false /\ sum (union ltr atr).l > sum ltr.l) ==> flag (absmerge ltr atr btr) = true)

#set-options "--z3rlimit 1000000"
let lemma5 ltr l atr a btr b = 
    lemma3 ltr atr;
    assert ((sum (union ltr atr).l = sum ltr.l + sum atr.l));
    assert (((sum (union ltr atr).l > sum ltr.l) ==> (sum ltr.l + sum atr.l > sum ltr.l)));
    assert ((sum (union ltr atr).l > sum ltr.l) ==> sum atr.l > 0);
    lem_sum atr.l;
    assert (sum atr.l > 0 <==> (exists e. mem e atr.l /\ get_op e = Enable));
<<<<<<< HEAD
    assert (((exists e. mem e atr.l /\ get_op e = Enable) /\ flag (union ltr atr) = true) ==> flag atr = true); 
    assert (flag atr = true ==> ((exists e. (mem e atr.l /\ get_op e = Enable /\ (forall d. (mem d atr.l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not (atr.vis e d))))));
    assert ((exists e. (mem e atr.l /\ get_op e = Enable /\ (forall d. (mem d atr.l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not (atr.vis e d)))) ==>
=======
    assert (((exists e. mem e atr.l /\ get_op e = Enable) /\ flag (union ltr atr) = true) ==> flag atr = true);
    assert (flag atr = true ==> ((exists e. (mem e atr.l /\ get_op e = Enable /\ (forall d. (mem d atr.l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not (atr.vis e d))))));
    assert ((exists e. (mem e atr.l /\ get_op e = Enable /\ (forall d. (mem d atr.l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not (atr.vis e d)))) ==> 
>>>>>>> 5ff2ca2 (More asserts to lemma5)
          (exists e. (mem e (absmerge ltr atr btr).l /\ get_op e = Enable /\ (forall d. (mem d (absmerge ltr atr btr).l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not ((absmerge ltr atr btr).vis e d)))));
    assert ((exists e. (mem e (absmerge ltr atr btr).l /\ get_op e = Enable /\ (forall d. (mem d (absmerge ltr atr btr).l /\ get_id e <> get_id d /\ get_op d = Disable) ==> not ((absmerge ltr atr btr).vis e d)))) ==>
           flag (absmerge ltr atr btr) = true);
    ()
(*23421 ms*)

val prop_merge : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) btr.l)) /\
                                (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))

#set-options "--z3rlimit 10000000"
let prop_merge ltr l atr a btr b = 
  lemma3 ltr atr; 
  lemma3 ltr btr;
  lemma1 ltr atr btr;
  lem_sum atr.l;
  lem_sum btr.l;
  assert (fst (merge ltr l atr a btr b) = sum (absmerge ltr atr btr).l);
  assert (snd (merge ltr l atr a btr b) = flag (absmerge ltr atr btr));
  ()
(*221678 ms*)

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

val prop_oper : tr:ae
              -> st:s
              -> op:o 
              -> Lemma (requires (sim tr st) /\ 
                                (not (member (get_id op) tr.l)))
                      (ensures (sim (append tr op) (app_op st op)))
let prop_oper tr st op = ()

val convergence : tr:ae
                -> a:s
                -> b:s  
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures a = b)
let convergence tr a b = ()


(*)val count : f:(o -> bool)
          -> l:list o
          -> Tot(n:nat {(n > 0 <==> (exists e. mem e l /\ f e)) /\
                     (n = 0 <==> (forall e. mem e l ==> not (f e)))} )
let rec count f l =
  match l with
  |[] -> 0
  |hd::tl -> if f hd then 1 + count f tl else count f tl 

val en : tr:ae 
       -> Tot (n:nat {(n > 0 <==> (exists e. mem e tr.l /\ get_op e = Enable /\ (forallb (fun d -> not (tr.vis e d)) 
                              (filter (fun d -> get_op d = Disable) tr.l)))) /\ 
                   (n = 0 <==> ((forall e. mem e tr.l /\ get_op e = Enable ==> (existsb (fun d -> (tr.vis e d)) (filter (fun d -> get_op d = Disable) tr.l))) \/ tr.l = [] \/ (forall e. mem e tr.l ==> get_op e = Disable)))})
let en tr =
    let lste = filter (fun e -> get_op e = Enable) tr.l in
    let lstd = filter (fun d -> get_op d = Disable) tr.l in
    let c = count (fun e -> forallb (fun d -> not (tr.vis e d)) lstd) lste in
    c

val en_flag : tr:ae 
         -> Lemma (ensures (en tr > 0 <==> flag tr = true /\ 
                           en tr = 0 <==> flag tr = false)) (decreases %[tr.l])
let rec en_flag tr = 
  match tr with
  |(A _ [])-> ()
  |(A _ (x::xs)) -> en_flag (A tr.vis xs)*)
  
