module Ew_correct_sim1

open FStar.List.Tot

type op =
  |Enable
  |Disable

type o = (nat (*unique id*) * op)

let get_id (id,_) = id
let get_op (_,op) = op

type s = nat * bool

val app_op : s -> o -> s
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
|A : vis:(o -> o -> Tot bool) -> l:list o {unique l} -> ae

assume val axiom : l:ae
                 -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\ 
                         get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*)/\ 
                         (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                         (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*)))
                         [SMTPat (unique l.l)]

(*)noeq type ae  =
       |A : vis : (o -> o -> Tot bool)
         -> l:(list o) {(unique l) /\
                       (forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ get_id e <> get_id e' /\ get_id e' <> get_id e'' /\ get_id e <> get_id e''  /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\ 
                       (forall e e'. (mem e l /\ mem e' l /\ get_id e <> get_id e' /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                       (forall e. mem e l ==> not (vis e e) (*irreflexive*))}  
         -> ae*)

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

val sum : l:(list o) -> Tot nat (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_,Enable)::xs -> 1 + sum xs
  |(_,Disable)::xs -> sum xs

val flag : tr:ae
         -> Tot (b:bool{(b = false <==> ((forall e. (mem e tr.l /\ get_op e = Enable ==> (exists d. mem d tr.l /\ get_op d = Disable /\
                                      get_id e <> get_id d /\ tr.vis e d))) \/ 
                                      (forall d. mem d tr.l ==> get_op d = Disable)) \/ tr.l = [])})

let flag tr = if ((forallb (fun e -> (existsb (fun d -> (get_op d = Disable) && get_id e <> get_id d && tr.vis e d) tr.l))
                                  (filter (fun e -> (get_op e = Enable)) tr.l))
               || (forallb (fun d -> (get_op d = Disable)) tr.l) || tr.l = []) then false else true

#set-options "--query_stats"
val sim : s0:s
        -> tr:ae
        -> s1:s
        -> Tot (b:bool {b = true <==> (((fst s0 + sum tr.l) = fst s1) /\
                                    ((flag tr = true \/ (snd s0 = true /\ tr.l = [] /\ fst s0 = fst s1)) <==> (snd s1 = true)) /\
                                    ((fst s0 = fst s1 /\ snd s1 = true) ==> tr.l = []))})

let sim s0 tr s1 =
    let c = fst s0 + sum tr.l in
    fst s1 = fst s0 + sum tr.l && 
    (if (flag tr = true || (tr.l = [] && snd s0 = true && fst s0 = c)) then (snd s1 = true) else true) &&
    (if (snd s1 = true) then (flag tr = true || (tr.l = [] && snd s0 = true && fst s0 = c)) else true) &&
    (if (fst s0 = c && flag tr = true) then (tr.l = []) else true)

val absmerge1 : l:ae
              -> a:ae 
              -> b:ae
              -> Pure (list o)
                (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                          (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                          (forall e. mem e b.l ==> not (member (get_id e) l.l)))
                (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique u)))
                (decreases %[l.l;a.l;b.l])
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
                         (forall e. mem e b.l ==> not (member (get_id e) l.l)))
                (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                                (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2) <==> 
                                          (mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                          (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/ 
                                          (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) \/
                                          (mem e1 l.l /\ mem e2 a.l /\ get_id e1 <> get_id e2) \/
                                          (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2))))

let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && get_id o <> get_id o1 && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && get_id o <> get_id o1 && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && get_id o <> get_id o1 && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && get_id o <> get_id o1) || 
                 (mem o l.l && mem o1 b.l && get_id o <> get_id o1)) (absmerge1 l a b))

val lemma1 : l:ae
           -> a:ae
           -> b:ae
           -> Lemma
             (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                       (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                       (forall e. mem e b.l ==> not (member (get_id e) l.l)))
             (ensures (forall e. mem e (absmerge1 l a b) <==> mem e l.l \/ mem e a.l \/ mem e b.l)  /\
                      (sum (absmerge1 l a b) = sum a.l + sum b.l + sum l.l))
             (decreases %[l.l;a.l;b.l])

let rec lemma1 l a b =
  match l,a,b with
  |(A _ []), (A _ []), (A _ []) -> ()
  |(A _ (x::xs)), _, _ -> lemma1 (A l.vis xs) a b
  |(A _ []), (A _ (x::xs)), _ -> lemma1 l (A a.vis xs) b
  |(A _ []), (A _ []), (A _ (x::xs)) -> lemma1 l a (A b.vis xs)
  
val lemma2 : l:ae
           -> a:ae
           -> b:ae
           -> Lemma (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                             (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                             (forall e. mem e b.l ==> not (member (get_id e) l.l)))
                   (ensures (sum (absmerge l a b).l = sum a.l + sum b.l + sum l.l))
let rec lemma2 l a b =
  lemma1 l a b

val merge_flag : l:s 
               -> a:s{fst a >= fst l}
               -> b:s{fst b >= fst l}
               -> bool
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

val merge : s0:s
          -> ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (sim s0 ltr l /\ sim l atr a /\ sim l btr b) /\ 
                             (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e btr.l ==> not (member (get_id e) ltr.l)))
                   (ensures (fun res -> true))   
let merge s0 ltr l atr a btr b = 
    let c = fst a + fst b - fst l in
    let f = merge_flag l a b in
    c, f

val prop_merge : s0:s
               -> ltr:ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (sim s0 ltr l /\ sim l atr a /\ sim l btr b) /\ 
                                 (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e btr.l ==> not (member (get_id e) ltr.l)))
                       (ensures (sim s0 (absmerge ltr atr btr) (merge s0 ltr l atr a btr b)))

#set-options "--z3rlimit 100"
let prop_merge s0 ltr l atr a btr b = 
  assert (fst s0 <= fst (merge s0 ltr l atr a btr b));
  lemma2 ltr atr btr;
  assert (fst (merge s0 ltr l atr a btr b) = fst s0 + sum (absmerge ltr atr btr).l); 
  assert ((fst s0 = fst (merge s0 ltr l atr a btr b) /\ snd (merge s0 ltr l atr a btr b)  = true) ==>
         (absmerge ltr atr btr).l = []);
  assert ((flag (absmerge ltr atr btr) = true \/ (snd s0 = true /\ (absmerge ltr atr btr).l = [] /\
         fst s0 = fst (merge s0 ltr l atr a btr b))) <==> (snd (merge s0 ltr l atr a btr b) = true));
  ()
(*25992 ms*)

val append1 : tr:ae
            -> op:o
            -> Pure (list o)
              (requires (not (member (get_id op) tr.l)))
              (ensures (fun res -> (forall e. mem e res <==> mem e tr.l \/ e = op)))
let append1 tr op = (op::tr.l)

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member (get_id op) tr.l)))
             (ensures (fun res -> (forall e. mem e res.l <==> mem e tr.l \/ e = op) /\
                               (forall e1 e2. (mem e1 res.l /\ mem e2 res.l /\ get_id e1 <> get_id e2 /\ res.vis e1 e2) <==> 
                                         (mem e1 tr.l /\ mem e2 tr.l /\ get_id e1 <> get_id e2 /\ tr.vis e1 e2) \/
                                         (mem e1 tr.l /\ e2 = op /\ get_id e1 <> get_id e2))))
let append tr op =
    (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && get_id o <> get_id o1 && tr.vis o o1) ||
                 (mem o tr.l && o1 = op && get_id o <> get_id op)) (append1 tr op))

val prop_oper : s0:s
              -> tr:ae
              -> st:s
              -> op:o 
              -> Lemma (requires (sim s0 tr st) /\ 
                                (not (member (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> mem op (append tr op).l /\ (append tr op).vis e op))
                      (ensures (sim s0 (append tr op) (app_op st op)))
let prop_oper s0 tr st op = ()

val convergence : s0:s
                -> tr:ae
                -> a:s
                -> b:s  
                -> Lemma (requires (sim s0 tr a /\ sim s0 tr b))
                        (ensures (a = b))
let convergence s0 tr a b = ()
