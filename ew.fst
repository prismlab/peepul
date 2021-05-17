module Ew

open FStar.List.Tot

type op =
    | Enable
    | Disable

type o = (nat (*unique id*) * op)

type s = nat * bool
     
val app_op : s -> o -> s
let app_op (c,f) e = 
  match e with
  |(_,Enable) -> (c + 1, true)
  |(_,Disable) -> (c, false)
  
val member : id:nat 
           -> l:list o
           -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})
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

noeq type ae  =
     |A : vis : (o -> o -> Tot bool)
        -> l:(list o) {(forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l /\ vis e e' /\ vis e' e'') ==> vis e e'') (*transitive*)/\ 
                      (forall e e'. (mem e l /\ mem e' l /\ vis e e') ==> not (vis e' e)) (*asymmetric*) /\
                      (forall e. mem e l ==> not (vis e e) (*irreflexive*) /\
                      (unique l))}  
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

val sum : l:(list o) -> Tot nat (decreases %[l])
let rec sum l =
  match l with
  |[] -> 0
  |(_,Enable)::xs -> 1 + sum xs
  |(_,Disable)::xs -> sum xs

val flag : l:ae -> bool
let flag tr = if ((forallb (fun e -> (existsb (fun d -> (snd d = Disable) && tr.vis e d) tr.l))
                                  (filter (fun e -> (snd e = Enable)) tr.l))
                  || (forallb (fun d -> (snd d = Disable)) tr.l) || (tr.l = [])) then false else true

#set-options "--query_stats"              
val sim : tr:ae
        -> s1:s 
        -> Tot (bool)           
let sim tr s1 = 
      let c = sum tr.l in
      let f = flag tr in
      s1 = (c,f)

val rem1 : l:ae 
         -> op:o
         -> Pure (list o)
           (requires true)
           (ensures (fun r -> (((snd op = Enable) /\ mem op l.l) ==> sum r = sum l.l - 1) /\
                           (((snd op = Disable) /\ mem op l.l) ==> sum r = sum l.l) /\
                           (forall e. mem e r ==> mem e l.l) /\ (unique r))) (decreases %[l.l])
let rec rem1 l op =
    match l with 
    |(A _ []) -> []
    |(A _ (x::xs)) -> if (x = op) then xs else (x::(rem1 (A l.vis xs) op))
          
val rem : l:ae 
        -> op:o
        -> Pure ae
          (requires true)
          (ensures (fun r -> (((snd op = Enable) /\ mem op l.l) ==> sum r.l = sum l.l - 1) /\
                          (((snd op = Disable) /\ mem op l.l) ==> sum r.l = sum l.l) /\
                          (forall e. mem e r.l ==> mem e l.l) /\
                          (forall e e1. mem e r.l /\ mem e1 r.l /\ r.vis e e1 ==> mem e l.l /\ mem e1 l.l /\ l.vis e e1) /\
                          (forall e e1. (mem e r.l /\ mem e1 r.l /\ not (r.vis e e1)) ==> (mem e l.l /\ mem e1 l.l /\ not (l.vis e e1))) /\
                          (forall e e1. (mem e r.l /\ mem e1 r.l /\ not (r.vis e e1 || r.vis e1 e)) ==> 
                                   (mem e l.l /\ mem e1 l.l /\ not (l.vis e e1 || l.vis e1 e)))))
let rem l op =
  let res = (rem1 l op) in
  (A (fun o o1 -> mem o l.l && mem o1 l.l && l.vis o o1) res)

val diff1 : a:ae
          -> l:ae
          -> Pure (list o)
            (requires (forall e. mem e l.l ==> mem e a.l) /\ 
                      (forall e e1. mem e l.l /\ mem e1 l.l /\ l.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                      (forall e e1. (mem e l.l /\ mem e1 a.l ==> mem e a.l /\ a.vis e e1)))
            (ensures (fun d -> (forall e. mem e d <==> mem e a.l /\ not (mem e l.l)) /\
                            (sum d = sum a.l - sum l.l) /\
                            (forall e. mem e d ==> not (member (fst e) l.l)))) (decreases %[l.l;a.l])
let rec diff1 a l = 
    match a,l with
    |_,(A _ []) -> a.l
    |_,(A _ (x::xs)) -> if (mem x a.l) then (diff1 (rem a x) (A l.vis xs)) else (diff1 a (A l.vis xs))

val diff : a:ae
         -> l:ae
         -> Pure ae
          (requires (forall e. mem e l.l ==> mem e a.l) /\ 
                    (forall e e1. mem e l.l /\ mem e1 l.l /\ l.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                    (forall e e1. (mem e l.l /\ mem e1 a.l ==> mem e a.l /\ a.vis e e1)))
          (ensures (fun d -> (forall e. mem e d.l <==> mem e a.l /\ not(mem e l.l)) /\
                          (sum d.l = sum a.l - sum l.l) /\
                          (forall e. mem e d.l ==> not (member (fst e) l.l)) /\
                          (forall e e1. mem e d.l /\ mem e1 d.l /\ d.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1)) ==> (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1))) /\
                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1 || d.vis e1 e)) ==>
                                   (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e))))) (decreases l)
let diff a l =
  (A (fun o o1 -> mem o a.l && mem o1 a.l && a.vis o o1) (diff1 a l))

val union1 : a:ae 
           -> b:ae
           -> Pure (list o)
             (requires (forall e. (mem e a.l ==> not (member (fst e) b.l))) /\
                             (forall e. (mem e b.l ==> not (member (fst e) a.l))))
             (ensures (fun u -> (sum u = sum a.l + sum b.l) /\ 
                             (forall e. mem e u <==> mem e a.l \/ mem e b.l) /\
                             (unique u)))     (decreases %[a.l;b.l])        
let rec union1 a b =
  match a,b with
  |(A _ []),(A _ []) -> []
  |(A _ (x::xs)),_ -> x::(union1 (A (fun o o1 -> mem o a.l && mem o1 a.l && a.vis o o1) xs) b)
  |(A _ []), (A _ (x::xs)) -> x::(union1 a (A (fun o o1 -> mem o b.l && mem o1 b.l && b.vis o o1) xs))

val union : a:ae 
          -> b:ae
          -> Pure ae
            (requires (forall e. (mem e a.l ==> not (member (fst e) b.l))) /\
                            (forall e. (mem e b.l ==> not (member (fst e) a.l))))
            (ensures (fun u -> (sum u.l = sum a.l + sum b.l) /\ 
                            (forall e. mem e u.l <==> mem e a.l \/ mem e b.l) /\
                            (forall e e1. (mem e u.l /\ mem e1 u.l /\ u.vis e e1) <==> 
                                     ((mem e a.l /\ mem e1 a.l /\ a.vis e e1) \/ (mem e b.l /\ mem e1 b.l /\ b.vis e e1))) /\
                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e) ==> 
                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1 || b.vis e1 e) ==> 
                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e))))
let union a b = 
  (A (fun o o1 -> (mem o a.l && mem o1 a.l && a.vis o o1) || (mem o b.l && mem o1 b.l && b.vis o o1)) (union1 a b))
  
val absmerge : l:ae
             -> a:ae
             -> b:ae
             -> Pure ae 
               (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                         (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> 
                                   mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\ mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                         (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                         (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                         (forall e. mem e (diff a l).l ==> not (member (fst e) b.l)) /\
                         (forall e1. mem e1 (diff b l).l ==> not (member (fst e1) a.l)))  
                (ensures (fun u ->(forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\ 
                               (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ u.vis e1 e2) <==> 
                                         (mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2) \/
                                         (mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2) \/ 
                                         (mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2)) /\ 
                              (forall e e1. mem e l.l /\ mem e1 l.l /\ not (l.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
                              (forall e e1. mem e l.l /\ mem e1 l.l /\ not (l.vis e e1 || l.vis e1 e) ==> 
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                              (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e) ==>
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
                              (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1 || b.vis e1 e) ==> 
                                       mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e))))
                                       
let absmerge l a b = 
    let la = diff a l in
    let lb = diff b l in
    let u1 = union la lb in
    let res = union l u1 in
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && l.vis o o1) || 
                 (mem o a.l && mem o1 a.l && a.vis o o1) || 
                 (mem o b.l && mem o1 b.l && b.vis o o1)) res.l)

val help1 : tr:ae 
          -> Lemma (ensures (not (forallb (fun e -> (existsb (fun d -> (snd d = Disable) && tr.vis e d)) tr.l)
                                                (filter (fun e -> (snd e = Enable)) tr.l))
                                && not (forallb (fun d -> (snd d = Disable)) tr.l) && (tr.l <> [])) <==>                          
                           (exists e. (mem e tr.l /\ snd e = Enable /\
                           (forall d. (mem d tr.l /\ snd d = Disable) ==> mem e tr.l /\ mem d tr.l /\ not (tr.vis e d)))) /\ tr.l <> []) (decreases tr.l)
let rec help1 tr = 
  match tr with
  |(A _ []) -> ()
  |(A _ (x::xs)) -> help1 (A tr.vis xs)

val help2 : tr:ae 
          -> Lemma (ensures (flag tr = false) <==>
                           ((forall e. (mem e tr.l /\ snd e = Enable) ==>  
                            (exists d. mem d tr.l /\ snd d = Disable /\ mem e tr.l /\ mem d tr.l /\ tr.vis e d)) \/ tr.l = [] \/
                            (forall d. mem d tr.l ==> snd d = Disable)))  (decreases tr.l) 
let help2 tr = ()

val help3 : tr:ae 
          -> Lemma (ensures (flag tr = true) <==> 
                           (exists e. (mem e tr.l /\ snd e = Enable /\
                           (forall d. (mem d tr.l /\ snd d = Disable) ==> mem e tr.l /\ mem d tr.l /\ not (tr.vis e d)))))
let help3 tr = help1 tr; ()

val help4 : l:ae 
          -> a:ae 
          -> Lemma (requires (forall e. mem e l.l ==> mem e a.l) /\ 
                            (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 ==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2) /\
                            (forall e e1. mem e l.l /\ mem e1 a.l  ==> mem e a.l /\ a.vis e e1))                                   
                            (ensures ((sum a.l = sum l.l) /\ (flag a = true) ==> ((diff a l).l = []))) (decreases %[l.l;a.l])
let rec help4 l a = 
  match l,a with
  |(A _ []),(A _ []) -> ()
  |(A _ (x::xs)),_ -> help4 (A l.vis xs) a
  |(A _ []),(A _ (x::xs)) -> help4 l (A a.vis xs)

val help5 : l:ae 
          -> a:ae
          -> b:ae 
          -> Lemma (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                            (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\
                                      mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                            (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                            (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                            (forall e e1. mem e (diff a l).l /\ mem e1 (diff b l).l ==>
                                     not (member (fst e) b.l) /\ not (member (fst e1) a.l)))
                  (ensures ((sum a.l = sum l.l) /\ (flag a = true) /\ (flag b = false)) ==> ((diff a l).l = []))
let help5 l a b =  help4 l a; ()

val lemma1 : l:ae 
           -> a:ae
           -> b:ae 
           -> Lemma (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                             (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\
                                       mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                             (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                             (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                             (forall e e1. mem e (diff a l).l /\ mem e1 (diff b l).l ==>
                                      not (member (fst e) b.l) /\ not (member (fst e1) a.l)))
                   (ensures ((flag b = true) /\ (flag a = true) ==> (flag (absmerge l a b) = true)))                  
let  lemma1 l a b = 
  help3 a;
  help3 b;
  help3 (absmerge l a b); ()

val lemma2 : l:ae 
           -> a:ae
           -> b:ae 
           -> Lemma (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                             (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\
                                       mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                             (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                             (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                             (forall e e1. mem e (diff a l).l /\ mem e1 (diff b l).l ==>
                                      not (member (fst e) b.l) /\ not (member (fst e1) a.l)))
                   (ensures (flag a = false /\ flag b = false) ==> flag (absmerge l a b) = false)
let  lemma2 l a b = 
  help2 a;
  help2 b;
  help2 (absmerge l a b); ()

val lemma3 : l:ae 
           -> a:ae
           -> b:ae 
           -> Lemma (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                             (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\
                                       mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                             (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                             (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                             (forall e e1. mem e (diff a l).l /\ mem e1 (diff b l).l ==>
                                      not (member (fst e) b.l) /\ not (member (fst e1) a.l)))
                   (ensures ((sum a.l - sum l.l > 0) /\  (flag a = true) /\ (flag b = false)) ==> (flag (absmerge l a b) = true))
let  lemma3 l a b =
  help3 a;
  help3 b;
  help3 (absmerge l a b); ()

val lemma4 : l:ae 
           -> a:ae
           -> b:ae 
           -> Lemma (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                             (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\
                                       mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                             (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                             (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                             (forall e e1. mem e (diff a l).l /\ mem e1 (diff b l).l ==>
                                      not (member (fst e) b.l) /\ not (member (fst e1) a.l)))
                   (ensures ((sum a.l = sum l.l) /\ (flag a = true) /\ (flag b = false)) ==> (flag (absmerge l a b) = false))
let lemma4 l a b = help5 l a b; ()

val lemma5 : l:ae 
           -> a:ae 
           -> b:ae 
           -> Lemma (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                             (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\
                                       mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                             (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                             (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                             (forall e e1. mem e (diff a l).l /\ mem e1 (diff b l).l ==>
                                      not (member (fst e) b.l) /\ not (member (fst e1) a.l)))
                   (ensures ((sum b.l - sum l.l > 0) /\ (flag b = true) /\ (flag a = false)) ==> (flag (absmerge l a b) = true))
let lemma5 l a b =
  help3 a;
  help3 b; 
  help3 (absmerge l a b); ()

val lemma6 : l:ae
           -> a:ae
           -> b:ae 
           -> Lemma (requires (forall e. mem e l.l <==> mem e a.l /\ mem e b.l) /\ 
                             (forall e1 e2. mem e1 l.l /\ mem e2 l.l /\ l.vis e1 e2 <==> mem e1 a.l /\ mem e2 a.l /\ a.vis e1 e2 /\
                                       mem e1 b.l /\ mem e2 b.l /\ b.vis e1 e2) /\
                             (forall e e1. mem e l.l /\ mem e1 a.l ==> a.vis e e1) /\
                             (forall e e1. mem e l.l /\ mem e1 b.l ==> b.vis e e1) /\
                             (forall e e1. mem e (diff a l).l /\ mem e1 (diff b l).l ==>
                                      not (member (fst e) b.l) /\ not (member (fst e1) a.l)))
                   (ensures ((sum b.l = sum l.l) /\ (flag b = true) /\ (flag a = false)) ==> (flag (absmerge l a b) = false))
let lemma6 l a b = help5 l b a; ()

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
    
val merge : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s 
          -> btr:ae
          -> b:s 
          -> Pure s (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                             (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                             (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                             (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                             (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                       (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                        mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                             (forall e e1. mem e (diff atr ltr).l /\ mem e1 (diff btr ltr).l ==> 
                                      not (member (fst e) btr.l) /\ not (member (fst e1) atr.l)))                
                   (ensures (fun res -> true))                  
let merge ltr l atr a btr b = 
    let c = fst a + fst b - fst l in
    let f = merge_flag l a b in
    c, f

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (not (member (fst op) tr.l)))
             (ensures (fun res -> true)) (decreases tr.l)               
let append tr op =
    match tr with
    |(A _ []) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::[]))
    |(A _ (x::xs)) -> (A (fun o o1 -> mem o tr.l && mem o1 tr.l && tr.vis o o1) (op::(x::xs)))

val prop_merge : ltr: ae
               -> l:s 
               -> atr:ae
               -> a:s 
               -> btr:ae
               -> b:s 
               -> Lemma (requires (sim ltr l /\ sim atr a /\ sim btr b) /\ 
                                 (forall e. mem e ltr.l <==> mem e atr.l /\ mem e btr.l) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 atr.l ==> mem e atr.l /\ atr.vis e e1) /\
                                 (forall e e1. mem e ltr.l /\ mem e1 btr.l ==>  mem e btr.l /\ btr.vis e e1) /\
                                 (forall e1 e2. (mem e1 ltr.l /\ mem e2 ltr.l /\ ltr.vis e1 e2) <==> 
                                           (mem e1 atr.l /\ mem e2 atr.l /\ atr.vis e1 e2 /\ 
                                           mem e1 btr.l /\ mem e2 btr.l /\ btr.vis e1 e2)) /\
                                 (forall e e1. mem e (diff atr ltr).l /\ mem e1 (diff btr ltr).l ==> 
                                          not (member (fst e) btr.l) /\ not (member (fst e1) atr.l)))                        
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b))) 

#set-options "--z3rlimit 100"                                          
let prop_merge ltr l atr a btr b = 
lemma1 ltr atr btr;
lemma2 ltr atr btr;
lemma3 ltr atr btr;
lemma4 ltr atr btr;
lemma5 ltr atr btr;
lemma6 ltr atr btr; ()

val prop_oper : tr:ae
              -> st:s
              -> op:o 
              -> Lemma (requires (sim tr st) /\ 
                                (not (member (fst op) tr.l)) /\ 
                                (forall e. mem e tr.l ==> (append tr op).vis e op))
                      (ensures (sim (append tr op) (app_op st op))) (decreases %[tr.l])
let prop_oper tr st op = ()
          
val convergence : tr:ae
                -> a:s 
                -> b:s 
                -> Lemma (ensures (sim tr a /\ sim tr b) ==> a = b)                      
let convergence tr a b = ()

