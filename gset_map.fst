module Gset_map

open FStar.List.Tot

module G = Gset

type o = (nat (*key*) * G.o)

val get_key : o -> nat
let get_key (k,_) = k

val get_gset : o -> G.o
let get_gset (_,op) = op

val member_k : k:nat
             -> l:list (nat * G.s)
             -> Tot (b:bool{(exists g. mem (k,g) l) <==> b=true})
let rec member_k n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member_k n xs

val unique_k : l:list (nat * G.s)
             -> Tot bool
let rec unique_k l =
  match l with
  |[] -> true
  |(id,x)::xs -> not (member_k id xs) && unique_k xs

type s = l:list (nat (*unique keys*) * G.s) {unique_k l}

val check : st:s -> Lemma (ensures (forall e. mem e st ==> G.unique_s (snd e)))
let check st = ()

val memkeyele : st:s
              -> k:nat
              -> e:nat
              -> Tot (b:bool {b = true <==> (exists e1. mem e1 st /\ fst e1 = k /\ mem e (snd e1))})
#set-options "--z3rlimit 1000"
let rec memkeyele st k e =
  match st with
  |[] -> false
  |(k1,x)::xs -> (k = k1 && mem e x) || memkeyele xs k e

val fst : (nat * G.s) -> nat
let fst (k,l) = k

val snd : (nat * G.s) -> G.s
let snd (k,l) = l

val member_id : id:nat
              -> l:list o
              -> Tot (b:bool{(exists k e. mem (k, (id, G.Add, e)) l) <==> b=true})
let rec member_id n l =
  match l with
  |[] -> false
  |(_,(id,G.Add,e))::xs -> (n = id) || member_id n xs

val unique_id : l:list o
              -> Tot bool
let rec unique_id l =
  match l with
  |[] -> true
  |(_,(id, G.Add, _))::xs -> not (member_id id xs) && unique_id xs

val memkeyele1 : tr:list o {unique_id tr}
               -> k:nat
               -> e:nat
               -> Tot (b:bool {b = true <==> (exists id. mem (k, (id, G.Add, e)) tr)})
let rec memkeyele1 st k e =
  match st with
  |[] -> false
  |(k1,(_,G.Add,e1))::xs -> (k = k1 && e = e1) || memkeyele1 xs k e

noeq type ae = 
  |A : vis:(o -> o -> Tot bool) -> l:list o {unique_id l} -> ae

assume val axiom1 : l:ae
                  -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ G.get_id (get_gset e) <> G.get_id (get_gset e') /\ G.get_id (get_gset e') <> G.get_id (get_gset e'') /\ G.get_id (get_gset e) <> G.get_id (get_gset e'') /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*) /\
                   (forall e e'. (mem e l.l /\ mem e' l.l /\ G.get_id (get_gset e) <> G.get_id (get_gset e') /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                   (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*)))

val forallb : #a:eqtype 
            -> f:(a -> bool)
            -> l:list a 
            -> Tot(b:bool{(forall e. mem e l ==> f e) <==> b = true})
let rec forallb #a f l =
  match l with
  |[] -> true
  |hd::tl -> if f hd then forallb f tl else false

#set-options "--query_stats"
val sim : tr:ae
        -> st:s
        -> Tot (b:bool {b = true <==> (forall k e. memkeyele st k e <==> memkeyele1 tr.l k e)})
let sim tr s1 =
    forallb (fun e -> memkeyele s1 (get_key e) (G.get_ele (get_gset e))) tr.l  &&
    forallb (fun e -> (forallb (fun l -> memkeyele1 tr.l (fst e) l) (snd e))) s1

val union1 : l:ae
           -> a:ae
           -> Pure (list o)
             (requires (forall e. (member_id e l.l ==> not (member_id e a.l))))
             (ensures (fun u -> (forall e. mem e u <==> mem e l.l \/ mem e a.l) /\ unique_id u /\
                             (forall id. member_id id u <==> member_id id l.l \/ member_id id a.l))) (decreases %[l.l;a.l])
#set-options "--z3rlimit 1000"
let rec union1 l a =
  match l,a with
  |(A _ []), (A _ []) -> []
  |(A _ (x::xs)), _ -> x::(union1 (A l.vis xs) a)
  |(A _ []), (A _ (x::xs)) -> x::(union1 l (A a.vis xs))

val union : l:ae
          -> a:ae
          -> Pure ae
            (requires (forall e. (member_id e l.l ==> not (member_id e a.l))))
            (ensures (fun u -> (forall e e1. (mem e u.l /\ mem e1 u.l /\ G.get_id (get_gset e) <> G.get_id (get_gset e1) /\ u.vis e e1) <==>
                                     (mem e l.l /\ mem e1 l.l /\ G.get_id (get_gset e) <> G.get_id (get_gset e1) /\ l.vis e e1) \/
                                     (mem e a.l /\ mem e1 a.l /\ G.get_id (get_gset e) <> G.get_id (get_gset e1) /\ a.vis e e1) \/
                                     (mem e l.l /\ mem e1 a.l /\ G.get_id (get_gset e) <> G.get_id (get_gset e1)))))
let union l a =
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && l.vis o o1) ||
                        (mem o a.l && mem o1 a.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && a.vis o o1) ||
                        (mem o l.l && mem o1 a.l && G.get_id (get_gset o) <> G.get_id (get_gset o1))) (union1 l a))

val absmerge1 : l:ae
              -> a:ae
              -> b:ae
              -> Pure (list o)
                (requires (forall e. mem e l.l ==> not (member_id (G.get_id (get_gset e)) a.l)) /\
                          (forall e. mem e a.l ==> not (member_id (G.get_id (get_gset e)) b.l)) /\
                          (forall e. mem e l.l ==> not (member_id (G.get_id (get_gset e)) b.l)))
                (ensures (fun u -> (forall e. mem e u <==> mem e a.l \/ mem e b.l \/ mem e l.l) /\ (unique_id u))) (decreases %[l.l;a.l;b.l])
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
               (requires (forall e. mem e l.l ==> not (member_id (G.get_id (get_gset e)) a.l)) /\
                         (forall e. mem e a.l ==> not (member_id (G.get_id (get_gset e)) b.l)) /\
                         (forall e. mem e l.l ==> not (member_id (G.get_id (get_gset e)) b.l)))
               (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                        (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ G.get_id (get_gset e1) <> G.get_id (get_gset e2) /\ u.vis e1 e2) <==>
                                  (mem e1 l.l /\ mem e2 l.l /\ G.get_id (get_gset e1) <> G.get_id (get_gset e2) /\ l.vis e1 e2) \/
                                  (mem e1 a.l /\ mem e2 a.l /\ G.get_id (get_gset e1) <> G.get_id (get_gset e2) /\ a.vis e1 e2) \/
                                  (mem e1 b.l /\ mem e2 b.l /\ G.get_id (get_gset e1) <> G.get_id (get_gset e2) /\ b.vis e1 e2) \/
                          (mem e1 l.l /\ mem e2 a.l /\ G.get_id (get_gset e1) <> G.get_id (get_gset e2) /\ (union l a).vis e1 e2) \/
                          (mem e1 l.l /\ mem e2 b.l /\ G.get_id (get_gset e1) <> G.get_id (get_gset e2) /\ (union l b).vis e1 e2))))
#set-options "--z3rlimit 10000"
let absmerge l a b = 
    (A (fun o o1 -> (mem o l.l && mem o1 l.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && l.vis o o1) ||
                 (mem o a.l && mem o1 a.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && a.vis o o1) ||
                 (mem o b.l && mem o1 b.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && b.vis o o1) ||
                 (mem o l.l && mem o1 a.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && (union l a).vis o o1) ||
                 (mem o l.l && mem o1 b.l && G.get_id (get_gset o) <> G.get_id (get_gset o1)) && (union l b).vis o o1) (absmerge1 l a b))

val findk : l:s
          -> k:nat
          -> Pure (list nat)
            (requires (member_k k l))
            (ensures (fun r -> G.unique_s r /\ mem (k,r) l /\ G.unique_s r /\
                            (forall e. mem e r <==> memkeyele l k e)))
let rec findk l k =
    match l with
    |(k1, x)::xs -> if k = k1 then x else findk xs k

val removek : l:s
            -> k:nat
            -> Pure s
              (requires  member_k k l)
              (ensures (fun res -> (forall e. mem e res <==> mem e l /\ (fst e <> k)) /\ not (member_k k res) /\
                                (forall k1 e. memkeyele res k1 e <==> memkeyele l k1 e /\ k1 <> k)))
let rec removek l ele = 
    match l with
    |[] -> []
    |(k,g)::xs -> if k = ele then xs else (k,g)::removek xs ele

val merge1 : a:s
           -> b:s
           -> Pure s
             (requires true)
             (ensures (fun r -> (forall k. member_k k r <==> member_k k a \/ member_k k b)/\
                             (forall e. mem e r ==> G.unique_s (snd e)) /\
                             (forall k e. memkeyele r k e <==> memkeyele a k e \/ memkeyele b k e)))
                             (decreases %[(length a); b])
#set-options "--z3rlimit 100000"
let rec merge1 a b =
  match a,b with
  |[],[] -> []
  |(k,x)::xs, _ -> if (member_k k b) then (k, (G.merge1 x (findk b k)))::(merge1 xs (removek b k))
                    else (k,x)::merge1 xs b

  |[],_ -> b

val merge : ltr:ae
          -> l:s
          -> atr:ae
          -> a:s
          -> btr:ae
          -> b:s
          -> Pure s
            (requires (forall e. member_id e ltr.l ==> not (member_id e atr.l)) /\
                      (forall e. member_id e atr.l ==> not (member_id e btr.l)) /\
                      (forall e. member_id e ltr.l ==> not (member_id e btr.l)) /\
                      (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
            (ensures (fun res -> (forall k e. memkeyele res k e <==> (memkeyele a k e \/ memkeyele b k e))))
let merge ltr l atr a btr b =
  merge1 a b

val prop_merge : ltr: ae
               -> l:s
               -> atr:ae
               -> a:s
               -> btr:ae
               -> b:s
               -> Lemma (requires (forall e. member_id e ltr.l ==> not (member_id e atr.l)) /\
                                 (forall e. member_id e atr.l ==> not (member_id e btr.l)) /\
                                 (forall e. member_id e ltr.l ==> not (member_id e btr.l)) /\
                                 (sim ltr l /\ sim (union ltr atr) a /\ sim (union ltr btr) b))
                       (ensures (sim (absmerge ltr atr btr) (merge ltr l atr a btr b)))
#set-options "--z3rlimit 100000"
let prop_merge ltr l atr a btr b = 
  assert (forall k e. memkeyele l k e ==> memkeyele a k e /\ memkeyele b k e);
  ()

val insert : a:s
             -> k:nat
             -> e:nat
             -> Pure s
               (requires (member_k k a))
               (ensures (fun r -> unique_k r /\ member_k k r /\
                               (forall e1. mem e1 r ==> G.unique_s (snd e1)) /\
                               (forall e1. member_k e1 r <==> member_k e1 a) /\
                               (forall e1. mem e1 r /\ fst e1 <> k <==> mem e1 a /\ fst e1 <> k) /\
                               (forall e3 e1. mem e3 a /\ mem e1 r /\ fst e3 = k /\ fst e1 = k ==> 
                               (forall e2. mem e2 (snd e3) \/ e2 = e <==> mem e2 (snd e1))) /\
                               (forall k1 e1. memkeyele r k1 e1 <==> memkeyele a k1 e1 \/ (k = k1 /\ e = e1))))
#set-options "--z3rlimit 1000"
let rec insert a k e =
  match a with
    |x::xs -> if k = fst x && mem e (snd x) then a
                   else if k = fst x then ((k,(e::(snd x)))::xs)
                     else (x::insert xs k e)

val app_op : st:s
           -> op:o
           -> Pure s
             (requires true)
             (ensures (fun r -> (forall k. member_k k r <==> member_k k st \/ k = get_key op) /\
                             (unique_k r /\ member_k (get_key op) r) /\
                             (forall e1. mem e1 r ==> G.unique_s (snd e1))  /\
                             (forall e1. mem e1 r /\ fst e1 <> (get_key op) <==> mem e1 st /\ fst e1 <> (get_key op)) /\
                             ((forall k e. memkeyele r k e <==> memkeyele st k e \/ (k = (get_key op) /\ e = (G.get_ele (get_gset op)))))))
             (decreases ( st))

#set-options "--z3rlimit 1000000"
let app_op s1 o = 
  match s1 with
  |[] -> [((get_key o), (G.app_op [] (get_gset o)))]
  |x::xs -> if (member_k (get_key o) s1) then insert s1 (get_key o) (G.get_ele (get_gset o))
               else ((get_key o),[(G.get_ele (get_gset o))])::s1
 
  (*)match s1 with
  |[] -> [(get_key o, (G.app_op [] (get_gset o)))]
  |x::xs -> if fst x = get_key o
             then (((fst x), (G.app_op (snd x) (get_gset o)))::xs)
          else (x::app_op xs o)*)

val append : tr:ae
           -> op:o
           -> Pure ae
             (requires (forall e. mem e tr.l ==> (G.get_id (get_gset op) <> G.get_id (get_gset e))))
             (ensures (fun res -> true))
let append tr op =
    match tr with
    |(A _ []) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && tr.vis o o1) ||
                             (mem o tr.l && o1 = op && G.get_id (get_gset o) <> G.get_id (get_gset op))) (((get_key op), (get_gset op))::[]))
    |(A _ (x::xs)) -> (A (fun o o1 -> (mem o tr.l && mem o1 tr.l && G.get_id (get_gset o) <> G.get_id (get_gset o1) && tr.vis o o1) ||
                                 (mem o tr.l && o1 = op && G.get_id (get_gset o) <> G.get_id (get_gset op)))
                                 (op::(x::xs)))

val prop_oper : tr:ae
               -> st:s
               -> op:o
               -> Lemma (requires (sim tr st) /\ 
                                  not (member_id (G.get_id (get_gset op)) tr.l) )
                       (ensures (sim (append tr op) (app_op st op)))
let prop_oper tr st op = ()

val convergence : tr:ae
                -> a:s
                -> b:s
                -> Lemma (requires (sim tr a /\ sim tr b))
                        (ensures (forall k e. memkeyele a k e <==> memkeyele b k e))
let convergence tr a b = ()


(*
val insert1 : a:s
            -> k:nat
            -> e:nat
            -> Pure s
              (requires not (member_k k a))
              (ensures (fun r -> unique_k r /\ member_k k r /\
                              (forall e1. mem e1 r ==> G.unique_s (snd e1)) /\
                              (forall e1. member_k e1 r <==> member_k e1 a \/ e1 = k) /\
                              (forall k1 e1. memkeyele r k1 e1 <==> memkeyele a k1 e1 \/ (k = k1 /\ e = e1))))
let insert1 a k e = (k,[e])::a



val insertk : a:s
            -> k:nat
            -> l:list nat
            -> Pure s
              (requires (member_k k a) /\ G.unique_s l)
              (ensures (fun r -> unique_k r /\ member_k k r /\
                          (forall e. mem e r ==> G.unique_s (snd e)) /\
                          (forall e. member_k e a <==> member_k e r) /\
                          (forall k1 e1. memkeyele r k1 e1 <==> memkeyele a k1 e1 \/ (k = k1 /\ mem e1 l))))
                          (decreases l)
let rec insertk a k l =
  match l with
  |[] -> a
  |x::xs -> insertk (insert a k x) k xs

val insertk1 : a:s
             -> k:nat
             -> l:list nat
             -> Pure s
               (requires not (member_k k a) /\ G.unique_s l)
               (ensures (fun r -> unique_k r /\ member_k k r /\
                             (forall e. mem e r ==> G.unique_s (snd e)) /\
                             (forall e. member_k e a \/ e = k <==> member_k e r) /\
                             (forall k1 e1. memkeyele r k1 e1 <==> memkeyele a k1 e1 \/ (k = k1 /\ mem e1 l))))
                             (decreases l)
let insertk1 a k l = (k,l)::a

val findkeys : a:s
             -> Pure (list nat)
               (requires true)
               (ensures (fun l -> (forall e. mem e l <==> member_k e a ) /\ G.unique_s l))
               (decreases %[(length a)])
let rec findkeys a = 
  match a with
  |[] -> []
  |(k,x)::xs -> k::findkeys xs

val fold : acc:s
         -> b:s
         -> l:list nat
         -> Pure s
           (requires l = findkeys b)
           (ensures (fun r -> (forall k. member_k k r <==> member_k k acc \/ member_k k b) /\ 
                           (forall k e. memkeyele r k e <==> memkeyele acc k e \/ memkeyele b k e) /\
                           (forall e. mem e r ==> G.unique_s (snd e)) ))
           (decreases l)
#set-options "--z3rlimit 10"
let rec fold acc b l =
  match l with
  |[] -> acc
  |k::ks -> if (member_k k acc) then fold (insertk acc k (findk b k)) (removek b k) ks
             else fold (insertk1 acc k (findk b k)) (removek b k) ks

val findk2 : a:s
              -> b:s
              -> n:nat
              -> Pure (list nat)
              (requires  length a  + length b = n)
              (ensures (fun l -> (forall e. mem e l <==> member_k e a \/ member_k e b)))
              (decreases %[n;(length b)])

#set-options "--initial_fuel 20 --max_fuel 20 --initial_ifuel 10 --max_ifuel 10"
#set-options "--z3rlimit 100000000"
let rec findk2 a b n = 
    if (n > 0) then
    match a,b with
    |[],[] -> []
    |(k,x)::xs ,_ -> if (member_k k b) then findk2 xs b (n-1) else k::findk2 xs b (n-1)
    |[],(k,x)::xs -> k::(findk2 [] xs (n-1))
    else []

val findki : a:s
               -> b:s
               -> Pure (list nat)
               (requires true)
               (ensures (fun l -> (forall e. mem e l <==> member_k e a /\ member_k e b)))
               (decreases %[(length a)])
#set-options "--z3rlimit 100"
let rec findki a b = 
      match a,b with
      |[],[] -> []
      |(k,x)::xs ,_ -> if (member_k k b) then k::findki xs b else findki xs b
      |[],_ -> []

(*)val fold1 : a:s
            -> b:s
                 -> l:list nat
                 -> Pure s
                 (requires l = findk2 a b (length a + length b))
                 (ensures (fun r -> (forall k. member_k k r <==> member_k k a \/ member_k k b) /\ 
                               (forall k e. memkeyele r k e <==> memkeyele a k e \/ memkeyele b k e) /\
                               (forall e. mem e r ==> G.unique_s (snd e)) ))
                 (decreases l)
#set-options "--initial_fuel 20 --max_fuel 20 --initial_ifuel 10 --max_ifuel 10"
#set-options "--z3rlimit 100000000"
let rec fold1 a b l =
         match l with
         |[] -> []
         |k::ks -> if (member_k k a && member_k k b) then (k, G.merge1 (findk a k) (findk b k))::(fold1 (removek a k) (removek b k) ks)
                else if (member_k k a) then (k, (findk a k))::(fold1 (removek a k) b ks)
                     else (k, (findk b k))::(fold1 a (removek b k) ks)*)

val mergei : a:s
          -> b:s
          -> Pure s
              (requires (forall k. member_k k a <==> member_k k b))
              (ensures (fun r -> (forall k. member_k k r <==> member_k k a /\ member_k k b) /\
                            (forall k. member_k k r ==> (forall e. mem e (findk r k) <==> mem e (G.merge1 (findk a k) (findk b k)))) /\
                            (forall k e. memkeyele r k e <==> memkeyele a k e \/ memkeyele b k e) /\
                            (forall e. mem e r ==> G.unique_s (snd e))))
                     (decreases length a)

(*)#set-options "--initial_fuel 20 --max_fuel 20 --initial_ifuel 10 --max_ifuel 10"*)
#set-options "--z3rlimit 100000"
let rec mergei a b =
  match a with
  |[] -> []
  |(k,x)::xs -> assert (member_k k b); 
              (k, (G.merge1 x (findk b k)))::mergei xs (removek b k)


  (*)val merge1 : a:s
                -> b:s
                -> Pure s
                (requires true)
                (ensures (fun r -> (forall k. member_k k r <==> member_k k a \/ member_k k b)/\
                              (forall e. mem e r ==> G.unique_s (snd e)) /\
                              (forall k e. memkeyele r k e <==> memkeyele a k e \/ memkeyele b k e)))
  let merge1 a b =
    let l = findkeys b in
    fold a b l*)


  val app : a:list nat
          -> b:list nat
          -> Pure (list nat)
            (requires (G.unique_s a /\ G.unique_s b))
            (ensures (fun r -> (forall e. mem e r <==> mem e a \/ mem e b) /\ G.unique_s r ))
  let rec app a b =
    match a, b with
    |[],[] -> []
    |(x::xs),_ -> if (mem x b) then app xs b else x::(app xs b)
    |[],_ -> b


val count : a:s
              -> Pure nat
              (requires true)
              (ensures (fun n -> true))
let rec count a =
    match a with
    |[] -> 0
    |(k,x)::xs -> length x + count xs 
*)










