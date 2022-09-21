module Ew

open FStar.List.Tot

val get_id : #op:eqtype -> (nat * op) -> nat
let get_id (id, _) = id

val get_op : #op:eqtype -> (nat * op) -> op
let get_op (_, op) = op

val mem_id : #op:eqtype
           -> id:nat
           -> l:list (nat * op)
           -> Tot (b:bool{(exists op. mem (id,op) l) <==> b=true})
let rec mem_id n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || mem_id n xs

val unique_id : #op:eqtype 
              -> l:list (nat * op)
              -> Tot bool
let rec unique_id l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (mem_id id xs) && unique_id xs

val get_eve : #op:eqtype 
            -> id:nat 
            -> l:list (nat * op){unique_id l /\ mem_id id l}
            -> Tot (s:(nat * op) {get_id s = id /\ mem s l})
let rec get_eve id l =
  match l with
  |(id1, x)::xs -> if id = id1 then (id1, x) else get_eve id xs 

val forallb : #a:eqtype
            -> f:(a -> bool)
            -> l:list a
            -> Tot (b:bool{(forall e. mem e l ==> f e) <==> b = true})
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

val sorted : #op:eqtype
           -> l:list(nat * op){unique_id l} -> bool
let rec sorted #op l =
  match l with
  |[] -> true
  |x::[] -> true
  |x::xs -> forallb (fun (e:(nat * op)) -> fst x < fst e) xs && sorted xs

val filter : #a:eqtype
           -> f:(a -> bool)
           -> l:list a
           -> Tot (l1:list a {forall e. mem e l1 <==> mem e l /\ f e})
let rec filter #a f l = 
  match l with
  |[] -> []
  |hd::tl -> if f hd then hd::(filter f tl) else filter f tl

/////////////////////////////////////////

type op =
  |Enable
  |Disable

///SEQUENTIAL DATA TYPE IMPLEMENTATION///

type s = bool

let init = false

val do : s -> (nat * op) -> s
let do s op =
  match op with
  |(_,Enable) -> true
  |(_,Disable) -> false

val spec : s1:s -> o1:(nat * op) -> o2:(nat * op) -> s
let spec s1 o1 o2 =
  match get_op o1, get_op o2 with
  |Enable, Disable -> do (do s1 o2) o1
  |_ -> do (do s1 o1) o2

val fold : st:s -> l:list (nat * op){unique_id l} -> Tot s (decreases l)
let rec fold s l =
  match l with
  |[] -> s
  |x::xs -> fold (do s x) xs

////////////MRDT IMPLEMENTATION////////////

type s' = nat * bool

val init' : s'
let init' = (0, false)

let pre_cond_do' s o = true

val do' : st:s' -> o:(nat * op) -> st1:s'{(get_op o = Enable <==> (st1 = (fst st + 1, true))) /\
                                      (get_op o = Disable <==> (st1 = (fst st, false)))}
let do' s' op =
  match op with
  |(_,Enable) -> (fst s' + 1, true)
  |(_,Disable) -> (fst s', false)

val tl : l:list(nat * op){l <> []} -> Tot (t:(nat * op){mem t l})
let rec tl l =
  match l with
  |[x] -> x
  |x::xs -> tl xs

val fold' : st:s' -> l:list (nat * op)
          -> Pure s'
            (requires unique_id l)
            (ensures (fun r -> ((l <> [] /\ (forall e. mem e l ==> get_op e <> Disable)) ==> (fst r > fst st)) /\
                             (fst r >= fst st) /\ (l <> [] /\ get_op (tl l) = Enable ==> (fst r > fst st)) /\
                             (l = [] ==> r = st) /\
                             ((snd r = true) <==> ((l = [] /\ snd st = true) \/ (l <> [] /\ get_op (tl l) = Enable))) /\
                             (l <> [] /\ get_op (tl l) = Disable ==> snd r = false)))
              (decreases l)
let rec fold' s l =
  match l with
  |[] -> s
  |x::xs -> fold' (do' s x) xs

val pre_cond_merge' : l:s' -> a:s' -> b:s' -> bool
let pre_cond_merge' l a b = fst a >= fst l && fst b >= fst l

val merge_flag : l:s'
               -> a:s'{fst a >= fst l}
               -> b:s'{fst b >= fst l}
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

val merge' : l:s' 
           -> a:s'
           -> b:s'
           -> Pure s'
             (requires pre_cond_merge' l a b)
             (ensures (fun r -> r = (fst a + fst b - fst l, merge_flag l a b)))
let merge' l a b =
  let c = fst a + fst b - fst l in
  let f = merge_flag l a b in
  c, f

////////////////////////////////////////////

val eq : st:s -> st':s' -> bool
let eq s s' = s = snd s'

val eq_m : a:s' -> b:s' -> bool
let eq_m a b = snd a = snd b

val prop_init : unit -> Lemma (ensures (eq init init'))
let prop_init () = ()

val prop_equivalence : a:s' -> b:s' -> o:(nat * op)
                     -> Lemma (requires (eq_m a b /\ pre_cond_do' a o /\ pre_cond_do' b o))
                             (ensures (eq_m (do' a o) (do' b o)))
let prop_equivalence a b o = ()

val prop_do : st:s -> st':s' -> o:(nat * op)
            -> Lemma (requires (eq st st'))
                    (ensures (eq (do st o) (do' st' o)))
let prop_do s s' op = ()

val inverse : st:s' -> o:(nat * op) 
            -> Pure (list s') 
              (requires (get_op o = Enable ==> fst st > 0) /\
                        (get_op o = Disable <==> snd st = false))
              (ensures (fun r -> (forall e. mem e r ==> st = do' e o)))
let inverse a o =
  match o with
  |(_, Enable) -> [(fst a - 1, true); (fst a - 1, false)]
  |(_, Disable) -> [(fst a, false); (fst a, true)]

val append : l1:list(nat * op) -> l2:list(nat * op)
           -> Pure (list (nat * op))
                  (requires (forall e. mem e l1 ==> not (mem_id (get_id e) l2)) /\
                            unique_id l1 /\ unique_id l2)
                  (ensures (fun r -> (forall e. mem e r <==> mem e l1 \/ mem e l2) /\ unique_id r /\
                                  (l2 <> [] ==> tl r = tl l2)))
                  (decreases %[l1;l2])
let rec append l1 l2 =
  match l1, l2 with
  |[],[] -> []
  |x::xs,_ -> x::(append xs l2)
  |[],x::xs -> x::(append [] xs)

val prop_merge1 : l:s' -> a:s' -> b:s' 
                -> atr:list(nat * op) -> o1:(nat * op) 
                -> btr:list(nat * op) -> o2:(nat * op) 
                -> Lemma (requires (unique_id atr /\ unique_id btr /\ get_id o1 <> get_id o2 /\
                                  (forall e. mem e atr ==> not (mem_id (get_id e) btr)) /\
                                  not (mem_id (get_id o1) atr) /\ not (mem_id (get_id o1) btr) /\
                                  not (mem_id (get_id o2) atr) /\ not (mem_id (get_id o2) btr) /\
                                  a = fold' l (append atr [o1]) /\ b = fold' l (append btr [o2])))
                        (ensures (forall ia ib. mem ia (inverse a o1) /\ mem ib (inverse b o2) ==>
                                   (let merge_prefix = (merge' l ia ib) in 
                                      ((merge' l a b) = (merge' merge_prefix (do' merge_prefix o1) (do' merge_prefix o2))))))
let prop_merge1 l a b atr o1 btr o2 = ()

val prop_merge2 : l:s' -> a:s' -> b:s' -> op1:(nat * op) -> op2:(nat * op)
                -> Lemma (requires (a = do' l op1 /\ b = do' l op2 /\ get_id op1 <> get_id op2))
                        (ensures (pre_cond_merge' l a b) /\
                                 (forall sl. eq sl l ==> (eq (spec sl op1 op2) (merge' l a b))))
let prop_merge2 l a b opa opb = ()

(*)val prop_merge3 : l:s' -> a:s' -> atr:list(nat * op) -> o1:(nat * op)
                -> Lemma (requires (unique_id atr /\ not (mem_id (get_id o1) atr) /\
                                  (a = fold' l (append atr [o1])) /\
                                  (forall e. mem e (inverse a o1) ==> e = fold' l atr)))
                        (ensures (forall ia. mem ia (inverse a o1) ==>
                                    (merge' l a l) = (merge' l ia (do' l o1))))
let prop_merge3 l a atr o1 = ()*)

val prop_merge4 : l:s' -> a:s' -> op1:(nat * op)
                -> Lemma (requires (a = do' l op1))
                        (ensures (pre_cond_merge' l a l) /\
                                 (forall sl. eq sl l ==> (eq (do sl op1) (merge' l a l))))
let prop_merge4 l a op1 = ()

val idempotence : a:s'
                -> Lemma (ensures (a = (merge' a a a)))
let idempotence a = ()

val commutativity : l:s' 
                  -> a:s'
                  -> b:s'
                  -> Lemma (requires (exists atr btr. unique_id atr /\ unique_id btr /\ a = fold' l atr /\ b = fold' l btr))
                          (ensures (merge' l b a = merge' l a b))
let commutativity l a b = ()

val associativity : l:s'
                  -> a:s'
                  -> b:s'
                  -> c:s'
                  -> Lemma (requires (exists atr btr ctr. unique_id atr /\ unique_id btr /\ unique_id ctr /\
                                     a = fold' l atr /\ b = fold' l btr /\ c = fold' l ctr))
                          (ensures (merge' l a (merge' l b c) = merge' l (merge' l a b) c))
let associativity l a b c = ()


val prop_merge00 : l:s' -> a:s' -> b:s' -> op1:(nat * op) -> op2:(nat * op)
                 -> Lemma (requires (a = do' l op1 /\ b = do' l op2 /\ get_id op1 <> get_id op2 /\
                                    (exists atr btr. unique_id atr /\ unique_id btr /\
                                    a = fold' l atr /\ b = fold' l btr)))
                         (ensures (pre_cond_merge' l a b) /\
                                  (forall sl. eq sl (merge' l a b) ==> 
                                     (eq (spec sl op1 op2) (merge' (merge' l a b)
                                                                   (do' (merge' l a b) op1) 
                                                                   (do' (merge' l a b) op2)))))

let prop_merge00 l a b opa opb = ()
