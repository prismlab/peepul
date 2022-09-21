module Nn_ctr

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
  |Inc
  |Dec

///SEQUENTIAL DATA TYPE IMPLEMENTATION///

type s = nat

let init = 0

val do : s1:s -> o:(nat * op) -> s2:s{(get_op o = Inc ==> s2 = s1 + 1) /\
                                  (get_op o = Dec /\ s1 > 0 ==> s2 = s1 - 1) /\
                                  (get_op o = Dec /\ s1 = 0 ==> s2 = s1)}
let do s op =
    match op with
    |(_,Inc) -> s + 1
    |(_,Dec) -> if s > 0 then s - 1 else s

val spec : s1:s -> o1:(nat * op) -> o2:(nat * op) -> s
let spec s1 o1 o2 =
    match o1, o2 with
    |(_,Inc), (_,Dec) -> do (do s1 o2) o1
    |(_,Dec), (_,Dec) -> do s1 o1
    |_ -> do (do s1 o1) o2

val fold : st:s -> l:list (nat * op){unique_id l} -> Tot s (decreases l)
let rec fold s l =
  match l with
  |[] -> s
  |x::xs -> fold (do s x) xs

////////////MRDT IMPLEMENTATION////////////

type s' = n:(nat * nat){fst n >= snd n}

val init' : s'
let init' = (0, 0)

let pre_cond_do' s o = true

val do' : st:s' -> (nat * op) -> st1:s'{fst st1 >= fst st /\ snd st1 >= snd st}
let do' s' op =
    match op with
    |(_,Inc) -> (fst s' + 1, snd s')
    |(_,Dec) -> if fst s' > snd s' then (fst s', snd s' + 1) else s'

val tl : l:list(nat * op){l <> []} -> Tot (t:(nat * op){mem t l})
let rec tl l =
  match l with
  |[x] -> x
  |x::xs -> tl xs

val fold' : st:s' -> l:list (nat * op){unique_id l} -> Tot (st':s' {fst st' >= fst st /\ snd st' >= snd st})
            (decreases l)
let rec fold' s l =
    match l with
    |[] -> s
    |x::xs -> fold' (do' s x) xs

val pre_cond_merge' : l:s' -> a:s' -> b:s' -> bool
let pre_cond_merge' l a b = fst a >= fst l && fst b >= fst l && snd a >= snd l && snd b >= snd l

val num_dec_from_lca : l:s' -> a:s'{fst a >= fst l /\ snd a >= snd l} -> Tot nat
let num_dec_from_lca (il, dl) (ia, da) =
  if il - dl < da - dl then
      (* the number of new decrement operations that were performed on the child
         is greater than the original number of available values in the lca. Then
         all the values in the lca must have been decremented. *)
     il - dl
  else
      (* Otherwise, the number of lca values decremented is exactly the number of
         new decrements *)
     da - dl

val overcount : l:s' -> a:s'{fst a >= fst l /\ snd a >= snd l} -> b:s'{fst b >= fst l /\ snd b >= snd l}
              -> Tot nat 
let overcount l a b =
  let na = num_dec_from_lca l a in
  let nb = num_dec_from_lca l b in
  min na nb

(** Concrete THREE_WAY MERGE function*)
val merge' : l:s' -> a:s' -> b:s'
             -> Pure s' (requires pre_cond_merge' l a b)
                   (ensures (fun r -> true))
let merge' l a b = 
    let o = overcount l a b in
    let i = fst a + fst b - fst l in
    let d = snd a + snd b - snd l in
    (i, d - o)(* account for the overcount *)

////////////////////////////////////////////

val eq : st:s -> st':s' -> bool
let eq s s' = s = fst s' - snd s'

val eq_m : a:s' -> b:s' -> bool
let eq_m a b = fst a - snd a = fst b - snd b

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
            -> Pure s'
              (requires (get_op o = Inc ==> fst st > 0 /\ fst st - snd st > 0) /\
                        (get_op o = Dec ==> snd st > 0))
              (ensures (fun r -> st = do' r o))
let inverse a o =
  match o with
  |(_, Inc) -> (fst a - 1, snd a)
  |(_, Dec) -> (fst a, snd a - 1)

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

val spec' : s1:s' -> o1:(nat * op) -> o2:(nat * op) -> s'
let spec' s1 o1 o2 =
    match o1, o2 with
    |(_,Inc), (_,Dec) -> do' (do' s1 o2) o1
    |(_,Dec), (_,Dec) -> do' s1 o1
    |_ -> do' (do' s1 o1) o2

val prop_merge1 : l:s' -> a:s' -> b:s' 
                -> atr:list(nat * op) -> o1:(nat * op) 
                -> btr:list(nat * op) -> o2:(nat * op) 
                -> Lemma (requires (unique_id atr /\ unique_id btr /\ get_id o1 <> get_id o2 /\
                                  (forall e. mem e atr ==> not (mem_id (get_id e) btr)) /\
                                  not (mem_id (get_id o1) atr) /\ not (mem_id (get_id o1) btr) /\
                                  not (mem_id (get_id o2) atr) /\ not (mem_id (get_id o2) btr) /\
                                  a = fold' l (append atr [o1]) /\ b = fold' l (append btr [o2]) /\
                                  (get_op o1 = Inc ==> fst a > 0 /\ fst a - snd a > 0) /\ (get_op o1 = Dec ==> snd a > 0) /\
                                  (get_op o2 = Inc ==> fst b > 0 /\ fst b - snd b > 0) /\ (get_op o2 = Dec ==> snd b > 0) /\
                                  (inverse a o1 = fold' l atr /\ inverse b o2 = fold' l btr)))
                        (ensures (let ia = (inverse a o1) in let ib = (inverse b o2) in
                                   (let merge_prefix = (merge' l ia ib) in 
                                      ((merge' l a b) = (merge' merge_prefix (do' merge_prefix o1) (do' merge_prefix o2))))))

#set-options "--z3rlimit 10000"
let prop_merge1 l a b atr o1 btr o2 = admit()

val prop_merge2 : l:s' -> a:s' -> b:s' -> op1:(nat * op) -> op2:(nat * op)
                -> Lemma (requires (a = do' l op1 /\ b = do' l op2 /\ get_id op1 <> get_id op2))
                        (ensures (pre_cond_merge' l a b) /\
                                 (forall sl. eq sl l ==> (eq (spec sl op1 op2) (merge' l a b))))
let prop_merge2 l a b opa opb = ()

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



