module History

//open FStar.Tactics
//module T = FStar.Tactics
//open FStar.Tactics.Typeclasses

module L = FStar.List.Tot

module M = Mrdt

val apply_trace : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} -> s -> t:list o -> Tot s (decreases %[t]) 
let rec apply_trace s t =
  match t with
  | [] -> s
  | op::ops -> apply_trace (M.apply_op s op) ops

type history (s:eqtype) (o:eqtype) =
 | History  : state:s
            -> children:list (list o * history s o)
            -> history s o

val size : #s:eqtype -> #o:eqtype -> h:history s o -> Tot nat (decreases %[h])
val size' : #s:eqtype -> #o:eqtype -> l:list (list o * history s o) -> Tot nat (decreases %[l])
let rec size h =
    let History  _ ch = h in
    1 + size' ch
and size' l =
    match l with
    | [] -> 0
    | (tr,x)::xs -> size x + size' xs

val hb : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> Tot bool (decreases (size h1))
let rec hb (History s ch) h2 = 
  match ch with
  | [] -> false
  | (_,x)::xs -> x = h2 || hb x h2 || hb (History s xs) h2

(* h1 --hb--> h2 <==> hbeq h1 h2 = true *)
val hbeq : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> bool
let hbeq h1 h2 = h1 = h2 || hb h1 h2

val concurrent : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> bool
let concurrent h1 h2 = not (hb h1 h2 || hb h2 h1 || h1 = h2)

val concurrent_commutative : #s:eqtype -> #o:eqtype 
                           -> h1:history s o
                           -> h2:history s o{concurrent h1 h2}
                           -> Lemma (ensures (concurrent h2 h1))
let concurrent_commutative h1 h2 = ()

val wellformed : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} -> h:history s o -> Tot bool (decreases (size h))
let rec wellformed (History s ch) =
  match ch with
  | [] -> true
  | (tr,h)::xs ->
      apply_trace s tr = History?.state h &&
      wellformed h &&
      wellformed (History s xs)

val hbeq_reflexive : #s:eqtype -> #o:eqtype -> h:history s o
                   -> Lemma (ensures (hbeq h h))
let hbeq_reflexive h = ()

val lemma1 : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} 
           -> h:history s o{wellformed h}
           -> Lemma (ensures (forall h'. hbeq h h' ==> wellformed h')) (decreases (size h))
let rec lemma1 (History s ch) = 
  match ch with
  | [] -> ()
  | (_,x)::xs -> 
     lemma1 x; 
     lemma1 (History s xs)

val concurrent_list : #s:eqtype -> #o:eqtype 
                    -> h:history s o 
                    -> l:list (history s o) 
                    -> r:bool{(forall h'. L.mem h' l ==> concurrent h h') <==> r = true}
let rec concurrent_list h l =
  match l with
  | [] -> true
  | x::xs -> concurrent h x && concurrent_list h xs

val cross_concurrent : #s:eqtype -> #o:eqtype
                     -> l:list (history s o)
                     -> r:list (history s o){(forall c. L.mem c r ==> L.mem c l) /\
                                            (forall c1 c2. L.mem c1 r /\ L.mem c2 r /\ ~(c1 = c2) ==> concurrent c1 c2)}
let rec cross_concurrent l = 
  match l with
  | [] -> []
  | x::xs -> 
      if concurrent_list x xs then 
        x::cross_concurrent xs
      else cross_concurrent xs

val append : #s:eqtype -> #o:eqtype -> p:(history s o -> bool) 
           -> l1:list (history s o){forall e. L.mem e l1 ==> p e}
           -> l2:list (history s o){forall e. L.mem e l2 ==> p e}
           -> l:list (history s o){forall e. L.mem e l ==> p e}
let rec append p l1 l2 =
  match l1 with
  | [] -> l2
  | x::xs -> x::(append p xs l2)

val lca_ : #s:eqtype -> #o:eqtype //-> {| M.mrdt s o |} XXX KC TODO
        -> m:M.mrdt s o
        -> h:history s o
        -> a:history s o{hb h a}
        -> b:history s o{hb h b}
        -> Tot (lcalst: list (history s o){(forall l. L.mem l lcalst ==> hb h l /\ hbeq l a /\ hbeq l b) /\ 
                                          (forall l1 l2. L.mem l1 lcalst /\ L.mem l2 lcalst /\ ~(l1 = l2) ==> concurrent l1 l2)})
              (decreases (size h))
let rec lca_ m h a b =
  let History s ch = h in
  match ch with
  | [] -> []
  | (_,x)::xs ->
      let l1 =
        if hb x a && hb x b then
          lca_ m x a b
        else []
      in
      let h' = History s xs in
      let l2 = 
        if hb h' a && hb h' b then
          lca_ m h' a b
        else []
      in
      assert (forall c. L.mem c l1 ==> hbeq c a /\ hbeq c b);
      assert (forall c. L.mem c l2 ==> hbeq c a /\ hbeq c b);
      let p = fun c -> hb h c && hbeq c a && hbeq c b in
      let l = (append p l1 l2) in
      cross_concurrent l

val lca : #s:eqtype -> #o:eqtype //-> {| M.mrdt s o |} XXX KC TODO
        -> m:M.mrdt s o
        -> h:history s o
        -> a:history s o{hbeq h a}
        -> b:history s o{hbeq h b}
        -> Tot (lcalst: list (history s o){(forall l. L.mem l lcalst ==> hbeq h l /\ hbeq l a /\ hbeq l b) /\ 
                                          (forall l1 l2. L.mem l1 lcalst /\ L.mem l2 lcalst /\ ~(l1 = l2) ==> concurrent l1 l2)})
              (decreases (size h))
let lca m h a b = 
  if h = a || h = b then [h]
  else begin
    assert (hb h a /\ hb h b);
    cross_concurrent (h::lca_ m h a b)
  end
