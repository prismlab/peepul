module History

module L = FStar.List.Tot

module M = Mrdt

val apply_trace : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} -> s -> t:list o -> Tot s (decreases %[t]) 
let rec apply_trace s t =
  match t with
  | [] -> s
  | op::ops -> apply_trace (M.apply_op s op) ops

type history (s:eqtype) (o:eqtype) =
 | History  : state:s
            -> children:list (history s o)
            -> traces:list (list o){L.length traces = L.length children}
            -> history s o

val size : #s:eqtype -> #o:eqtype -> h:history s o -> Tot nat (decreases %[h])
val size' : #s:eqtype -> #o:eqtype -> l:list (history s o) -> Tot nat (decreases %[l])
let rec size h =
    let History  _ ch _ = h in
    1 + size' ch
and size' l =
    match l with
    | [] -> 0
    | x::xs -> size x + size' xs

val hb : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> Tot bool (decreases (size h1))
let rec hb (History s ch tr) h2 = 
  match ch,tr with
  | [],[] -> false
  | x::xs,_::ys -> x = h2 || hb x h2 || hb (History s xs ys) h2

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
let rec wellformed (History s ch tr) =
  match ch, tr with
  | [], [] -> true
  | h::hs, tr::trs ->
      apply_trace s tr = History?.state h &&
      wellformed h &&
      wellformed (History s hs trs)

val hbeq_reflexive : #s:eqtype -> #o:eqtype -> h:history s o
                   -> Lemma (ensures (hbeq h h))
let hbeq_reflexive h = ()

val lemma1 : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} 
           -> h:history s o{wellformed h}
           -> Lemma (ensures (forall h'. hbeq h h' ==> wellformed h')) (decreases (size h))
let rec lemma1 (History s ch tr) = 
  match ch,tr with
  | [],[] -> ()
  | x::xs,y::ys -> 
     lemma1 x; 
     lemma1 (History s xs ys)

val lemma2 : #s:eqtype -> #o:eqtype -> h:history s o
           -> Lemma (ensures (forall h'. L.mem h' (History?.children h) ==> hb h h'))
                   (decreases (size h))
let rec lemma2 h = 
  let History s ch tr = h in
  match ch, tr with
  | [],[] -> ()
  | x::xs,y::ys -> 
      let h' = History s xs ys in
      lemma2 h'

val lemma3 : #s:eqtype -> #o:eqtype -> h1:history s o
           -> Lemma (ensures (forall h2 h3. hb h1 h2 /\ hb h2 h3 ==> hb h1 h3))
                   (decreases (size h1))
let rec lemma3 h = 
  let History s ch tr = h in
  match ch, tr with
  | [], [] -> ()
  | x::xs, y::ys ->
      lemma3 x;
      lemma3 (History s xs ys)

val appendp : #s:eqtype -> #o:eqtype -> p:(history s o -> bool) 
           -> l1:list (history s o){forall e. L.mem e l1 ==> p e}
           -> l2:list (history s o){forall e. L.mem e l2 ==> p e}
           -> l:list (history s o){forall e. L.mem e l ==> p e}
let rec appendp p l1 l2 =
  match l1 with
  | [] -> l2
  | x::xs -> x::(appendp p xs l2)

(* Descendents is inclusive of the given element *)
val descendents  : #s:eqtype -> #o:eqtype -> h:history s o 
                 -> Tot (l:list (history s o){forall h'. L.mem h' l ==> hbeq h h'}) //(decreases (size h))
val descendents' : #s:eqtype -> #o:eqtype -> ch:list (history s o) -> h:history s o{forall h'. L.mem h' ch ==> hbeq h h'}
                 -> Tot (l:list (history s o){forall h'. L.mem h' l ==> hbeq h h'}) //(decreases (sum (L.map size ch)))
let rec descendents h =
  let History _ ch _ = h in
  lemma2 h;
  h::descendents' ch h
and descendents' ch h =
  match ch with
  | [] -> []
  | x::xs -> 
      assert (hbeq h x);
      let l1 = descendents x in
      assert (forall h'. L.mem h' l1 ==> hbeq x h');
      lemma3 h;
      assert (forall h'. L.mem h' l1 ==> hbeq h h');
      let l2 = descendents' xs h in
      assert (forall h'. L.mem h' l2 ==> hbeq h h');
      x :: (appendp (fun h' -> hbeq h h') l1 l2)

val remove_descendents2 : #s:eqtype -> #o:eqtype
                        -> l:list (history s o)
                        -> p:(history s o -> bool){forall h. L.mem h l ==> p h}
                        -> a:history s o
                        -> b:history s o
                        -> r:list (history s o){forall h. L.mem h r ==> p h /\ hbeq h a /\ hbeq h b}
let rec remove_descendents2 l p a b =
  match l with
  | [] -> []
  | h::hs -> 
      if hbeq h a && hbeq h b then
        h::remove_descendents2 hs p a b
      else remove_descendents2 hs p a b

val ancestors2 : #s:eqtype -> #o:eqtype 
              -> h:history s o -> a:history s o{hbeq h a} -> b:history s o{hbeq h b}
              -> l:list (history s o){forall h'. L.mem h' l ==> hbeq h h' /\ hbeq h' a /\ hbeq h' b}
let ancestors2 h a b =
  let d = descendents h in
  let res = remove_descendents2 d (fun h' -> hbeq h h') a b in
  assert (forall h'. L.mem h' res ==> hbeq h h' /\ hbeq h' a /\ hbeq h' b);
  assert (forall h'. L.mem h' res ==> hbeq h' a);
  assert (forall h'. L.mem h' res ==> hbeq h' b);
  res

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

val lca : #s:eqtype -> #o:eqtype -> h:history s o -> a:history s o{hbeq h a} -> b:history s o{hbeq h b}
        -> l:list (history s o){forall h'. L.mem h' l ==> hbeq h h' /\ hbeq h' a /\ hbeq h' b /\ (forall h''. L.mem h'' l ==> h' = h'' \/ concurrent h' h'')}
let lca h a b =
  if h = a || h = b then [h]
  else begin
    assert (hb h a /\ hb h b);
    let a = ancestors2 h a b in
    cross_concurrent a
  end
