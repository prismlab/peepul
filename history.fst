module History

module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

open FStar.Tactics
module T = FStar.Tactics
open FStar.Tactics.Typeclasses

class datatype (state:eqtype) (operation:eqtype) = {
  apply_op : state -> operation -> state;
}

val apply_trace: #s:eqtype -> #o:eqtype -> {| datatype s o |}
               -> st:s -> tr:list o -> Tot s (decreases %[tr])
let apply_trace st tr = L.fold_left apply_op st tr

type history (s:eqtype) (o:eqtype) =
 | HistLeaf : id:nat -> state:s -> history s o
 | HistNode : id:nat
            -> state:s
            -> tr1:list o
            -> ch1:history s o
            -> tr2:list o
            -> ch2:history s o
            -> history s o

val get_state : #s:eqtype -> #o:eqtype -> history s o -> s
let get_state h = 
  match h with 
  | HistLeaf _ s -> s
  | HistNode _ s _ _ _ _ -> s
  
let id h = 
  match h with 
  | HistLeaf id _ -> id
  | HistNode id _ _ _ _ _ -> id

val size : #s:eqtype -> #o:eqtype -> h:history s o -> nat
let rec size h =
  match h with
  | HistLeaf _ _ -> 0
  | HistNode _ _ _ ch1 _ ch2 -> 1 + size ch1 + size ch2

val hb : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> bool 
let rec hb h1 h2 =
  match h1 with
  | HistLeaf _ _ -> false 
  | HistNode _ _ _ ch1 _ ch2 -> ch1 = h2 || ch2 = h2 || hb ch1 h2 || hb ch2 h2

val hbeq : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> bool
let hbeq h1 h2 = h1 = h2 || hb h1 h2

val concurrent : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> bool
let concurrent h1 h2 = not (hb h1 h2 || hb h2 h1 || h1 = h2)

val concurrent_commutative : #s:eqtype -> #o:eqtype 
                           -> h1:history s o
                           -> h2:history s o{concurrent h1 h2}
                           -> Lemma (ensures (concurrent h2 h1))
let concurrent_commutative h1 h2 = ()

val wellformed : #s:eqtype -> #o:eqtype -> {|datatype s o|} -> h:history s o -> bool
let rec wellformed h =
  match h with
  | HistLeaf _ _ -> true
  | HistNode _ st tr1 ch1 tr2 ch2 ->
      apply_trace st tr1 = get_state ch1 &&
      apply_trace st tr2 = get_state ch2 &&
      wellformed ch1 && wellformed ch2

val hbeq_reflexive : #s:eqtype -> #o:eqtype -> h:history s o
                   -> Lemma (ensures (hbeq h h))
let hbeq_reflexive h = ()

val lemma1 : #s:eqtype -> #o:eqtype -> {| datatype s o |} 
           -> h:history s o{wellformed h}
           -> Lemma (ensures (forall h'. hbeq h h' ==> wellformed h')) //(decreases (size h))
let rec lemma1 h =
  match h with 
  | HistLeaf _ _ -> ()
  | HistNode _ _ _ ch1 _ ch2 ->
      lemma1 ch1;
      lemma1 ch2

val lemma2 : #s:eqtype -> #o:eqtype -> h1:history s o
           -> Lemma (ensures (forall h2 h3. hb h1 h2 /\ hb h2 h3 ==> hb h1 h3))
let rec lemma2 h = 
  match h with
  | HistLeaf _ _ -> ()
  | HistNode _ _ _ ch1 _ ch2 ->
      lemma2 ch1;
      lemma2 ch2

val append_des : #s:eqtype -> #o:eqtype
             -> h:history s o
             -> l1:list (history s o)
             -> l2:list (history s o)
             -> acc:list (history s o)
             -> Pure (list (history s o)) 
                    (requires (forall h'. hbeq h h' <==> L.mem h' l1 \/ L.mem h' l2 \/ L.mem h' acc))
                    (ensures (fun l -> forall h'. hbeq h h' <==> L.mem h' l))
let rec append_des h l1 l2 acc = 
  match l1, l2 with
  | [], [] -> acc
  | x::xs, _ -> append_des h xs l2 (x::acc)
  | [], x::xs -> append_des h [] xs (x::acc)

val descendents  : #s:eqtype -> #o:eqtype -> h:history s o 
                 -> Tot (l:list (history s o){(forall h'. L.mem h' l <==> hbeq h h') /\ Cons? l}) 
let rec descendents h =
  match h with
  | HistLeaf _ _ -> [h] 
  | HistNode _ _ _ ch1 _ ch2 ->
      lemma2 h;
      let l1 = descendents ch1 in 
      let l2 = descendents ch2 in
      append_des h l1 l2 [h]

val is_lca : #s:eqtype -> #o:eqtype
           -> l:history s o
           -> a:history s o
           -> b:history s o
           -> Tot bool
let is_lca l a b =
  hbeq l a && hbeq l b &&
  begin match l with
  | HistLeaf _ _ -> true 
  | HistNode _ _ _ ch1 _ ch2 ->
      (not (hbeq ch1 a && hbeq ch1 b)) &&
      (not (hbeq ch2 a && hbeq ch2 b))
  end

val lca_ : #s:eqtype -> #o:eqtype
         -> h:history s o
         -> a:history s o{hbeq h a}
         -> b:history s o{hbeq h b}
         -> l:list (history s o)
         -> acc1:list (history s o){forall h'. L.mem h' acc1 ==> ~(hbeq h h' /\ is_lca h' a b)}
         -> acc2:list (history s o){forall h'. L.mem h' acc2 ==> hbeq h h' /\ is_lca h' a b}
         -> Pure (list (history s o))
                (requires (forall h'. L.mem h' l \/ L.mem h' acc1 \/ L.mem h' acc2 <==> hbeq h h'))
                (ensures (fun r -> forall h'. L.mem h' r <==> hbeq h h' /\ is_lca h' a b))
let rec lca_ h a b l acc1 acc2 = 
  match l with
  | [] -> acc2
  | x::xs ->
      if is_lca x a b then
        lca_ h a b xs acc1 (x::acc2)
      else
        lca_ h a b xs (x::acc1) acc2

val remove_duplicates : #s:eqtype -> #o:eqtype
                      -> l:list (history s o)
                      -> acc1:list (history s o){L.noRepeats acc1}
                      -> orig:list (history s o)
                      -> Pure (list (history s o))
                             (requires (forall h'. L.mem h' l \/ L.mem h' acc1 <==> L.mem h' orig))
                             (ensures (fun r -> L.noRepeats r /\ (forall h'. L.mem h' r <==> L.mem h' orig)))
let rec remove_duplicates l acc1 orig =
  match l with
  | [] -> acc1
  | x::xs ->
      if not (L.mem x acc1) then begin
        LP.noRepeats_cons x acc1;
        remove_duplicates xs (x::acc1) orig
      end else remove_duplicates xs acc1 orig

val lca : #s:eqtype -> #o:eqtype
        -> h:history s o
        -> a:history s o{hbeq h a}
        -> b:history s o{hbeq h b}
        -> Tot (l:list (history s o){(forall h'. L.mem h' l <==> hbeq h h' /\ is_lca h' a b) /\ L.noRepeats l})
let lca h a b =
  let d = descendents h in
  let lca_with_duplicates = lca_ h a b d [] [] in
  remove_duplicates lca_with_duplicates [] lca_with_duplicates

val lemma_lca_commutative:
    #s:eqtype -> #o:eqtype
  -> h:history s o
  -> a:history s o{hbeq h a}
  -> b:history s o{hbeq h b}
  -> Lemma (ensures (forall h'. L.mem h' (lca h a b) <==> L.mem h' (lca h b a)))
let lemma_lca_commutative h a b = ()

val lemma_lca_idempotence:
    #s:eqtype -> #o:eqtype
  -> h:history s o
  -> a:history s o{hbeq h a}
  -> Lemma (ensures ((forall h'. L.mem h' (lca h a a) ==> h' = a)))
let lemma_lca_idempotence h a = ()

val append_trace : #s:eqtype -> #o:eqtype -> {| datatype s o |}
                 -> s1:s -> tr1:list o -> s2:s -> tr2:list o -> s3:s
                 -> Pure (list o) (requires (apply_trace s1 tr1 = s2 /\ apply_trace s2 tr2 = s3))
                                 (ensures (fun tr -> apply_trace s1 tr = s3))
                                 (decreases %[tr1])
let rec append_trace s1 tr1 s2 tr2 s3 =
  match tr1 with
  | [] -> tr2
  | op::ops ->
      let tr = append_trace (apply_op s1 op) ops s2 tr2 s3 in
      op::tr

val get_trace : #s:eqtype -> #o:eqtype -> {| datatype s o |}
              -> a:history s o{wellformed a}
              -> b:history s o{hbeq a b}
              -> tr:list o{L.fold_left apply_op (get_state a) tr = get_state b}
let rec get_trace a b =
  lemma1 a;
  if a = b then []
  else begin
    match a with
    | HistLeaf _ _ -> []
    | HistNode _ _ tr1 ch1 tr2 ch2 ->
        assert (wellformed ch1);
        assert (wellformed ch2);
        if hbeq ch1 b then
          append_trace (get_state a) tr1 (get_state ch1) (get_trace ch1 b) (get_state b)
        else 
          append_trace (get_state a) tr2 (get_state ch2) (get_trace ch2 b) (get_state b)
  end

class mrdt (s:eqtype) (o:eqtype) (m : datatype s o) = {
  merge : h:history s o{wellformed h}
        -> a:history s o{hbeq h a}
        -> b:history s o{hbeq h b}
        -> l:history s o{lca h a b = [l]}
        -> s;

  commutativity : h:history s o{wellformed h} 
                -> a:history s o{hbeq h a} 
                -> b:history s o{hbeq h b} 
                -> l:history s o{lca h a b = [l] /\ lca h b a = [l]}
                -> Lemma (ensures (merge h a b l = merge h b a l));

  idempotence : h:history s o{wellformed h}
              -> a:history s o{hbeq h a}
              -> Lemma (requires (lca h a a = [a]))
                      (ensures (merge h a a a = get_state a))
}
