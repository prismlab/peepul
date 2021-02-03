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

val trace_ok : #s:eqtype -> #o:eqtype -> {|datatype s o|} -> h:history s o -> bool
let rec trace_ok h =
  match h with
  | HistLeaf _ _ -> true
  | HistNode _ st tr1 ch1 tr2 ch2 ->
      apply_trace st tr1 = get_state ch1 &&
      apply_trace st tr2 = get_state ch2 &&
      trace_ok ch1 && trace_ok ch2

val hbeq_reflexive : #s:eqtype -> #o:eqtype -> h:history s o
                   -> Lemma (ensures (hbeq h h))
let hbeq_reflexive h = ()

val lemma1 : #s:eqtype -> #o:eqtype -> {| datatype s o |} 
           -> h:history s o{trace_ok h}
           -> Lemma (ensures (forall h'. hbeq h h' ==> trace_ok h')) //(decreases (size h))
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

val lemma_is_lca_commutative : 
    #s:eqtype -> #o:eqtype
  -> l:history s o
  -> a:history s o
  -> b:history s o
  -> Lemma (ensures (is_lca l a b = is_lca l b a))
    [SMTPat (is_lca l a b)]
let lemma_is_lca_commutative l a b = ()

val lemma3 : #s:eqtype -> #o:eqtype 
           -> a:history s o -> b:history s o{hb a b}
           -> Lemma (ensures (~(hb b a)))
let rec lemma3 a b =
  match a with
  | HistLeaf _ _ -> ()
  | HistNode _ _ _ ch1 _ ch2 ->
     admit ()
      
val lemma_is_lca_reflexive :
    #s:eqtype -> #o:eqtype
  -> a:history s o
  -> Lemma (ensures (is_lca a a a))
let rec lemma_is_lca_reflexive a = 
  match a with
  | HistLeaf _ _ -> ()
  | HistNode _ _ _ ch1 _ ch2 -> 
      lemma3 a ch1;
      lemma3 a ch2

val lca_ : #s:eqtype -> #o:eqtype
         -> h:history s o
         -> a:history s o{hbeq h a}
         -> b:history s o{hbeq h b}
         -> l:list (history s o)
         -> acc1:list (history s o){forall h'. L.mem h' acc1 ==> ~(is_lca h' a b)}
         -> acc2:list (history s o){forall h'. L.mem h' acc2 ==> is_lca h' a b}
         -> Pure (list (history s o))
                (requires (//(L.length l + L.length acc1 + L.length acc2 > 0) /\
                           (forall h'. L.mem h' l \/ L.mem h' acc1 \/ L.mem h' acc2 <==> hbeq h h')))
                (ensures (fun r -> forall h'. L.mem h' r <==> hbeq h h' /\ is_lca h' a b)) //TODO: Prove Cons? r
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
  -> Lemma (ensures ((forall h'. L.mem h' (lca h a a) ==> h' = a))) //TODO: Prove lca h a a = [a]
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
              -> a:history s o{trace_ok a}
              -> b:history s o{hbeq a b}
              -> tr:list o{L.fold_left apply_op (get_state a) tr = get_state b}
let rec get_trace a b =
  lemma1 a;
  if a = b then []
  else begin
    match a with
    | HistLeaf _ _ -> []
    | HistNode _ _ tr1 ch1 tr2 ch2 ->
        assert (trace_ok ch1);
        assert (trace_ok ch2);
        if hbeq ch1 b then
          append_trace (get_state a) tr1 (get_state ch1) (get_trace ch1 b) (get_state b)
        else 
          append_trace (get_state a) tr2 (get_state ch2) (get_trace ch2 b) (get_state b)
  end

val children : #s:eqtype -> #o:eqtype -> h:history s o -> list (history s o)
let children h = 
  match h with
  | HistLeaf _ _ -> []
  | HistNode _ _ _ ch1 _ ch2 -> [ch1; ch2]

val merge_node : #s:eqtype -> #o:eqtype 
               -> a:history s o
               -> b:history s o
               -> m:history s o
               -> r:bool{L.mem m (children a) /\ L.mem m (children b) <==> r = true}
let merge_node a b m =
  L.mem m (children a) && L.mem m (children b)

val unique_lca : #s:eqtype -> #o:eqtype
               -> h:history s o
               -> a:history s o{hbeq h a}
               -> b:history s o{hbeq h b}
               -> Tot (r:bool{r = true <==> (exists l. lca h a b = [l])})
let unique_lca h a b =
  match lca h a b with
  | [_] -> true
  | _ -> false

val wellformed : #s:eqtype -> #o:eqtype -> {| datatype s o |}
               -> h:history s o
               -> Tot (r:bool {r = true <==> (trace_ok h /\ (forall h1 h2. hbeq h h1 /\ hbeq h h2 ==> unique_lca h h1 h2))})
let wellformed h = admit ()

val lemma4 : #s:eqtype -> #o:eqtype -> {| datatype s o |} 
           -> h:history s o{wellformed h}
           -> Lemma (ensures (forall h'. hbeq h h' ==> wellformed h')) //(decreases (size h))
             [SMTPat (wellformed h)]
let rec lemma4 h = admit ()

val lemma_merge_node_is_descendent : 
    #s:eqtype -> #o:eqtype -> {| datatype s o |}
  -> a:history s o{wellformed a}
  -> b:history s o{wellformed b}
  -> m:history s o{merge_node a b m}
  -> Lemma (ensures (hb a m /\ hb b m /\ wellformed m))
let lemma_merge_node_is_descendent a b m =
  lemma4 a

val lcau : #s:eqtype -> #o:eqtype -> {| datatype s o |}
         -> h:history s o{wellformed h}
         -> a:history s o{hbeq h a}
         -> b:history s o{hbeq h b}
         -> Tot (l:history s o{wellformed l /\ is_lca l a b /\ hbeq h l})
let lcau h a b =
  lemma1 h;
  assert (hbeq h a);
  assert (hbeq h b);
  assert (unique_lca h a b);
  let [l] = lca h a b in
  l

val lcau_associative : #s:eqtype -> #o:eqtype -> {| datatype s o |}
                     -> h:history s o{wellformed h}
                     -> a:history s o{wellformed a /\ hbeq h a}
                     -> b:history s o{wellformed b /\ hbeq h b}
                     -> c:history s o{wellformed c /\ hbeq h c}
                     -> lab:history s o{lcau h a b = lab}
                     -> lbc:history s o{lcau h b c = lbc}
                     -> lac:history s o{lcau h c a = lac}
                     -> Lemma (ensures (lcau h lab lac = lcau h lbc lac))
let lcau_associative h a b c lab lbc lca = admit ()

class mrdt (s:eqtype) (o:eqtype) (m : datatype s o) = {
  merge : a:history s o
        -> b:history s o
        -> l:history s o{wellformed l /\ is_lca l a b}
        -> s;

  commutativity : a:history s o
                -> b:history s o
                -> l:history s o{wellformed l /\ is_lca l a b}
                -> Lemma (ensures (merge a b l = merge b a l));

  idempotence : a:history s o{wellformed a /\ is_lca a a a}
              -> Lemma (ensures (merge a a a = get_state a));

  associativity : h:history s o{wellformed h}
                -> a:history s o{wellformed a /\ hbeq h a}
                -> b:history s o{wellformed b /\ hbeq h b}
                -> c:history s o{wellformed c /\ hbeq h c}
                -> lab:history s o{lcau h a b = lab}
                -> lbc:history s o{lcau h b c = lbc}
                -> lac:history s o{lcau h c a = lac}
                -> mab:history s o{hbeq h mab /\ merge_node a b mab /\ get_state mab = merge a b lab}
                -> mbc:history s o{hbeq h mbc /\ merge_node b c mbc /\ get_state mbc = merge b c lbc}
                -> m1:history s o{hbeq h m1 /\ merge_node lab lac m1 /\ get_state m1 = merge lab lac (lcau h lab lac) /\ lcau h a mbc = m1}
                -> m2:history s o{hbeq h m2 /\ merge_node lbc lac m2 /\ get_state m2 = merge lbc lac (lcau h lbc lac) /\ lcau h mab c = m2}
                -> mabc1: history s o{hbeq h mabc1 /\ merge_node a mbc mabc1 /\ get_state mabc1 = merge a mbc m1}
                -> mabc2: history s o{hbeq h mabc2 /\ merge_node mab c mabc2 /\ get_state mabc2 = merge mab c m2}
                -> Lemma (get_state mabc1 = get_state mabc2)
}
