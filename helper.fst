module Helper

open FStar.List.Tot
open FStar.Tactics.Typeclasses
open FStar.Tactics

(*
Things to be moved here:
+ func member
+ func unique
+ type ae
- Props for diff
- Props for union
- Props for abs_merge, merge and prop_merge

All of these, depend on types op and o which are specific to each MRDT.
One thing we can do is create an init function, that takes in the op and returns the MRDT-specific funcs and props.
I'm thinking of other ideas still. If I come up with anything cleaner, I'll add that.
*)

val member : #op:eqtype
           -> id:nat
           -> l:list (nat * op)
           -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})

let rec member n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member n xs

// type v = (o:eqtype{exists op. subtype_of o (nat * op)})

val unique : #op:eqtype
           -> l:list (nat * op)
           -> Tot bool

let rec unique l =
  match l with
  |[] -> true
  |(id,_)::xs -> not (member id xs) && unique xs

let get_id (id,_) = id
let get_op (_,op) = op

noeq type ae (op:eqtype) =
| A : vis : ((nat * op) -> (nat * op) -> Tot bool)
      ->  l:(list (nat * op)) {(forall e e' e''. (mem e l /\ mem e' l /\ mem e'' l  /\ get_id e <> get_id e' /\ 
                         get_id e' <> get_id e'' /\ get_id e <> get_id e'  /\ vis e e' /\ vis e' e'') ==> vis e e'') /\
                      (forall e e'. (mem e l /\ mem e' l /\ get_id e <> get_id e' /\  vis e e') ==> not (vis e' e)) /\
                      (forall e. mem e l ==> not (vis e e) /\
                      (unique l))}
      ->  ae op

class mrdt_props (op:eqtype) (s:eqtype) (app_op:s -> (nat * op) -> s) (sim_prop:s -> (ae op) ->s -> bool -> prop) (diff_prop:prop) (union_prop:prop)  = {

  sim : s0:s
        -> tr:ae op
        -> s1:s
        -> Tot (b:bool{ sim_prop s0 tr s1 b });


  absmerge : l:ae op
             -> a:ae op
             -> b:ae op
             -> Pure (ae op)
               (requires (forall e. mem e l.l ==> not (member (get_id e) a.l)) /\
                         (forall e. mem e a.l ==> not (member (get_id e) b.l)) /\
                         (forall e. mem e b.l ==> not (member (get_id e) l.l)))
                (ensures (fun u -> (forall e. mem e u.l <==> mem e l.l \/ mem e a.l \/ mem e b.l) /\
                                (forall e1 e2. (mem e1 u.l /\ mem e2 u.l /\ get_id e1 <> get_id e2 /\ u.vis e1 e2) <==>
                                          (mem e1 l.l /\ mem e2 l.l /\ get_id e1 <> get_id e2 /\ l.vis e1 e2) \/
                                          (mem e1 a.l /\ mem e2 a.l /\ get_id e1 <> get_id e2 /\ a.vis e1 e2) \/
                                          (mem e1 b.l /\ mem e2 b.l /\ get_id e1 <> get_id e2 /\ b.vis e1 e2) \/
                                          (mem e1 l.l /\ mem e2 a.l /\ get_id e1 <> get_id e2) \/
                                          (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2))));

  merge : s0:s
          -> ltr:ae op
          -> l:s
          -> atr:ae op
          -> a:s
          -> btr:ae op
          -> b:s
          -> Pure s (requires (sim s0 ltr l /\ sim l atr a /\ sim l btr b) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e btr.l ==> not (member (get_id e) ltr.l)))
                   (ensures (fun res -> true));

  prop_merge : s0:s
               -> ltr:ae op
               -> l:s
               -> atr:ae op
               -> a:s
               -> btr:ae op
               -> b:s
               -> Lemma (requires (sim s0 ltr l /\ sim l atr a /\ sim l btr b) /\
                                 (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                                 (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                                 (forall e. mem e btr.l ==> not (member (get_id e) ltr.l)))
                       (ensures (sim s0 (absmerge ltr atr btr) (merge s0 ltr l atr a btr b)));

 append : tr:ae op
           -> o:(nat * op)
           -> Pure (ae op)
             (requires (not (member (get_id o) tr.l)))
             (ensures (fun res -> (forall e. mem e res.l <==> mem e tr.l \/ e = o) /\
                               (forall e1 e2. (mem e1 res.l /\ mem e2 res.l /\ get_id e1 <> get_id e2 /\ res.vis e1 e2) <==>
                                         (mem e1 tr.l /\ mem e2 tr.l /\ get_id e1 <> get_id e2 /\ tr.vis e1 e2) \/
                                         (mem e1 tr.l /\ e2 = o /\ get_id e1 <> get_id e2))));

 prop_oper : s0:s
              -> tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim s0 tr st) /\
                                (not (member (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> mem op (append tr op).l /\ (append tr op).vis e op))
                      (ensures (sim s0 (append tr op) (app_op st op)));

 convergence : s0:s
                -> tr:ae op
                -> a:s
                -> b:s
                -> Lemma (requires (sim s0 tr a /\ sim s0 tr b))
                        (ensures (a = b));

 // diff : a:ae op
 //         -> l:ae op
 //         -> Pure (ae op)
 //          (requires (forall e. mem e l.l ==> mem e a.l) /\
 //                    (forall e e1. mem e l.l /\ mem e1 l.l /\ l.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
 //                    (forall e e1. (mem e l.l /\ mem e1 a.l ==> mem e a.l /\ a.vis e e1)))
 //          (ensures (fun d -> (forall e. mem e d.l <==> mem e a.l /\ not(mem e l.l)) /\
 //                          (forall e. mem e d.l ==> not (member (get_id e) l.l)) /\
 //                          (diff_prop) /\
 //                          (forall e e1. mem e d.l /\ mem e1 d.l /\ d.vis e e1 ==> mem e a.l /\ mem e1 a.l /\ a.vis e e1) /\
 //                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1)) ==> (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1))) /\
 //                          (forall e e1. (mem e d.l /\ mem e1 d.l /\ not (d.vis e e1 || d.vis e1 e)) ==>
 //                                   (mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e))))) (decreases l);

 //  union :  a:ae op
 //          -> b:ae op
 //          -> Pure (ae op)
 //            (requires (forall e. (mem e a.l ==> not (member (get_id e) b.l))) /\
 //                            (forall e. (mem e b.l ==> not (member (get_id e) a.l))))
 //            (ensures (fun u ->
 //                            (forall e. mem e u.l <==> mem e a.l \/ mem e b.l) /\
 //                            (union_prop) /\
 //                            (forall e e1. (mem e u.l /\ mem e1 u.l /\ u.vis e e1) <==>
 //                                     ((mem e a.l /\ mem e1 a.l /\ a.vis e e1) \/ (mem e b.l /\ mem e1 b.l /\ b.vis e e1))) /\
 //                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
 //                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1) ==> mem e u.l /\ mem e1 u.l /\ not (u.vis e e1)) /\
 //                            (forall e e1. mem e a.l /\ mem e1 a.l /\ not (a.vis e e1 || a.vis e1 e) ==>
 //                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e)) /\
 //                            (forall e e1. mem e b.l /\ mem e1 b.l /\ not (b.vis e e1 || b.vis e1 e) ==>
 //                                     mem e u.l /\ mem e1 u.l /\ not (u.vis e e1 || u.vis e1 e))))

}
