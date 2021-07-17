module Helper

open FStar.List.Tot

val member : #op:eqtype
           -> id:nat
           -> l:list (nat * op)
           -> Tot (b:bool{(exists n. mem (id,n) l) <==> b=true})

let rec member n l =
  match l with
  |[] -> false
  |(id,_)::xs -> (n = id) || member n xs


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
|A : vis : ((nat * op) -> (nat * op) -> Tot bool) -> l:list (nat * op) {unique l} -> ae op

assume val axiom : op: eqtype -> l:ae op
                 -> Lemma (ensures (forall e e' e''. (mem e l.l /\ mem e' l.l /\ mem e'' l.l /\ get_id e <> get_id e' /\
                   get_id e' <> get_id e'' /\ get_id e <> get_id e'' /\ l.vis e e' /\ l.vis e' e'') ==> l.vis e e'') (*transitive*)/\
                     (forall e e'. (mem e l.l /\ mem e' l.l /\ get_id e <> get_id e' /\ l.vis e e') ==> not (l.vis e' e)) (*asymmetric*) /\
                     (forall e. mem e l.l ==> not (l.vis e e) (*irreflexive*)))
                         [SMTPat (unique l.l)]

let sim_type (op:eqtype) (s:eqtype) (sim_prop:s -> (ae op) ->s -> bool -> prop) =  s0:s
                                                                               -> tr:ae op
                                                                               -> s1:s
                                                                               -> Tot (b:bool{ sim_prop s0 tr s1 b })
let abs_merge_type (op:eqtype) = l:ae op
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
                                          (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2))))

let merge_type (op:eqtype) (s:eqtype) (sim_prop: s -> (ae op) -> s -> bool -> prop) 
               (sim: (s0:s) -> (tr:ae op)  -> (s1:s) -> Tot (b:bool{ sim_prop s0 tr s1 b })) =  s0:s
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
                   (ensures (fun res -> true))

let prop_merge_type (op:eqtype) (s:eqtype) (sim_prop: s -> (ae op) -> s -> bool -> prop) 
                    (sim: (s0:s) -> (tr:ae op)  -> (s1:s) -> Tot (b:bool{ sim_prop s0 tr s1 b })) 
                      (merge : (s0:s) -> (ltr: ae op) -> (l:s) -> (atr:ae op) -> (a:s) -> (btr:ae op) -> (b:s)
                             -> Pure s (requires (sim s0 ltr l /\ sim l atr a /\ sim l btr b) /\
                             (forall e. mem e ltr.l ==> not (member (get_id e) atr.l)) /\
                             (forall e. mem e atr.l ==> not (member (get_id e) btr.l)) /\
                             (forall e. mem e btr.l ==> not (member (get_id e) ltr.l)))
                             (ensures (fun res -> true)))
                       (absmerge : (l:ae op) -> (a:ae op) -> (b:ae op) 
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
                                          (mem e1 l.l /\ mem e2 b.l /\ get_id e1 <> get_id e2)))))
               = s0:s
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
                       (ensures (sim s0 (absmerge ltr atr btr) (merge s0 ltr l atr a btr b)))

let append_type (op:eqtype) = tr:ae op
           -> o:(nat * op)
           -> Pure (ae op)
             (requires (not (member (get_id o) tr.l)))
             (ensures (fun res -> (forall e. mem e res.l <==> mem e tr.l \/ e = o) /\
                               (forall e1 e2. (mem e1 res.l /\ mem e2 res.l /\ get_id e1 <> get_id e2 /\ res.vis e1 e2) <==>
                                         (mem e1 tr.l /\ mem e2 tr.l /\ get_id e1 <> get_id e2 /\ tr.vis e1 e2) \/
                                         (mem e1 tr.l /\ e2 = o /\ get_id e1 <> get_id e2))))

let prop_oper_type (op:eqtype) (s:eqtype) (app_op:s -> (nat * op) -> s) (sim_prop: s -> (ae op) -> s -> bool -> prop)
                    (sim: (s0:s) -> (tr:ae op)  -> (s1:s) -> Tot (b:bool{ sim_prop s0 tr s1 b }))
                    (append: (tr:ae op) -> (o:(nat * op))
                             -> Pure (ae op)
                             (requires (not (member (get_id o) tr.l)))
                             (ensures (fun res -> (forall e. mem e res.l <==> mem e tr.l \/ e = o) /\
                               (forall e1 e2. (mem e1 res.l /\ mem e2 res.l /\ get_id e1 <> get_id e2 /\ res.vis e1 e2) <==>
                                         (mem e1 tr.l /\ mem e2 tr.l /\ get_id e1 <> get_id e2 /\ tr.vis e1 e2) \/
                                         (mem e1 tr.l /\ e2 = o /\ get_id e1 <> get_id e2)))))
              = s0:s
              -> tr:ae op
              -> st:s
              -> op:(nat * op)
              -> Lemma (requires (sim s0 tr st) /\
                                (not (member (get_id op) tr.l)) /\
                                (forall e. mem e tr.l ==> mem op (append tr op).l /\ (append tr op).vis e op))
                      (ensures (sim s0 (append tr op) (app_op st op)))

