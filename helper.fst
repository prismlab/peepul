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

type v = (o:eqtype{exists op. subtype_of o (nat * op)})

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

// class mrdt_props (op:eqtype) (s:eqtype) = {
// Will contain the verification conditions for diff, union, abs_merge, merge and prop_merge
//   }
