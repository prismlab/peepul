module Library
module L = FStar.List.Tot

open FStar.Tactics
module T = FStar.Tactics
open FStar.Tactics.Typeclasses
  
class datatype (state:eqtype) (operation:eqtype) = {
    apply_op : state -> operation -> state
}

class mrdt (s:eqtype) (o:eqtype) (m : datatype s o) = {

  sim : a:s
      -> tr:list o
      -> b:s
      -> Tot bool;

  visib : list o
        -> o
        -> o
        -> bool;

  union : l:list o
        -> a:list o
        -> b:list o
        -> list o;
      
  merge : init:s
        -> ltr:list o
        -> l:s
        -> atr:list o
        -> a:s
        -> btr:list o
        -> b:s
        -> Pure s (requires (sim init ltr l /\ sim l atr a /\ sim l btr b) /\ 
             (forall o1 o2 o3. L.mem o1 ltr /\ L.mem o2 atr /\ L.mem o3 btr ==> visib (union ltr atr btr) o1 o2 /\ visib (union ltr atr btr) o1 o3) /\ 
             (forall o1 o2. (visib ltr o1 o2 ==> visib atr o1 o2 /\ visib btr o1 o2)))
             (ensures (fun res -> true));

  prop : init: s 
       -> ltr:list o
       -> l:s 
       -> atr:list o 
       -> a:s
       -> btr:list o
       -> b:s 
       -> Lemma (ensures (sim init ltr l /\ sim l atr a /\ sim l btr b) /\ 
            (forall o1 o2 o3. L.mem o1 ltr /\ L.mem o2 atr /\ L.mem o3 btr ==> visib (union ltr atr btr) o1 o2 /\ visib (union ltr atr btr) o1 o3) /\ 
            (forall o1 o2. (visib ltr o1 o2 ==> visib atr o1 o2 /\ visib btr o1 o2))
             ==> (sim init (union ltr atr btr) (merge init ltr l atr a btr b)));
                
  convergence : init:s 
              -> tr:list o
              -> a:s
              -> b:s 
              -> Lemma (requires (sim init tr a /\ sim init tr b))
                      (ensures (a = b))
}

