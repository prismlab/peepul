module Icounter

open FStar.List.Tot
open Library

type o =
    | Inc : nat -> o

type s = nat
       
val app_op : s -> o -> s
let app_op s (Inc n) = s + n

instance icounter : datatype s o = {
   Library.apply_op = app_op
}

val vis : o -> o -> Tot bool
let vis a b = admit()

val visib : l:list o -> o1:o -> o2:o -> bool
let visib l o1 o2 = mem o1 l && mem o2 l && vis o1 o2

val sum : list o -> nat
let rec sum l =
    match l with
    |[] -> 0
    |(Inc n)::xs -> n + sum xs
    
val sim : s0:s
        -> tr:list o
        -> s1:s 
        -> Tot bool           
let sim s0 tr s1 = 
        s1 = s0 + sum tr  


val union : l:list o 
          -> a:list o
          -> b:list o
          -> list o          
let rec union l a b = 
    match l,a,b with
    |[],[],[] -> []
    |x::xs, _, _ -> x::(union xs a b)
    |[],x::xs,_ -> x::(union [] xs b)
    |[],[],_ -> b

assume val axiom : l:list o -> a:list o -> b:list o
                 -> Lemma (ensures (forall o1 o2. visib (union l a b) o1 o2 ==> visib l o1 o2 \/ visib a o1 o2 \/ visib b o1 o2)) [SMTPat (union l a b)]

val merge : init:s
          -> ltr:list o
          -> l:s
          -> atr:list o 
          -> a:s 
          -> btr:list o 
          -> b:s 
          -> Pure s (requires (sim init ltr l /\ sim l atr a /\ sim l btr b) /\ 
                   (forall o1 o2 o3. mem o1 ltr /\ mem o2 atr /\ mem o3 btr ==> 
                      visib (union ltr atr btr) o1 o2 /\ visib (union ltr atr btr) o1 o3) /\ 
                   (forall o1 o2. (visib ltr o1 o2 ==> visib atr o1 o2 /\ visib btr o1 o2)))
                   (ensures (fun res -> true))
let merge init ltr l atr a btr b = 
    a + b - l


val lemma1 : l:list o
           -> a:list o
           -> b:list o
           -> Lemma (ensures (forall ele. mem ele (union l a b) <==> mem ele l \/ mem ele a \/ mem ele b) /\ (sum (union l a b) = sum l + sum a + sum b)) (decreases %[l;a;b])           
let rec lemma1 l a b = 
  match l,a,b with
  |[],[],[] -> ()
  |x::xs, _, _ -> lemma1 xs a b
  |[],x::xs,_ -> lemma1 [] xs b
  |[],[],x::xs -> lemma1 [] [] xs


val prop : init:s
         -> ltr: list o
         -> l:s 
         -> atr:list o 
         -> a:s 
         -> btr:list o
         -> b:s 
         -> Lemma (ensures (sim init ltr l /\ sim l atr a /\ sim l btr b) /\ 
                 (forall o1 o2 o3. mem o1 ltr /\ mem o2 atr /\ mem o3 btr ==> 
                     visib (union ltr atr btr) o1 o2 /\ visib (union ltr atr btr) o1 o3) /\ 
                 (forall o1 o2. (visib ltr o1 o2 ==> visib atr o1 o2 /\ visib btr o1 o2)) ==> 
                 (sim init (union ltr atr btr) (merge init ltr l atr a btr b)))                
let prop init ltr l atr a btr b = 
  lemma1 ltr atr btr; ()

val convergence : init:s 
                -> tr:list o
                -> a:s 
                -> b:s 
                -> Lemma (requires (sim init tr a /\ sim init tr b))
                        (ensures (a = b))
let convergence inir tr a b = ()


instance _ : mrdt s o icounter = {
    Library.sim = sim;
    Library.visib = visib;
    Library.union = union;
    Library.merge = merge;
    Library.prop = prop;
    Library.convergence = convergence
  }
