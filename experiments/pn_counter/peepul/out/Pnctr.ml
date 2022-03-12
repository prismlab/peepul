open Prims
type s = Prims.int
type op =
  | Add 
  | Rem 
let (uu___is_Add : op -> Prims.bool) =
  fun projectee -> match projectee with | Add -> true | uu___ -> false
let (uu___is_Rem : op -> Prims.bool) =
  fun projectee -> match projectee with | Rem -> true | uu___ -> false
let (opa : (Prims.nat * op) -> Prims.bool) =
  fun op1 -> match op1 with | (id, Add) -> true | uu___ -> false
let (opr : (Prims.nat * op) -> Prims.bool) =
  fun op1 -> match op1 with | (id, Rem) -> true | uu___ -> false
let (app_op : s -> (Prims.nat * op) -> s) =
  fun s1 ->
    fun op1 ->
      match op1 with
      | (uu___, Add) -> s1 + Prims.int_one
      | (uu___, Rem) -> s1 - Prims.int_one
let (ctr : (s, op) Library.datatype) = { Library.app_op = app_op }
let rec (sum : (Prims.nat * op) Prims.list -> Prims.int) =
  fun l ->
    match l with
    | [] -> Prims.int_zero
    | (uu___, Add)::xs -> (sum xs) + Prims.int_one
    | (uu___, Rem)::xs -> (sum xs) - Prims.int_one
let (sim : op Library.ae -> s -> Prims.bool) =
  fun tr -> fun s1 -> s1 = (sum (Library.__proj__A__item__l tr))


let (merge1 : s -> s -> s -> s) = fun l -> fun a -> fun b -> (a + b) - l
let (merge :
  op Library.ae -> s -> op Library.ae -> s -> op Library.ae -> s -> s) =
  fun ltr -> fun l -> fun atr -> fun a -> fun btr -> fun b -> merge1 l a b



let (uu___185 : (s, op, unit) Library.mrdt) =
  {
    Library.sim = sim;
    Library.merge = merge;
    Library.prop_merge = ();
    Library.prop_oper = ();
    Library.convergence = ()
  }