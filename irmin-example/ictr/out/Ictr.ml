(* open Prims *)
type s = int
type t = int [@@deriving irmin]
type op =
  | Add 
let (uu___is_Add : op -> bool) = fun projectee -> true
let (init : int) = 0
let pre_cond_op : 'uuuuu 'uuuuu1 . 'uuuuu -> 'uuuuu1 -> bool =
  fun s1 -> fun op1 -> true
let (app_op : s -> (int * op) -> s) =
  fun s1 -> fun op1 -> match op1 with | (uu___, Add) -> s1 + 1
let rec (sum : (int * op) list -> int) =
  fun l ->
    match l with
    | [] -> 0
    | (uu___, Add)::xs -> (sum xs) + 1
let (sim : op Library.ae -> s -> bool) =
  fun tr -> fun s1 -> s1 = (sum (Library.__proj__A__item__l tr))

let (pre_cond_merge1 : int -> int -> int -> bool) =
  fun l -> fun a -> fun b -> (a >= l) && (b >= l)
let (merge1 : s -> s -> s -> s) = fun l -> fun a -> fun b -> (a + b) - l
let pre_cond_merge :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    'uuuuu ->
      'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4 -> 'uuuuu5 -> bool
  = fun ltr -> fun l -> fun atr -> fun a -> fun btr -> fun b -> true
let (merge :
  op Library.ae -> s -> op Library.ae -> s -> op Library.ae -> s -> s) =
  fun ltr -> fun l -> fun atr -> fun a -> fun btr -> fun b -> merge1 l a b

let (uu___173 : (s, op) Library.mrdt) =
  {
    Library.init = init;
    Library.pre_cond_op = pre_cond_op;
    Library.app_op = app_op;
    Library.sim = sim;
    Library.pre_cond_merge = pre_cond_merge;
    Library.pre_cond_merge1 = pre_cond_merge1;
    Library.merge1 = merge1;
    Library.merge = merge;
    Library.prop_merge = ();
    Library.prop_oper = ();
    Library.convergence = ()
  }

let merge ~old a b =
	let open Irmin.Merge.Infix in
	old () >>=* fun old ->
  let _old = (match old with None -> 0 | Some l -> l) in
  Irmin.Merge.ok (merge1 _old a b)

let merge = Irmin.Merge.(option (v t merge))


