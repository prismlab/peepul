(* open Prims *)
type s = int
type t = int [@@deriving irmin]
type rval =
  | Val of s 
  | Bot 
let (uu___is_Val : rval -> bool) =
  fun projectee -> match projectee with | Val _0 -> true | uu___ -> false
let (__proj__Val__item___0 : rval -> s) =
  fun projectee -> match projectee with | Val _0 -> _0
let (uu___is_Bot : rval -> bool) =
  fun projectee -> match projectee with | Bot -> true | uu___ -> false
type op =
  | Add 
  | Rd 
let (uu___is_Add : op -> bool) =
  fun projectee -> match projectee with | Add -> true | uu___ -> false
let (uu___is_Rd : op -> bool) =
  fun projectee -> match projectee with | Rd -> true | uu___ -> false
let (init : int) = 0
let pre_cond_do : 'uuuuu 'uuuuu1 . 'uuuuu -> 'uuuuu1 -> bool =
  fun s1 -> fun op1 -> true
let pre_cond_prop_do :
  'uuuuu 'uuuuu1 'uuuuu2 . 'uuuuu -> 'uuuuu1 -> 'uuuuu2 -> bool =
  fun tr -> fun s1 -> fun op1 -> true
let (do1 : s -> (int * op) -> (s * rval)) =
  fun s1 ->
    fun op1 ->
      match op1 with
      | (uu___, Add) -> ((s1 + 1), Bot)
      | (uu___, Rd) -> (s1, (Val s1))
let rec (sum : (int * op) list -> int) =
  fun l ->
    match l with
    | [] -> 0
    | (uu___, Add)::xs -> (sum xs) + 1
    | (uu___, Rd)::xs -> sum xs
let (spec : (int * op) -> op Library.ae -> rval) =
  fun o ->
    fun tr ->
      match o with
      | (uu___, Add) -> Bot
      | (uu___, Rd) -> Val (sum (Library.__proj__A__item__l tr))
let (sim : op Library.ae -> s -> bool) =
  fun tr -> fun s1 -> s1 = (sum (Library.__proj__A__item__l tr))


let (pre_cond_merge : int -> int -> int -> bool) =
  fun l -> fun a -> fun b -> (a >= l) && (b >= l)
let pre_cond_prop_merge :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    'uuuuu ->
      'uuuuu1 -> 'uuuuu2 -> 'uuuuu3 -> 'uuuuu4 -> 'uuuuu5 -> bool
  = fun ltr -> fun l -> fun atr -> fun a -> fun btr -> fun b -> true
let (merge : s -> s -> s -> s) = fun l -> fun a -> fun b -> (a + b) - l





let (ictr : (s, op, rval) Library.mrdt) =
  {
    Library.init = init;
    Library.spec = spec;
    Library.sim = sim;
    Library.pre_cond_do = pre_cond_do;
    Library.pre_cond_prop_do = pre_cond_prop_do;
    Library.pre_cond_merge = pre_cond_merge;
    Library.pre_cond_prop_merge = pre_cond_prop_merge;
    Library.do1 = do1;
    Library.merge = merge;
    Library.prop_do = ();
    Library.prop_merge = ();
    Library.prop_spec = ();
    Library.convergence = ()
  }



let merge ~old a b =
	let open Irmin.Merge.Infix in
	old () >>=* fun old ->
 let _old = (match old with None -> 0 | Some l -> Printf.printf "Merge called %d %d %d\n" l a b;  l) in
  Irmin.Merge.ok (merge _old a b)

let merge = Irmin.Merge.(option (v t merge))
