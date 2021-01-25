module Icounter

open FStar.List.Tot

module M = Mrdt

type oper =
       | Inc : nat -> oper
       
type trace = list oper

val app_op : s1:nat -> oper -> Tot (s2:nat {s2 >= s1}) 
let app_op s op = 
    match op with
    | (Inc n) -> s + n

val app_tr : s1:nat -> t:trace -> Tot (s2:nat {s2 >= s1}) (decreases t)
let rec app_tr s t =
    match t with
    | [] -> s
    | op::ops -> app_tr (app_op s op) ops


instance icounter_mrdt : M.mrdt nat oper = {
                                   M.apply_op = (fun (t:nat) (o:oper) -> app_op t o);
                                   M.apply_tr = (fun (t:nat) (tr:trace) -> app_tr t tr)}























