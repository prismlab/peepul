open Lwt.Syntax
open Lwt.Infix
open Irmin.Merge.Infix

module Store = Irmin_mem.KV(Ictr)

let config = Irmin_mem.config ()
let author = "Adharsh <adharsh@abc.com>"
let info fmt = Irmin_unix.info ~author fmt

let _ = Random.self_init ()

let rec print_path path acc = match path with
  | [] -> acc
  | x::xs -> print_path xs (acc ^ "/" ^ x)

let incr store path =
  let info = info "incrementing counter at %s" (print_path path "") in
  let* ctr = Store.get store path in
  Store.set_exn store path (fst (Ictr.do1 ctr ((Random.int 1000000), Ictr.Add))) ~info

let main =
  let path = [ "foo"; "bar" ] in
  let* repo = Store.Repo.v config in
  let* t = Store.master repo in
  let* t1 = Store.of_branch repo "temp" in
  let* () = Store.set_exn t ~info:(info "Initializing foo/bar") path 0 in
  let* () = Store.set_exn t1 ~info:(info "Initializing foo/bar") path 0 in
  let* _ = incr t path in
  let* _ = incr t1 path in
  let* _ = incr t path in
  let* _ = incr t1 path in
  let* _ = incr t1 path in
  let* _ = incr t path in
  let* _ = incr t1 path in
  let* _ = incr t1 path in
  let* _ = incr t path in
  let* _ = incr t path in
  let* a = Store.get t [ "foo"; "bar" ] in
  let* b = Store.get t1 [ "foo"; "bar" ] in
  let* _ = Store.merge_into ~into:t t1 ~info:(info "Merging T1 into T") in
  let+ m = Store.get t1 [ "foo"; "bar" ] in
  Printf.printf "Value of the counters before merge: A = %d, B = %d \nValue after merge: result = %d\n" a b m

let () = Lwt_main.run main

