open Lwt.Syntax
open Lwt.Infix
open Irmin.Merge.Infix

module Store = Irmin_mem.KV(Orset_opt_detailed)

let config = Irmin_mem.config ()
let author = "Adharsh <adharsh@abc.com>"
let info fmt = Irmin_unix.info ~author fmt

let _ = Random.self_init ()

let add store path value =
  let info = info "added %d" value in
  let* set = Store.get store path in
  Store.set_exn store path (Orset_opt_detailed.app_op set (Random.int 10000, Orset_opt_detailed.Add, value)) ~info

let remove store path value =
  let info = info "removed %d" value in
  let* set = Store.get store path in
  Store.set_exn store path (Orset_opt_detailed.app_op set (Random.int 10000, Orset_opt_detailed.Rem, value)) ~info

let rec print_tuples =
  function
  | [] -> ()
  | (a, b) :: xs ->
    Printf.printf "%d; " b;
    print_tuples xs

let main =
  let path = [ "foo"; "bar" ] in
  let* repo = Store.Repo.v config in
  let* t = Store.master repo in

  let* () = Store.set_exn t ~info:(info "Initializing foo/bar") path [] in

  let* _ = add t path 100 in
  let* _ = add t path 200 in
  let* _ = add t path 300 in
  let* _ = remove t path 100 in
  let* _ = add t path 500 in

  let+ x = Store.get t [ "foo"; "bar" ] in
  print_tuples x

let () = Lwt_main.run main

