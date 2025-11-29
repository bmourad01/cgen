open Core
open Regular.Std
open Virtual

include Egraph_common

module Rule = Egraph_rule
module Subst = Egraph_subst
module Builder = Egraph_builder

type rule = Rule.t

let init input depth_limit match_limit rules = {
  input;
  classes = Uf.create ();
  memo = Hashtbl.create (module Enode);
  node = Vec.create ();
  typs = Vec.create ();
  lmoved = Label.Table.create ();
  imoved = Vec.create ();
  pinned = Z.zero;
  ilbl = Vec.create ();
  lval = Label.Table.create ();
  depth_limit;
  match_limit;
  rules;
}

let check_ssa fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    Ok ()
  else
    Input.E.failf "Expected SSA form for function $%s"
      (Func.name fn) ()

let debug_dump t =
  Logs.debug (fun m ->
      let pp_lmoved ppf (l, s) =
        Format.fprintf ppf "  %a: %s%!" Label.pp l
          (Iset.to_list s |>
           List.to_string ~f:Id.to_string) in
      let pp_sep ppf () = Format.fprintf ppf "\n" in
      m "%s: $%s lmoved:\n%a%!"
        __FUNCTION__ (Func.name t.input.fn)
        (Format.pp_print_list ~pp_sep pp_lmoved)
        (Hashtbl.to_alist t.lmoved));
  Logs.debug (fun m ->
      let pp_lmoved ppf (id, s) =
        Format.fprintf ppf "  %d: %s%!" id
          (Lset.to_list s |>
           List.to_string ~f:Label.to_string) in
      let pp_sep ppf () = Format.fprintf ppf "\n" in
      m "%s: $%s imoved:\n%a%!"
        __FUNCTION__ (Func.name t.input.fn)
        (Format.pp_print_list ~pp_sep pp_lmoved)
        (Vec.to_sequence_mutable t.imoved |>
         Seq.mapi ~f:Tuple2.create |>
         Seq.to_list));
  Logs.debug (fun m ->
      let pp_ilbl ppf (id, l) =
        Format.fprintf ppf "  %d: %a%!" id
          (Format.pp_print_option
             ~none:(fun ppf () -> Format.fprintf ppf "<none>")
             Label.pp) (Uopt.to_option l) in
      let pp_sep ppf () = Format.fprintf ppf "\n" in
      m "%s: $%s ilbl:\n%a%!"
        __FUNCTION__ (Func.name t.input.fn)
        (Format.pp_print_list ~pp_sep pp_ilbl)
        (Vec.to_sequence_mutable t.ilbl |>
         Seq.mapi ~f:Tuple2.create |>
         Seq.to_list))

let run ?(depth_limit = 6) ?(match_limit = 20) fn tenv rules =
  let open Context.Syntax in
  let*? () = check_ssa fn in
  let*? input = Input.init fn tenv in
  let t = init input depth_limit match_limit rules in
  let*? () = Builder.run t in
  debug_dump t;
  let ex = Extractor.init t in
  Extractor.cfg ex
