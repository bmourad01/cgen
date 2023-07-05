open Core
open Common

include Extractor_core

let term_exn t l = match Hashtbl.find t.eg.lbl2id l with
  | None -> None
  | Some id ->
    let id = find t.eg id in
    match extract t id with
    | None ->
      invalid_argf "Couldn't extract term for label %a (id %a)"
        Label.pps l Id.pps id ()
    | Some e -> match Extractor_term.exp e with
      | Some _ as e -> e
      | None ->
        invalid_argf
          "Term for label %a (id %a) is not well-formed: %a"
          Label.pps l Id.pps id pps_ext e ()

let term t l = Or_error.try_with @@ fun () -> term_exn t l
let reify = Extractor_reify.reify
