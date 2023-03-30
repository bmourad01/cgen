open Core
open Regular.Std

module Reg = struct
  module T = struct
    type t = {
      name  : string;
      width : int;
    } [@@deriving bin_io, compare, equal, hash, sexp]
  end

  include T

  let create ~name ~width = {name; width}
  let name r = r.name
  let width r = r.width

  let r1   = create ~width:1
  let r8   = create ~width:8
  let r16  = create ~width:16
  let r32  = create ~width:32
  let r64  = create ~width:64
  let r128 = create ~width:128

  include Regular.Make(struct
      include T
      let pp ppf r = Format.fprintf ppf "%s" r.name
      let version = "0.1"
      let hash = hash
      let module_name = Some "Cgen.Target.Reg"
    end)
end

type reg = Reg.t [@@deriving bin_io, compare, equal, hash, sexp]

module T = struct
  type t = {
    name   : string;
    word   : Type.imm_base;
    little : bool;
    flag   : Set.M(Reg).t;
    fp     : Set.M(Reg).t;
    gpr    : Set.M(Reg).t;
    sp     : reg;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let create
    ?(flag = [])
    ?(fp = [])
    ?(gpr = [])
    ~name
    ~word
    ~little
    ~sp
    () = {
  name;
  word;
  little;
  flag = Reg.Set.of_list flag;
  fp = Reg.Set.of_list fp;
  gpr = Reg.Set.of_list gpr;
  sp;
}

let name t = t.name
let word t = t.word
let bits t = Type.sizeof_imm_base t.word
let little t = t.little
let flag t = t.flag
let fp t = t.fp
let gpr t = t.gpr
let sp t = t.sp

let is_flag t r = Set.mem t.flag r
let is_fp t r = Set.mem t.fp r
let is_gpr t r = Set.mem t.flag r
let is_sp t r = Reg.equal t.sp r

include Regular.Make(struct
    include T
    let pp ppf t = Format.fprintf ppf "%s" t.name
    let version = "0.1"
    let hash = hash
    let module_name = Some "Cgen.Target"
  end)
