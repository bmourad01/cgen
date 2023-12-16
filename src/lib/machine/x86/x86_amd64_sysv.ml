open Core

let target = Target.create ()
    ~name:"amd64-sysv"
    ~word:`i64
    ~little:true

module Machine = struct
  type gpr = [
    | `rax
    | `rcx
    | `rdx
    | `rbx
    | `rsi
    | `rdi
    | `rsp
    | `rbp
    | `r8
    | `r9
    | `r10
    | `r11
    | `r12
    | `r13
    | `r14
    | `r15
  ] [@@deriving compare, equal, sexp]

  let pp_gpr ppf gpr =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_gpr gpr)

  type sse = [
    | `xmm0
    | `xmm1
    | `xmm2
    | `xmm3
    | `xmm4
    | `xmm5
    | `xmm6
    | `xmm7
    | `xmm8
    | `xmm9
    | `xmm10
    | `xmm11
    | `xmm12
    | `xmm13
    | `xmm14
    | `xmm15
  ] [@@deriving compare, equal, sexp]

  let pp_sse ppf sse =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_sse sse)

  type reg = [
    | gpr
    | sse
  ] [@@deriving compare, equal, sexp]

  let pp_reg ppf r =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_reg r)

  let lower_abi = Sysv.run
end

let () =
  Context.register_machine target (module Machine)
