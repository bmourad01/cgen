let target = Target.create ()
    ~name:"amd64-sysv"
    ~word:`i64
    ~little:true

module Machine = struct
  let lower_abi = Sysv.run
end

let () =
  Context.register_machine target (module Machine)
