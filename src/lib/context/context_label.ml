open Core
open Context_state

let init = Int63.(succ (Obj.magic Label.pseudoexit : t))

let fresh =
  let* s = M.get () in
  let l = s.nextlabel in
  let+ () = M.put {s with nextlabel = Int63.succ l} in
  (Obj.magic l : Label.t)
