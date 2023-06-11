open Regular.Std

type t = private int

include Regular.S with type t := t
