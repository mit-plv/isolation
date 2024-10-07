type machine_id_t =
  | Impl
  | Spec

type reglist =
  | RegList of int list
  | RegRange of int * int
type expr =
  | Query of machine_id_t * reglist * int
  | Stop
