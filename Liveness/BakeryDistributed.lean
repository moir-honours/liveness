import Veil

-- source: https://members.loria.fr/SMerz/papers/distributed-bakery/BakeryDistributed.tla


veil module BakeryDistributed

type node


@[veil_decl] structure Message (node : Type) where
  payload : node
  src : node
  dst : node


end BakeryDistributed
