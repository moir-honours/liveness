import Veil
import Veil.Liveness

-- source: https://members.loria.fr/SMerz/papers/distributed-bakery/BakeryDistributed.tla


veil module BakeryDeconstructed

type process
type sequence_t
enum state = {ncs, M, M0, L, cs, p, Lb, L2, L3}

instantiate sequence : TotalOrderWithZero sequence_t
instantiate thread : TotalOrderWithZero process



immutable individual one_th: process
immutable individual one: sequence_t

/- Variables -/
function number   : process → sequence_t
function pc : process → state

function localNum : process → process → ℕ
function localCh  : process → process → ℕ
function unRead  : process → process → ℕ
function v  : process → ℕ

#gen_state


/- Ticket number lt -/
theory ghost relation lt (x y : sequence_t) :=
    sequence.le x y ∧ x ≠ y

theory ghost relation next (x y : sequence_t) :=
    (lt x y ∧ ∀ z, lt x z → sequence.le y z)


/- Process number lt -/
theory ghost relation lt_thread (x y : process) :=
    (thread.le x y ∧ x ≠ y)

theory ghost relation next_thread (x y : process) :=
    (lt_thread x y ∧ ∀ z, lt_thread x z → thread.le y z)

/- Is (num[i], i) < (num[j], j) -/

ghost relation prec (a1 b1 : sequence_t) (a2 b2 : process) :=
  lt a1 b1 ∨ (a1 = b1 ∧ lt_thread a2 b2)

assumption [zero_one_th] next_thread thread.zero one_th
assumption [one_index_th] ∀i, thread.le thread.zero i
assumption [nat_gt_zero] ∀n, sequence.le sequence.zero n
assumption [zero_one] next sequence.zero one



after_init {
    number P := sequence.zero
    localNum P Q := 0
    localCh P Q := 0
    v P := 0
    pc P := ncs

}

action NCS (self: process) {
    require pc self = ncs
    pc self := M
}

action M (self: process) {
    require pc self = M
}







end BakeryDeconstructed
