import Veil
import Veil.Liveness

-- source: https://members.loria.fr/SMerz/papers/distributed-bakery/BakeryDistributed.tla




veil module BakeryDeconstructed

type process
type sequence_t

/-  As explained in Lamport's paper, there are 1 through N main processes.
    Each process i has N - 1 subprocesses j ≠ i for reading, and N - 1
    processes for writing.

-/
enum pc_main = {ncs, M, M0, L, cs, p}
enum pc_sub = {ch, test, Lb, L2, L3 }
enum pc_wr = {wr}

instantiate sequence : TotalOrderWithZero sequence_t
instantiate thread : TotalOrderWithZero process


relation unchecked: process → process → Bool

immutable individual one_th: process
immutable individual one: sequence_t

/- Variables -/
function number   : process → sequence_t
function localNum : process → process → ℕ
function localCh  : process → process → ℕ

function v  : process → ℕ


function mainPc : process → pc_main
function subPc  : process → process → pc_sub
function wrPc   : process → process → pc_wr

relation unRead  : process → process → Bool



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



/- Initial State -/
after_init {
    /- Global Variables-/
    number P := sequence.zero
    localNum P Q := 0
    localCh P Q := 0

    /- Process Main -/
    unRead P Q := false
    v P := 0

    mainPc P := ncs
    subPc  P Q := ch
    wrPc   P Q := wr

}


/- Non Critical State -/
action NCS (self: process) {
    require mainPc self = ncs
    mainPc self := M
}

/- Announce I is choosing -/
action M (self: process) {
    require mainPc self = M
    require ∀ q, q ≠ self → subPc self q = test

    mainPc self := M0
}


/- Read tickets and choose new ticket val -/
action M0 (self: process) {
    require mainPc self = M0

    if (∃ i, unRead self i) then
      let i :| unRead self i
      unRead self i := false



      mainPc self := M0
    else
      mainPc self := ncs
}

/- Wait for comparisons -/
-- action L ()

-- action cs

/- Release ticket -/
-- action p





end BakeryDeconstructed
