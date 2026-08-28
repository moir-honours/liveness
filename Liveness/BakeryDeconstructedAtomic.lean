import Veil
import Veil.Liveness

-- source: https://members.loria.fr/SMerz/papers/distributed-bakery/BakeryDistributed.tla

veil module BakeryDeconstructedAtomic

type process
type sequence_t

/-  As explained in Lamport's paper, there are 1 through N main processes.
    Each process i has N - 1 subprocesses j ≠ i for reading, and N - 1
    processes for writing.

-/
enum pc_main = {ncs, M, M0, L, cs, p}
enum pc_sub = {ch, test, Lb, L2, L3 }
enum pc_wr = {wr}

-- Sequence is for ticket numbers, thread is for process ids
instantiate sequence : TotalOrderWithZero sequence_t
instantiate thread : TotalOrderWithZero process

immutable individual one_th: process
immutable individual one: sequence_t

/- Variables -/
function number   : process → sequence_t
function localNum : process → process → sequence_t
relation localCh  : process → process → Bool
relation localQm  : process → process → Bool

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
    localNum P Q := sequence.zero
    localCh P Q := false
    localQm P Q := false

    /- Process Main -/
    unRead P Q := false
    v P := 0

    mainPc P := ncs
    subPc  P Q := ch
    wrPc   P Q := wr

}

-- (***************************************************************************)
-- (* Main Process States
-- (***************************************************************************)


/- Non Critical State -/
action evtNCS (self: process) {
    require mainPc self = ncs
    mainPc self := M
}

/- Announce I is choosing, pick next ticket -/
action evtM (self: process) {
    require mainPc self = M
    require ∀ other, other ≠ self → subPc self other = test

    let ticket ← pick sequence_t

    assume ticket ≠ sequence.zero

    assume ∀ other,
      other ≠ self →
        (¬localQm self other →
          lt (localNum self other) ticket)

    number self := ticket

    localQm OTHER self :=
      if OTHER = self then false else true

    mainPc self := L

}

/- Wait for comparisons -/
action evtL (self: process) {
  require mainPc self = L
  require ∀ q, q ≠ self → subPc self q = ch

  mainPc self := cs
}

-- action cs
action evtCs (self: process) {
  require mainPc self = cs
  mainPc self := p

}

action evtP (self: process) {
    require mainPc self = p

    number self := sequence.zero
    localNum OTHER self := sequence.zero
    localQm OTHER self := true
    mainPc self := ncs
}

-- (***************************************************************************)
-- (* Sub Process States
-- (***************************************************************************)


/- Raise choosing flag -/
action evtCh (self other: process) {
    require self ≠ other
    require subPc self other = ch
    require mainPc self = M

    localCh other self := true
    subPc self other := test
}

/-  Publish local ticket number -/
action evtTest (self other: process) {
    require self ≠ other
    require subPc self other = test
    -- require mainPc self = L

    localNum other self := number self
    subPc self other := Lb
}

/- Lower the choosing flag -/
action evtLb (self other: process) {
    require self ≠ other
    require subPc self other = Lb

    localCh other self := false
}

/- Wait for other processes to lower their choosing flag -/
action evtL2 (self other: process) {
    require self ≠ other
    require subPc self other = L2
    require localCh self other = false
    subPc self other := L3
}

action evtL3 (self other: process) {
    require self ≠ other
    require subPc self other = L3
    require (localNum self other ≠ sequence.zero ∧ localQm self other ≠ true) →
      prec (number self) (localNum self other) self other
}

-- (***************************************************************************)
-- (* Write Process State
-- (***************************************************************************)

/- Release ticket -/
action evtWr (self other: process) {
    require self ≠ other
    require wrPc self other = wr
    require localQm other self = true
    require mainPc self = M ∨ mainPc self = ncs

    localNum other self := sequence.zero
    localQm other self := false

    wrPc self other := wr
}


-- (***************************************************************************)
-- (* Invariants
-- (***************************************************************************)

invariant [critical_lowest]
  mainPc I = cs →
    ∀ J, J ≠ I →
      number J = sequence.zero ∨
      prec (number I) (number J) I J

invariant [critical_has_ticket]
    mainPc I = cs →
        number I ≠ sequence.zero

invariant [positive_ticket]
  mainPc I = cs → number I ≠ sequence.zero

safety [mutex] mainPc I = cs ∧ mainPc J = cs → I = J

set_option maxHeartbeats 2500000
#gen_spec
#check_invariants

#model_check
{ process := Fin 2,
  sequence_t := Fin 3,
  pc_main := pc_main_IndT,
  pc_sub  := pc_sub_IndT,
  pc_wr   := pc_wr_IndT }
{ one_th := 1,
  one := 1 }


end BakeryDeconstructedAtomic
