import Veil
import Veil.Liveness

veil module Bakery

type process
type sequence_t

enum pc_state = { ncs, e1, e2, e3, e4, w1, w2, cs, exit }

instantiate sequence : TotalOrderWithZero sequence_t
instantiate thread : TotalOrderWithZero process

immutable individual one_th: process
immutable individual one: sequence_t

-- relation number: process → sequence_t → Bool
function number : process → sequence_t
function flag : process → Bool

/- Local variables -/
relation unchecked: process → process → Bool
function max : process → sequence_t
function nxt : process → process
function pc : process → pc_state

#gen_state

theory ghost relation lt (x y : sequence_t) := (sequence.le x y ∧ x ≠ y)
theory ghost relation next (x y : sequence_t) := (lt x y ∧ ∀ z, lt x z → sequence.le y z)

theory ghost relation lt_thread (x y : process) := (thread.le x y ∧ x ≠ y)
theory ghost relation next_thread (x y : process) := (lt_thread x y ∧ ∀ z, lt_thread x z → thread.le y z)



assumption [zero_one_th] next_thread thread.zero one_th
assumption [one_index_th] ∀i, thread.le thread.zero i
assumption [nat_gt_zero] ∀n, sequence.le sequence.zero n
assumption [zero_one] next sequence.zero one


ghost relation vCritical (v : process) :=
  (pc v = cs)

ghost relation prec (a1 b1 : sequence_t) (a2 b2 : process) :=
  (lt a1 b1 ∨ (a1 = b1 ∧ lt_thread a2 b2))

 ghost relation number_gt_zero (i : process) := lt sequence.zero (number i)

ghost relation pc_ncs_e1_exit (j : process) := pc j = ncs ∨ pc j = e1 ∨ pc j = exit

ghost relation pc_ex (i j : process) :=
  pc j = e2 ∧ (unchecked j i ∨ (sequence.le (number i) (max j)))

ghost relation pc_e3 (i j : process) :=
  pc j = e3 ∧ (sequence.le (number i) (max j))

ghost relation pc_e4_w1_w2 (i j : process) :=
  (pc j = e4 ∨ pc j = w1 ∨ pc j = w2) ∧
  (prec (number i) (number j) i j) ∧
  (pc j = w1 ∨ pc j = w2 → unchecked j i)

ghost relation before (i j : process) :=
  number_gt_zero i ∧ (pc_ncs_e1_exit j ∨ pc_ex i j ∨ pc_e3 i j ∨ pc_e4_w1_w2 i j)

after_init {
  number P := sequence.zero
  flag P := false
  unchecked P Q := false
  max P := sequence.zero
  nxt P := thread.zero
  pc P := ncs
}


action evtNCS (self : process) {
  require pc self = ncs
  pc self := e1
}

action evtE1_branch1 (self : process) {
  require pc self = e1
  flag self := !(flag self)
  pc self := e1
}



action _evtE1_branch2 (self : process) {
  require pc self = e1
  flag self := true
  -- unchecked self self := false
  unchecked self Q := if Q = self then false else true
  max self := sequence.zero
  pc self := e2
}


action evtE2 (self : process) {
  require pc self = e2
  if (∃i, unchecked self i) then
    let i :| unchecked self i
    unchecked self i := false
    let number_i := number i
    let max_self := max self
    if lt max_self number_i then
      max self := number_i
    pc self := e2
  else
    pc self := e3
}


action evtE3_branch1 (self : process) {
  require pc self = e3
  let k ← pick sequence_t
  number self := k
  pc self := e3
}


action evtE3_branch2 (self : process) {
  require pc self = e3
  let max_self := max self
  let j ← pick sequence_t
  assume lt max_self j
  number self := j
  pc self := e4
}

action evtE4_branch1 (self : process) {
  require pc self = e4
  flag self := !flag self
  pc self := e4
}


action evtE4_branch2 (self : process) {
  require pc self = e4
  flag self := false
  unchecked self Q := if Q = self then false else true
  pc self := w1
}


action evtW1 (self : process) {
  require pc self = w1
  if (∃i, unchecked self i) then
    let i ← pick process
    assume unchecked self i
    nxt self := i
    require ¬ flag i
    pc self := w2
  else
    pc self := cs
}



action evtW2 (self : process) {
  require pc self = w2
  let nxt_self := nxt self
  let number_self := number self
  let number_nxt_self := number nxt_self
  require (number_nxt_self = sequence.zero) ∨ (prec number_self number_nxt_self self nxt_self)
  unchecked self nxt_self := false
  pc self := w1
}



action evtCS (self : process) {
  require pc self = cs
  pc self := exit
}


action evtExit_branch1 (self : process) {
  require pc self = exit
  let k ← pick sequence_t
  number self := k
  pc self := exit
}

action evtExit_branch2 (self : process) {
  require pc self = exit
  number self := sequence.zero
  pc self := ncs
}



invariant [p1_non_zero_number] pc I = e4 ∨ pc I = w1 ∨ pc I = w2 ∨ pc I = cs → ¬(number I = sequence.zero)
invariant [p2_flag_e2_e3] pc I = e2 ∨ pc I = e3 → flag I
invariant [p3_nxt_not_self] pc I = w2 → ¬ (nxt I = I)
invariant [p4_unchecked_not_self] pc I = w1 ∨ pc I = w2 → ¬(unchecked I I)
invariant [p5_critical_section] pc I = w1 ∨ pc I = w2 → ∀j, (j ≠ I ∧ ¬unchecked I j) → before I j
invariant [p6_nxt_e2_e3]
  pc I = w2 ∧
  ((pc (nxt I) = e2 ∧ ¬unchecked (nxt I) I) ∨ (pc (nxt I) = e3)) →
    (sequence.le (number I) (max (nxt I)))
invariant [p7_cs_precedes_all] pc I = cs → ∀j, (j ≠ I) → before I j

/- Ensures no two processes are in critical section simultaneously. -/
safety [mutual_exclusion] pc I = cs ∧ pc J = cs → I = J

set_option maxHeartbeats 2500000

#gen_spec

#check_invariants

#print State.Label

-- theorem enter_mutex : ∀ (st st' : State),
--   assumptions st → inv st → evtW2 st st' → mutual_exclusion st' := by

--   sorry


temporal [success] ∀ x : process, 𝒲ℱ (evtW2 x) → ◇ ⌜ vCritical x ⌝

prove_temporal_by [success]

  tstart hInit hNext hInv
  tclear hInv
  tdsimp only [success]
  intro hwf



  sorry


/-
Note that:
`process := Fin 2` corresponds to `N = 2`
`sequence_t := Fin 3` corresponds to Nat = `MaxNat = 2`

So the corresponding parameters here are:
`2-3`, `3-4`
-/
-- #model_check
-- { process := Fin 2,
--   sequence_t := Fin 3,
--   pc_state := pc_state_IndT }
-- { one_th := 1,
--   one := 1 }


end Bakery
