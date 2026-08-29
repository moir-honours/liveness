import Veil
import Veil.Liveness

veil module Bakery

type process
type sequence_t


-- Process states
enum pc_main = { ncs, e1, e2, e3, e4, w1, w2, cs, exit }

-- Sequence is for ticket numbers, thread is for process ids
instantiate sequence : TotalOrderWithZero sequence_t
instantiate thread : TotalOrderWithZero process

immutable individual one_th: process
immutable individual one: sequence_t

/- Variables -/
function number : process → sequence_t
function flag : process → Bool
relation unchecked: process → process → Bool
function max : process → sequence_t
function nxt : process → process
function pc : process → pc_main

#gen_state

-- Ticket number less than
theory ghost relation lt (x y : sequence_t) := (sequence.le x y ∧ x ≠ y)
theory ghost relation next (x y : sequence_t) := (lt x y ∧ ∀ z, lt x z → sequence.le y z)

-- Process id less than
theory ghost relation lt_thread (x y : process) := (thread.le x y ∧ x ≠ y)
theory ghost relation next_thread (x y : process) := (lt_thread x y ∧ ∀ z, lt_thread x z → thread.le y z)

assumption [zero_one_th] next_thread thread.zero one_th
assumption [one_index_th] ∀i, thread.le thread.zero i
assumption [nat_gt_zero] ∀n, sequence.le sequence.zero n
assumption [zero_one] next sequence.zero one


ghost relation vCritical (v : process) :=
  (pc v = cs)

ghost relation vNotCritical (v : process) :=
  (pc v ≠ cs)

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



-- Initial State
after_init {
  number P := sequence.zero
  flag P := false
  unchecked P Q := false
  max P := sequence.zero
  nxt P := thread.zero
  pc P := ncs
}

-- Non Critical State
action evtNCS (self : process) {
  require pc self = ncs
  pc self := e1
}

/- Doorway starts -/

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

/- Doorway Ends -/


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



invariant [p1_non_zero_number]
  pc I = e4 ∨ pc I = w1 ∨ pc I = w2 ∨ pc I = cs →
    ¬(number I = sequence.zero)

invariant [p2_flag_e2_e3]
  pc I = e2 ∨ pc I = e3 →
    flag I

invariant [p3_nxt_not_self]
  pc I = w2 →
    ¬(nxt I = I)

invariant [p4_unchecked_not_self]
  pc I = w1 ∨ pc I = w2 →
    ¬(unchecked I I)

invariant [p5_critical_section]
  pc I = w1 ∨ pc I = w2 →
    ∀j, (j ≠ I ∧ ¬unchecked I j) →
      before I j

invariant [p6_nxt_e2_e3]
  pc I = w2 ∧
  ((pc (nxt I) = e2 ∧ ¬unchecked (nxt I) I) ∨ (pc (nxt I) = e3)) →
    (sequence.le (number I) (max (nxt I)))

invariant [p7_cs_precedes_all]
  pc I = cs →
    ∀j, (j ≠ I) →
      before I j

/- Ensures no two processes are in critical section simultaneously. -/
safety [mutual_exclusion]
  pc I = cs ∧ pc J = cs → I = J

set_option maxHeartbeats 2500000



#gen_spec

#check_invariants


@[veil]
theorem evtW1_mutual_exclusion (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (sequence_t : Type) [sequence_t_dec_eq : DecidableEq.{1} sequence_t]
    [sequence_t_inhabited : Inhabited.{1} sequence_t] (pc_main : Type) [pc_main_dec_eq : DecidableEq.{1} pc_main]
    [pc_main_inhabited : Inhabited.{1} pc_main] [pc_main_Enum : @pc_main_EnumClass pc_main]
    [sequence : TotalOrderWithZero sequence_t] [thread : TotalOrderWithZero process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process sequence_t pc_main __veil_f)
          (State.Label.toCodomain process sequence_t pc_main __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process sequence_t pc_main __veil_f)
          (State.Label.toCodomain process sequence_t pc_main __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process sequence_t pc_main) ρ]
    [evtW1_dec_0 : delta% @Bakery.evtW1._veil_dec_type_0 process χ sequence_t pc_main χ_rep] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@evtW1.ext ρ σ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq sequence_t_inhabited
          pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread χ χ_rep χ_rep_lawful σ_sub ρ_sub
          evtW1_dec_0 self)
        (@Assumptions ρ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq sequence_t_inhabited
          pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq sequence_t_inhabited
          pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@mutual_exclusion ρ σ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq
          sequence_t_inhabited pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  classical


  /-  We need to show that when the extW1 transition happens, mutex is preserved.
      This action can move a node either back to W2 or to CS, so both cases will need to be handled.

  -/

  show st.pc self = w1 →
    if ∃ i, st.unchecked self i = true then
      ∀ (i : process),
        st.unchecked self i = true →
          st.flag i = false →
            ∀ (I J : process), (if self = I then w2 else st.pc I) = cs → (if self = J then w2 else st.pc J) = cs → I = J
    else ∀ (I J : process), (¬self = I → st.pc I = cs) → (¬self = J → st.pc J = cs) → I = J


  -- Introduce predicates and invariants
  intro self_was_w1
  rcases hinv with ⟨num_non_zero, flag_raised, nxt_not_self, unchecked_not_self, critical_section, nxt_e2_e3, cs_precedes_all, mutex⟩


  -- Handle each branch of the if in W1 seperately.
  split_ifs with h₁

  · -- There exists k : unchecked self k = true
    -- k is called i in the action transition above TODO: Fix
    intro k unchecked_i_self n_flag_i i j i_cs j_cs
    show i = j

    sorry




  · -- There doesn't exists i : unchecked self i = true
    intro i j self_neq_i_implies_cs_i self_neq_j_implies_cs_j
    show i = j
    apply mutex


    -- Check if
    · show st.pc i = cs
      by_cases h : (self = i)
      ·

        sorry
      · exact self_neq_i_implies_cs_i h

    · show st.pc j = cs
      sorry





@[veil]
theorem evtCS_mutual_exclusion (ρ : Type) (σ : Type) (process : Type) [process_dec_eq : DecidableEq.{1} process]
    [process_inhabited : Inhabited.{1} process] (sequence_t : Type) [sequence_t_dec_eq : DecidableEq.{1} sequence_t]
    [sequence_t_inhabited : Inhabited.{1} sequence_t] (pc_main : Type) [pc_main_dec_eq : DecidableEq.{1} pc_main]
    [pc_main_inhabited : Inhabited.{1} pc_main] [pc_main_Enum : @pc_main_EnumClass pc_main]
    [sequence : TotalOrderWithZero sequence_t] [thread : TotalOrderWithZero process] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain process sequence_t pc_main __veil_f)
          (State.Label.toCodomain process sequence_t pc_main __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain process sequence_t pc_main __veil_f)
          (State.Label.toCodomain process sequence_t pc_main __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory process sequence_t pc_main) ρ] :
    ∀ (self : process),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@evtCS.ext ρ σ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq sequence_t_inhabited
          pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread χ χ_rep χ_rep_lawful σ_sub ρ_sub self)
        (@Assumptions ρ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq sequence_t_inhabited
          pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread ρ_sub)
        (@Invariants ρ σ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq sequence_t_inhabited
          pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@mutual_exclusion ρ σ process process_dec_eq process_inhabited sequence_t sequence_t_dec_eq
          sequence_t_inhabited pc_main pc_main_dec_eq pc_main_inhabited pc_main_Enum sequence thread χ χ_rep
          χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil

  /-  We need to show that mutual exclusion between all processes when an arbitrary process 'self' exits
      its critical section.
  -/

  show  st.pc self = cs →
          ∀ (I J : process),
            (if self = I then exit else st.pc I) = cs →
              (if self = J then exit else st.pc J) = cs →
                I = J

  -- Extract all predicates from the statement above, then bring all invariants into the context
  intros self_was_cs i j i_cs j_cs
  rcases hinv with ⟨num_non_zero, flag_raised, nxt_not_self, unchecked_not_self, critical_section, nxt_e2_e3, cs_precedes_all, mutex⟩

  -- Now the goal is to show, under the previous assumptions, i = j.
  show i = j
  apply mutex

  -- As mutex held before the transition, it suffices to show that st.pc i = cs and st.pc j = cs

  · -- First show state i = cs
    show st.pc i = cs

    by_cases self_is_i : (i = self)
    · rw [self_is_i]
      exact self_was_cs
    · rw [if_neg (Ne.symm self_is_i)] at i_cs
      exact i_cs

  · -- Now show state j = cs
    show st.pc j = cs
    by_cases self_is_j : (j = self)
    · rw [self_is_j]
      exact self_was_cs
    · rw [if_neg (Ne.symm self_is_j)] at j_cs
      exact j_cs



temporal [success] ∀ x : process, 𝒲ℱ (evtW1 x) → ◇ ⌜ vCritical x ⌝

prove_temporal_by [success]


  tstart hInit hNext hInv

  tclear hInv
  tdsimp only [success]
  intro hwf


  -- Reduce goal to `v not in critical ↝  v in critical`


  -- tsuffices hleadsto :
  --   ∀ v : process,
  --     ⌜fun st => (veil_term% vNotCritical) st⌝ ↝
  --       ⌜fun st => (veil_term% vCritical) st⌝ by
    -- sorry


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
--   pc_main := pc_main_IndT }
-- { one_th := 1,
--   one := 1 }


end Bakery
