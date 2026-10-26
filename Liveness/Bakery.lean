import Liveness.Rules

open TLA

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
function flag : process → Bool          -- Shows a process is choosing
relation unchecked: process → process → Bool -- Used to check ticket nums
function max : process → sequence_t -- Largest ticker number a process has seen
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

/- Ghost relations (for specification only) -/

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

ghost relation at_e1   (i : process) := pc i = e1
ghost relation at_e2   (i : process) := pc i = e2
ghost relation at_e3   (i : process) := pc i = e3
ghost relation at_e4   (i : process) := pc i = e4
ghost relation at_w1   (i : process) := pc i = w1
ghost relation at_cs   (i : process) := pc i = cs
ghost relation at_ncs  (i : process) := pc i = ncs
ghost relation at_exit (i : process) := pc i = exit
ghost relation waiting (i : process) := pc i = w1 ∨ pc i = w2

/- Relations for waiting argument-/

ghost relation some_cs :=
  ∃ i, pc i = cs

ghost relation unblocked (i : process) :=
  i ≠ J → pc J = ncs ∨ (waiting J ∧ prec (number i) (number J) i J)


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

action evtE1_branch2 (self : process) {
  require pc self = e1
  flag self := true
  unchecked self Q := if Q = self then false else true
  max self := sequence.zero
  pc self := e2
}

action evtE2 (self : process) {
  require pc self = e2
  if (∃k, unchecked self k) then
    let k :| unchecked self k
    unchecked self k := false
    let number_k := number k
    let max_self := max self
    if lt max_self number_k then
      max self := number_k
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

/- Wait to enter CS -/
action evtW1 (self : process) {
  require pc self = w1
  if (∃k, unchecked self k) then
    let k ← pick process
    assume unchecked self k
    nxt self := k
    require ¬ flag k
    pc self := w2
  else
    pc self := cs
}

/- Check process in loop -/
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

/- Invariants -/

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

invariant [p8_checked_not_cs]
  pc I = w1 ∨ pc I = w2 →
    ∀ j, (j ≠ I ∧ ¬ unchecked I j) →
      pc j ≠ cs


/- Ensures no two processes are in critical section simultaneously. -/
safety [mutual_exclusion]
  pc I = cs ∧ pc J = cs → I = J

-- Invariants for liveness proofs

invariant [p9]
  pc I = w2 → unchecked I (nxt I)

invariant [p10]
  pc I = ncs ∨ pc I = e1 ∨ pc I = e2 → number I = sequence.zero

invariant [p11]
  pc I = ncs ∨ pc I = w1 ∨ pc I = w2 ∨ pc I = cs ∨ pc I = exit → flag I = false




set_option maxHeartbeats 2500000

#gen_spec

/- Manual proofs of mutual exclusion under state transitions -/

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
  rcases hinv with ⟨num_non_zero, flag_raised, nxt_not_self, unchecked_not_self, critical_section, nxt_e2_e3, cs_precedes_all, checked_not_cs, mutex, p9, p10, p11⟩

  have hd := pc_main_EnumClass.distinct

  -- Handle each branch of the if in W1 seperately.
  split_ifs with h₁

  · -- There exists k : unchecked self k = true
    -- k is called i in the action transition above TODO: Fix
    intro k unchecked_i_self n_flag_i i j i_cs j_cs
    show i = j

    -- Split into cases where i and j are self or not.
    by_cases hsi : (i = self)
    · by_cases hsj : (j = self)

      · rw [hsi, hsj]
      · rw [hsi, if_pos rfl] at i_cs
        · have h_w2_cs : ¬ w2 = cs := by
            have h_flat := hd.2
            aesop
          exact absurd i_cs h_w2_cs

    · by_cases hsj : (j = self)
      · rw [hsj, if_pos rfl] at j_cs
        · have h_w2_cs : ¬ w2 = cs := by
            have h_flat := hd.2
            aesop
          exact absurd j_cs h_w2_cs
      ·
        apply mutex
        · aesop
        · aesop

  · -- There doesn't exists i : unchecked self i = true
    -- This is the branch of the if where self actually transitions into CS, so the proof is more involved.

    intro i j self_neq_i_implies_cs_i self_neq_j_implies_cs_j
    show i = j

    -- To show i = j, given the hypotheses, we split into the cases where i,j = self or not.

    by_cases hsi : (i = self)
    · by_cases hsj : (j = self)

      · -- i = self ∧ j = self
        rw [hsi, hsj]

      · -- i = self ∧ j ≠ self
        -- We must show this case is impossible
        rw [_root_.not_exists] at h₁

        have h_j_checked : ¬st.unchecked self j :=
          by exact h₁ j

        rw [Bool.not_eq_true] at h_j_checked

        have h_j_cs : st.pc j = cs :=
          by exact self_neq_j_implies_cs_j (mt Eq.symm hsj)

        -- Apply invariant
        have res1 := checked_not_cs self (Or.inl self_was_w1) j hsj h_j_checked
        exact absurd h_j_cs res1

    · by_cases hsj : (j = self)
      · -- i ≠ self ∧ j = self
        rw [_root_.not_exists] at h₁
        have h_i_checked : ¬st.unchecked self i:=
          by exact h₁ i
        rw [Bool.not_eq_true] at h_i_checked

        have h_i_cs : st.pc i = cs :=
          by exact self_neq_i_implies_cs_i (mt Eq.symm hsi)

        have res1 := checked_not_cs self (Or.inl self_was_w1) i hsi h_i_checked
        exact absurd h_i_cs res1

      · -- i ≠ self ∧ j ≠ self

        -- We assume mutex holds in the previous state. As i and j are not self, we know
        -- that their states are the same as before this transition. Therefore if they
        -- are both critical, they must be the same process.
        apply mutex
        · exact self_neq_i_implies_cs_i (mt Eq.symm hsi)
        · exact self_neq_j_implies_cs_j (mt Eq.symm hsj)

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
  rcases hinv with ⟨num_non_zero, flag_raised, nxt_not_self, unchecked_not_self, critical_section, nxt_e2_e3, cs_precedes_all, checked_not_cs, mutex, p9, p10, p11⟩

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

#check_invariants

/- Shared proof macros -/

-- Opens goal and creates hypotheses about the state fields
set_option hygiene false in
macro "bakery_open" : tactic => `(tactic| (
  __liveness_narrow_action
  __liveness_narrow_enabled
  __liveness_narrow_assumptions
  __liveness_narrow_invariants
  __liveness_narrow_localrprop
  __veil_concretize_state_wp
  __veil_concretize_fields_wp !
  __liveness_unfold_assumptions_core
  __liveness_unfold_invariants_core
  veil_dsimp only [nextSimp, State.Label.toCodomain, State.Label.toDomain] at *
  __veil_neutralize_decidable_inst
  open Classical in veil_simp only [invSimp, smtSimp, ghostRelSimp] at *
  -- All steps before this were taken from Veil's liveness pipeline,
  -- but stop before it uses SMT solvers (or bundles steps)
  -- Veil/Liveness/Tactics.lean
  all_goals
    have hd := pc_main_Enum.distinct
    simp [distinctN_pairwise_neq] at hd))

-- Put the goal into its simplest form
set_option hygiene false in
macro "bakery_post" : tactic => `(tactic| (
  (try simp only [← funext_iff] at hNext) <;> (try simp only [← funext_iff] at hact) <;>
  (try casesm* _ ∧ _, ∃ _, _) <;> (try split_ifs at *) <;> (try casesm* _ ∧ _, ∃ _, _) <;>
  (try split_ifs at *) <;> (try casesm* _ ∧ _, ∃ _, _) <;>
  (try subst_vars) <;> (try simp only [] at *) <;> (try split_ifs at *) <;> (try split_ifs)))

-- Runs bakery post then closes each goal with simp
macro "bakery_close" : tactic => `(tactic| (
  all_goals bakery_post
  all_goals first
    | (simp_all; done)
    | grind [TotalOrderWithZero.le_refl, TotalOrderWithZero.le_trans,
        TotalOrderWithZero.le_antisymm, TotalOrderWithZero.le_total, TotalOrderWithZero.zero_le]))

-- Destructure and create goals for each action
set_option hygiene false in
macro "bakery_cases" : tactic => `(tactic| (
  obtain ⟨label, hNext⟩ := hNext
  cases label <;> simp only [NextTr] at hNext))

-- The standardised proof of one WF1 step
set_option hygiene false in
macro "bakery_wf1" : tactic => `(tactic| (
  tapply wf1_original
  tsplit_ands <;> tmonotone
  · -- Stability (1)
    trintro ⟨hp, hNext⟩
    tfinite_window
    bakery_cases
    all_goals (clear hass; bakery_open; bakery_close)
  · -- Progress (2)
    trintro ⟨hp, -, hact⟩
    tfinite_window
    clear hass; bakery_open; bakery_close
  · -- Enabledness (3)
    tintro hp
    tfinite_window
    clear hass; bakery_open; bakery_close))

/- Liveness proofs -/


-- progress e1, e3, and e4 are trivial

temporal [progress_e1]
  ∀ i, 𝒲ℱ (evtE1_branch2 i) → ⌜fun st => at_e1 i st⌝ ↝ ⌜fun st => at_e2 i st⌝

prove_temporal_by [progress_e1]
  tstart hInit hNext hInv
  tclear hInit hInv
  tdsimp only [progress_e1]
  tintro i hwf
  trevert hNext hwf ; trewrite [← TLA.and_imp]
  bakery_wf1


temporal [progress_e2_rank]
  ∀ i, ∀ n,
    ⌞ Finite process ⌟ →
    𝒲ℱ (evtE2 i) →
      ⌜fun st => at_e2 i st ∧ Set.ncard {k | unchecked i k st} = n⌝ ↝
        ⌜fun st => at_e3 i st ∨ (at_e2 i st ∧ Set.ncard {k | unchecked i k st} < n)⌝

prove_temporal_by [progress_e2_rank]
  tstart hInit hNext hInv
  tclear hInit hInv
  tdsimp only [progress_e2_rank]
  tintro i n hfin hwf
  trevert hNext hwf ; trewrite [← TLA.and_imp]
  tapply wf1_original

  tsplit_ands <;> tmonotone
  · trintro ⟨hp, hNext⟩
    tfinite_window
    bakery_cases
    all_goals
      clear hass; bakery_open
      bakery_post <;> simp_all [ncard_erase_lt]
  · trintro ⟨hp, -, hact⟩
    tfinite_window
    clear hass; bakery_open
    bakery_post <;> simp_all [ncard_erase_lt]
  · tintro hp
    tfinite_window
    clear hass; bakery_open; bakery_close

temporal [progress_e2]
  ∀ i, ⌞ Finite process ⌟ → 𝒲ℱ (evtE2 i) → ⌜fun st => at_e2 i st⌝ ↝ ⌜fun st => at_e3 i st⌝

prove_temporal_by [progress_e2]
  intro e hB
  have hr := (progress_e2_rank._proof (evtE2_dec_0 := evtE2_dec_0) (evtW1_dec_0 := evtW1_dec_0)
    th hass) e hB
  intro i hfin hwf
  exact rank_leads_to e (fun n => hr i n hfin hwf)


temporal [progress_e3]
  ∀ i,
    ⌞ ∀ m : sequence_t, ∃ j : sequence_t, TotalOrderWithZero.le m j ∧ m ≠ j ⌟ →
    𝒲ℱ (evtE3_branch2 i) →
      ⌜fun st => at_e3 i st⌝ ↝ ⌜fun st => at_e4 i st⌝

prove_temporal_by [progress_e3]
  tstart hInit hNext hInv
  tclear hInit hInv
  tdsimp only [progress_e3]
  tintro i hunb hwf
  trevert hNext hwf ; trewrite [← TLA.and_imp]
  bakery_wf1

temporal [progress_e4]
  ∀ i, 𝒲ℱ (evtE4_branch2 i) → ⌜fun st => at_e4 i st⌝ ↝ ⌜fun st => at_w1 i st⌝

prove_temporal_by [progress_e4]
  tstart hInit hNext hInv
  tclear hInit hInv
  tdsimp only [progress_e4]
  tintro i hwf
  trevert hNext hwf ; trewrite [← TLA.and_imp]
  bakery_wf1


-- Use the tranistivity of ↝ to chain these together

set_option hygiene false in
macro "fact%" n:ident : term =>
  `(($(Lean.mkIdent (n.getId ++ `_proof)) (evtE2_dec_0 := evtE2_dec_0)
      (evtW1_dec_0 := evtW1_dec_0) th hass) e hB)

temporal [doorway_progress]
  ⌞ Finite process ⌟ →
  ⌞ ∀ m : sequence_t, ∃ j : sequence_t, TotalOrderWithZero.le m j ∧ m ≠ j ⌟ →
  ∀ i,
    𝒲ℱ (evtE1_branch2 i) →
    𝒲ℱ (evtE2 i) →
    𝒲ℱ (evtE3_branch2 i) →
    𝒲ℱ (evtE4_branch2 i) →
      ⌜fun st => at_e1 i st⌝ ↝ ⌜fun st => at_w1 i st⌝

prove_temporal_by [doorway_progress]
  intro e hB hfin hunb i wfE1 wfE2 wfE3 wfE4

  have h12 := (fact% progress_e1) i wfE1
  have h23 := (fact% progress_e2) i hfin wfE2
  have h34 := (fact% progress_e3) i hunb wfE3
  have h4w := (fact% progress_e4) i wfE4
  exact leads_to_trans _ _ _ e h12 (leads_to_trans _ _ _ e h23 (leads_to_trans _ _ _ e h34 h4w))


/- Waiting to CS -/

temporal [before_next]
  ∀ i, ∀ k,
    □ (⌜fun st => waiting i st⌝ ∧ ⌜fun st => before i k st⌝ ∧  ◯⌜fun st => waiting i st⌝ →
      ◯ ⌜fun st => before i k st⌝)

prove_temporal_by [before_next]
  tstart hInit hNext hInv
  tmonotone
  trintro ⟨hw, hb, hw'⟩



  sorry





end Bakery
