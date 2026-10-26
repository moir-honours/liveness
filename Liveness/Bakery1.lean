import Mathlib.Data.Set.Card
import Veil
import Veil.Liveness

open TLA

theorem rank_leads_to {σ : Type} {p q : σ → Prop} {f : σ → Nat} :
    (∀ n, ⌜fun s => p s ∧ f s = n⌝ ↝ ⌜fun s => q s ∨ (p s ∧ f s < n)⌝) |-tla- (⌜p⌝ ↝ ⌜q⌝) := by
  intro e h
  tunfold_simp'
  intro k hp
  induction hn : f (e k) using Nat.strongRecOn generalizing k with
  | _ n ih =>
    obtain ⟨k1, hq | ⟨hp', hlt⟩⟩ := h n k hp hn
    · exact ⟨k1, hq⟩
    · obtain ⟨k2, hq⟩ := ih _ hlt (k + k1) hp' rfl
      exact ⟨k1 + k2, by simpa [Nat.add_assoc] using hq⟩

theorem ncard_erase_lt {α : Type} [Finite α] {u : α → Bool} {w : α} {n : ℕ} (hw : u w = true)
    (hn : {k | u k = true}.ncard = n) : {k | ¬w = k ∧ u k = true}.ncard < n :=
  hn ▸ Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨fun _ hk => hk.2, fun h => by
    have : w ∈ {k | ¬w = k ∧ u k = true} := h ▸ hw
    exact this.1 rfl⟩)

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

ghost relation prec (a1 b1 : sequence_t) (a2 b2 : process) :=
  (lt a1 b1 ∨ (a1 = b1 ∧ lt_thread a2 b2))

ghost relation at_e1 (i : process) := pc i = e1
ghost relation at_e2 (i : process) := pc i = e2
ghost relation at_e3 (i : process) := pc i = e3
ghost relation at_e4 (i : process) := pc i = e4
ghost relation at_w1 (i : process) := pc i = w1
ghost relation at_cs (i : process) := pc i = cs

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

invariant [p2_flag_e2_e3]
  pc I = e2 ∨ pc I = e3 →
    flag I

#gen_spec

#check_invariants


/- Shared proof macros -/

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
  all_goals
    have hd := pc_main_Enum.distinct
    simp [distinctN_pairwise_neq] at hd))

set_option hygiene false in
macro "bakery_post" : tactic => `(tactic| (
  (try simp only [← funext_iff] at hNext) <;> (try simp only [← funext_iff] at hact) <;>
  (try casesm* _ ∧ _, ∃ _, _) <;> (try split_ifs at *) <;> (try casesm* _ ∧ _, ∃ _, _) <;>
  (try split_ifs at *) <;> (try casesm* _ ∧ _, ∃ _, _) <;>
  (try subst_vars) <;> (try simp only [] at *) <;> (try split_ifs at *) <;> (try split_ifs)))

macro "bakery_close" : tactic => `(tactic| (
  all_goals bakery_post
  all_goals first
    | (simp_all; done)
    | grind [TotalOrderWithZero.le_refl, TotalOrderWithZero.le_trans,
        TotalOrderWithZero.le_antisymm, TotalOrderWithZero.le_total, TotalOrderWithZero.zero_le]))

set_option hygiene false in
macro "bakery_cases" : tactic => `(tactic| (
  obtain ⟨label, hNext⟩ := hNext
  cases label <;> simp only [NextTr] at hNext))

set_option hygiene false in
macro "bakery_wf1" : tactic => `(tactic| (
  tapply wf1_original
  tsplit_ands <;> tmonotone
  · trintro ⟨hp, hNext⟩
    tfinite_window
    bakery_cases
    all_goals (clear hass; bakery_open; bakery_close)
  · trintro ⟨hp, -, hact⟩
    tfinite_window
    clear hass; bakery_open; bakery_close
  · tintro hp
    tfinite_window
    clear hass; bakery_open; bakery_close))


/- Liveness proofs -/


temporal [progress_e1]
  ∀ i, 𝒲ℱ (_evtE1_branch2 i) → ⌜fun st => at_e1 i st⌝ ↝ ⌜fun st => at_e2 i st⌝

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

set_option hygiene false in
macro "fact%" n:ident : term =>
  `(($(Lean.mkIdent (n.getId ++ `_proof)) (evtE2_dec_0 := evtE2_dec_0)
      (evtW1_dec_0 := evtW1_dec_0) th hass) e hB)




temporal [doorway_progress]
  ⌞ Finite process ⌟ →
  ⌞ ∀ m : sequence_t, ∃ j : sequence_t, TotalOrderWithZero.le m j ∧ m ≠ j ⌟ →
  (∀ j, 𝒲ℱ (_evtE1_branch2 j)) →
  (∀ j, 𝒲ℱ (evtE2 j)) →
  (∀ j, 𝒲ℱ (evtE3_branch2 j)) →
  (∀ j, 𝒲ℱ (evtE4_branch2 j)) →
    ∀ i, ⌜fun st => at_e1 i st⌝ ↝ ⌜fun st => at_w1 i st⌝

prove_temporal_by [doorway_progress]
  intro e hB hfin hunb wfE1 wfE2 wfE3 wfE4 i
  have h12 := (fact% progress_e1) i (wfE1 i)
  have h23 := (fact% progress_e2) i hfin (wfE2 i)
  have h34 := (fact% progress_e3) i hunb (wfE3 i)
  have h4w := (fact% progress_e4) i (wfE4 i)
  exact leads_to_trans _ _ _ e h12 (leads_to_trans _ _ _ e h23 (leads_to_trans _ _ _ e h34 h4w))

#print axioms doorway_progress._proof

-- temporal [progress_w1]
--   ⌞ Finite process ⌟ →
--   ⌞ ∀ m : sequence_t, ∃ j : sequence_t, TotalOrderWithZero.le m j ∧ m ≠ j ⌟ →
--   (∀ j, 𝒲ℱ (_evtE1_branch2 j)) →
--   (∀ j, 𝒲ℱ (evtE2 j)) →
--   (∀ j, 𝒲ℱ (evtE3_branch2 j)) →
--   (∀ j, 𝒲ℱ (evtE4_branch2 j)) →
--   (∀ j, 𝒲ℱ (evtW1 j)) →
--   (∀ j, 𝒲ℱ (evtW2 j)) →
--   (∀ j, 𝒲ℱ (evtCS j)) →
--   (∀ j, 𝒲ℱ (evtExit_branch2 j)) →
--     ∀ i, ⌜fun st => at_w1 i st⌝ ↝ ⌜fun st => at_cs i st⌝

-- prove_temporal_by [progress_w1]
--   tstart hInit hNext hInv
--   tclear hInit hInv
--   sorry

end Bakery
