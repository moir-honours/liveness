import Mathlib.Data.Set.Card
import Veil
import Veil.Liveness

open TLA

theorem rank_leads_to {σ : Type} {p q : σ → Prop} {f : σ → Nat} :
    (∀ n, ⌜fun s => p s ∧ f s = n⌝ ↝ ⌜fun s => q s ∨ (p s ∧ f s < n)⌝) |-tla- (⌜p⌝ ↝ ⌜q⌝) := by

  intro e hrank
  tunfold_simp'
  intro k hp
  -- Unfold and introduce hyps
  -- k is position in execution e where p holds

  induction hn : f (e k) using Nat.strongRecOn generalizing k with
  | _ n ih =>
    -- Need to show there exists position k + d where q holds
    -- Recurse on rank of state until it reaches 0, then q must hold
    obtain ⟨d, hq | ⟨hp', hlt⟩⟩ := hrank n k hp hn
    · -- q (e (k + d)) holds
      exact ⟨d, hq⟩
    · -- p (e (k + d)) holds and f (e (k + d)) < n = f (e k)
      -- apply induction hypothesis
      obtain ⟨d', hq⟩ := ih _ hlt (k + d) hp' rfl
      exact ⟨d + d', by simpa [Nat.add_assoc] using hq⟩

theorem ncard_erase_lt {α : Type} [Finite α] {u : α → Bool} {w : α} {n : ℕ} (hw : u w = true)
    (hn : {k | u k = true}.ncard = n) : {k | ¬w = k ∧ u k = true}.ncard < n := by


  -- Convert relation without elem to set without elem
  have hset : {k | ¬w = k ∧ u k = true} = {k | u k = true} \ {w} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hne, hk⟩
      exact ⟨hk, fun h => hne h.symm⟩
    · rintro ⟨hk, hne⟩
      exact ⟨fun h => hne h.symm, hk⟩

  rw [hset, ← hn]
  -- Mathlib: Set.ncard_diff_singleton_lt_of_mem (Mathlib/Data/Set/Card.lean)
  exact Set.ncard_diff_singleton_lt_of_mem hw
