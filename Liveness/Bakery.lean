import Veil
import Veil.Liveness

-- Language options
set_option linter.dupNamespace false
set_option veil.printCounterexamples true

veil module Mutex

-- Node definitions
type node

instantiate tot : TotalOrderWithMinimum node
open TotalOrderWithMinimum

function choosing : node → Bool
relation critical : node → Bool
function number   : node → ℕ

#gen_state
#print State


-- Initial state
after_init {
  number N := 0;
  choosing N := False;
  critical N := False;
}



-- Transition actions

action choose (i : node)  = {
  require ¬ choosing i;
  require number i = 0;
  choosing i := True;

  -- Find ticket value greater than all others
  let t_max ← fresh;
  require ∀ j, j ≠ i → number j < t_max;
  number i := t_max;

  choosing i := False;
}

action enter (i : node) = {
  -- Only allow enter if not choosing
  require ¬ critical i;
  require number i ≠ 0;
  require ∀ j, j ≠ i → ¬ choosing j;

  -- Only allow enter if i holds the smallest non-zero ticket number
  require ∀ j, j ≠ i →
    (number j = 0) ∨
    (number i < number j) ∨
    (number i = number j ∧ lt i j);

  critical i := True;
}

action exit (i : node) = {
  require critical i
  critical i := False
  number i := 0
}


-- Invariants

safety [mutex]
  ∀ I J, critical I → critical J → I = J


invariant [different_vals]
  number I ≠ 0 →
    number I = number J →
      I = J


invariant [critical_lowest]
  critical I →
    ∀ J, J ≠ I → number J = 0 ∨ number I < number J


invariant [critical_has_ticket]
    critical I →
        number I ≠ 0


#gen_spec
#check_invariants


@[invProof]
theorem enter_mutex1 :
    ∀ (st : @State node),
      ∀ (i : node),
        (@System node node_dec node_ne tot).assumptions st →
          (@System node node_dec node_ne tot).inv st →
            (@Mutex.enter.ext node node_dec node_ne tot i) st fun _ (st' : @State node) =>
              @Mutex.mutex node node_dec node_ne tot st' :=
  by

    -- Move state, process trying to enter i, and invariant into the Lean context.
    intros st i assumptions inv

    -- Unfold goal and invariant definitions.
    simp [Mutex.enter.ext, invSimp] at *

    -- Split invariant into individual clauses.
    rcases inv with ⟨critical_has_ticket, critical_lowest, different_vals, mutex⟩

    -- Add implictations to lean context
    rintro h_not_critical h_num h_choose h_lowest N M critN critM

    -- Now we need to prove if two arbitrary processes N and M are both in their critical sections, then N = M
    -- The currently entering process is i

    -- Use our different_vals invariant to split the current goal
    apply different_vals

    -- Show that number N ≠ 0
    · by_cases h : (N = i)
      -- If N = i
      · simp [h]
        exact h_num
      -- If N ≠ i
      · simp [h] at critN
        exact critical_has_ticket N critN

    -- Show that number N = number M
    · by_cases hN : N = i <;> by_cases hM : M = i
      -- N = i and M = i
      · simp [hN, hM]

      -- N = i and M ≠ i
      · simp [hM] at critM
        have hMlow := critical_lowest M critM i (Ne.symm hM)
        rcases hMlow with h0 | hlt
        · simp [hN, h0]
          omega
        · have hilow := h_lowest M hM
          rcases hilow with h0 | hlt' | ⟨heq, _⟩
          · simp [hN] at critN
            exact absurd h0 (critical_has_ticket M critM)
          · omega
          · omega

      -- N ≠ i and M = i
      · simp [hN] at critN
        have hNlow := critical_lowest N critN i (Ne.symm hN)
        rcases hNlow with h0 | hlt
        · simp [hM, h0]
          omega
        · have hilow := h_lowest N hN
          rcases hilow with h0 | hlt' | ⟨heq, _⟩
          · simp [hM] at critM
            exact absurd h0 (critical_has_ticket N critN)
          · omega
          · omega

      -- N ≠ i and M ≠ i
      · simp [hN] at critN
        simp [hM] at critM
        have same : N = M := by exact mutex N M critN critM
        simp [same]



end Mutex
