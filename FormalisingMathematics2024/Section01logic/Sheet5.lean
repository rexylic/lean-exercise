/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

lemma equiv_refl : (P ↔ Q) → (Q ↔ P) := by
  intro hPeQ
  rw [hPeQ]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  apply equiv_refl
  apply equiv_refl
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro ePQ eQR
  rw [ePQ]
  exact eQR
  done

example : P ∧ Q ↔ Q ∧ P := by
  tauto
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  tauto
  done

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  triv
  intro hPT
  cases' hPT with hP _
  exact hP
  done

example : False ↔ P ∧ False := by
  constructor
  intro h
  exfalso
  exact h
  intro h
  exfalso
  cases' h with _ hF
  exact hF
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  constructor
  intro cPR
  rw [← hPQ, ← hRS]
  exact cPR
  intro cQS
  rw [hPQ, hRS]
  exact cQS
  done

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  by_cases hP : P
  exact h1 hP hP
  apply h1
  exact h2 hP
  exact h2 hP
  done
