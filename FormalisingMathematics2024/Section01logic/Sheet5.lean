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

example : (P ↔ Q) → (Q ↔ P) := by
  intro ePQ
  apply ePQ.symm
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  apply Iff.intro
  intro ePQ
  apply ePQ.symm
  intro eQP
  apply eQP.symm
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro ePQ eQR
  constructor
  rw [ePQ, eQR]
  intro h
  apply h
  rw [← eQR, ← ePQ]
  intro h
  apply h
  done

example : P ∧ Q ↔ Q ∧ P := by
  apply Iff.intro
  intro cPQ
  constructor
  exact cPQ.right
  exact cPQ.left
  intro cQP
  constructor
  exact cQP.right
  exact cQP.left
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  apply Iff.intro
  intro cPQR
  constructor
  exact cPQR.left.left
  constructor
  exact cPQR.left.right
  exact cPQR.right
  intro cPQR
  constructor
  constructor
  exact cPQR.left
  exact cPQR.right.left
  exact cPQR.right.right
  done

example : P ↔ P ∧ True := by
  apply Iff.intro
  intro h
  constructor
  exact h
  triv
  intro h
  exact h.left
  done

example : False ↔ P ∧ False := by
  apply Iff.intro
  intro h
  exfalso
  exact h
  intro h
  exfalso
  exact h.right
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  apply Iff.intro
  intro cPR
  rw [← hPQ, ← hRS]
  exact cPR
  intro cQS
  rw [hPQ, hRS]
  exact cQS
  done

example : ¬(P ↔ ¬P) := by
  intro h
  have h1 : (P → ¬P) := h.mp
  have h2 : (¬P → P) := h.mpr
  by_cases p : P
  exact h1 p p
  have p : P := h2 p
  exact h1 p p
  done
