/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  apply Or.intro_left
  done

example : Q → P ∨ Q := by
  apply Or.intro_right
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro dPQ
  cases' dPQ with hP hQ
  intro hPR hQR
  apply hPR hP
  intro hPR hQR
  apply hQR hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro dPQ
  cases' dPQ with hP hQ
  apply Or.inr
  exact hP
  apply Or.inl
  exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  apply Iff.intro
  intro dPQR
  cases' dPQR with dPQ hR
  cases' dPQ with hP hQ
  apply Or.inl
  exact hP
  apply Or.inr
  apply Or.inl
  exact hQ
  apply Or.inr
  apply Or.inr
  exact hR
  intro dPQR
  cases' dPQR with hPQR hR
  apply Or.inl
  apply Or.inl
  exact hPQR
  cases' hR with hQ hR
  apply Or.inl
  apply Or.inr
  exact hQ
  apply Or.inr
  exact hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS dPQ
  cases' dPQ with hP hQ
  apply Or.inl
  apply hPR hP
  apply hQS at hQ
  apply Or.inr
  exact hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ dPR
  cases' dPR with hP hR
  apply Or.inl
  apply hPQ hP
  apply Or.inr
  exact hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPQ hQS
  apply Iff.intro
  intro dPQ
  cases' dPQ with hP hQ
  apply Or.inl
  apply hPQ.1 hP
  apply Or.inr
  apply hQS.1 hQ
  intro dRS
  cases' dRS with hR hS
  apply Or.inl
  apply hPQ.2 hR
  apply Or.inr
  apply hQS.2 hS
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  apply Iff.intro
  intro hPQ
  apply And.intro
  intro hP
  apply hPQ
  apply Or.inl
  exact hP
  intro hQ
  apply hPQ
  apply Or.inr
  exact hQ
  intro hPQ
  intro dPQ
  cases' dPQ with hP hQ
  apply hPQ.left hP
  apply hPQ.right hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  apply Iff.intro
  intro hPQ
  by_cases hP : P
  by_cases hQ : Q
  exfalso
  apply hPQ
  constructor
  exact hP
  exact hQ
  apply Or.inr
  exact hQ
  apply Or.inl
  exact hP
  intro hPQ
  intro dPQ
  cases' hPQ with hP hQ
  apply hP
  exact dPQ.left
  apply hQ
  exact dPQ.right
  done
