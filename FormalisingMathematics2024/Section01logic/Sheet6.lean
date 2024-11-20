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
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro hP
  right
  exact hP
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  cases' hPoQ with hP hQ
  exact hPR hP
  exact hQR hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  right; exact hP
  left; exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro h1
    cases' h1 with hPQ hR
    · cases' hPQ with hP hQ
      · left; exact hP
      · right; left; exact hQ
    · right; right; exact hR
  · intro h2
    cases' h2 with hP hQR
    · left; left; exact hP
    · cases' hQR with hQ hR
      · left; right; exact hQ
      · right; exact hR

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  cases' hPoQ with hP hQ
  · left; exact hPR hP
  · right; exact hQS hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  cases' hPoR with hP hR
  · left; exact hPQ hP
  · right; exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intros ePR eQS
  rw [ePR, eQS]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h1; constructor
    · intro h2; apply h1; left; exact h2
    · intro h2; apply h1; right; exact h2
  · intro h1; cases' h1 with hnP hnQ
    intro h2; cases' h2 with hP hQ
    · exact hnP hP
    · exact hnQ hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h1; by_cases hP: P
    · right; intro hQ; apply h1; constructor
      · exact hP
      · exact hQ
    · left; exact hP
  · intro h2 h3; cases' h2 with hnP hnQ
    · cases' h3 with hP _; exact hnP hP
    · cases' h3 with _ hQ; exact hnQ hQ
  done
