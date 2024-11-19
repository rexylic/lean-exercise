/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro dPQ
  exact dPQ.left
  done

example : P ∧ Q → Q := by
  intro dPQ
  exact dPQ.right
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR cPQ
  exact hPQR cPQ.left cPQ.right
  done

example : P → Q → P ∧ Q := by
  intro pP pQ
  constructor
  exact pP
  exact pQ
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro cPQ
  constructor
  exact cPQ.right
  exact cPQ.left
  done

example : P → P ∧ True := by
  intro pP
  constructor
  exact pP
  triv
  done

example : False → P ∧ False := by
  intro pF
  exfalso
  exact pF
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro cPQ cQR
  constructor
  exact cPQ.left
  exact cQR.right
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h cP cQ
  apply h
  constructor
  exact cP
  exact cQ
  done
