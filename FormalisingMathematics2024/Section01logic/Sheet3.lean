/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  apply h
  triv
  done

example : False → ¬True := by
  intro h
  intro t
  exact h
  done

example : ¬False → True := by
  intro h
  triv
  done

example : True → ¬False := by
  intro hT
  intro hF
  exact hF
  done

example : False → ¬P := by
  intro hF
  intro hP
  exact hF
  done

example : P → ¬P → False := by
  intro hP
  intro hPF
  apply hPF
  exact hP
  done

example : P → ¬¬P := by
  intro h1
  intro h2
  apply h2
  exact h1
  done

example : (P → Q) → ¬Q → ¬P := by
  intro h1 h2 h3
  apply h1 at h3
  exact h2 h3
  done

example : ¬¬False → False := by
  intro h1
  apply h1
  intro h2
  exact h2
  done

example : ¬¬P → P := by
  intro h1
  by_contra h2
  exact h1 h2
  done

example : (¬Q → ¬P) → P → Q := by
  intro h1 h2
  by_cases hQ : Q
  exact hQ
  exfalso
  apply h1 at hQ
  apply hQ at h2
  exact h2
  done
