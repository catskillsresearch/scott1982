/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.InfoSys

/-!
# Factoid 2.4 — first example: lower bounds on ℕ

**Scott 1982, §2 (“A first example”).** Data objects are non-negative integers,
read as propositions `n ≤ x`. Take `Δ = 0`, every finite set consistent, and

```
{n₀, …, nₖ₋₁} ⊢ m  iff  m = 0  ∨  ∃ i, m ≤ nᵢ.
```

Scott: “That ⊢ is an entailment relation in the sense of our axioms is clear.”
We package this as an `example` that builds an `InfoSys ℕ` and discharges Def 2.1.
-/

namespace Scott1982

namespace Factoid24

/-- Entailment for the lower-bound system: `u ⊢ m` iff `m = 0` or some `n ∈ u` has `m ≤ n`. -/
def lowerBoundEnt (u : Finset ℕ) (m : ℕ) : Prop :=
  m = 0 ∨ ∃ n ∈ u, m ≤ n

/-- **Factoid 2.4.** The ℕ lower-bound information system of Scott 1982, §2. -/
example : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := lowerBoundEnt
  con_subset := by
    intro u v _ _
    exact Set.mem_univ v
  con_sing := by
    intro a
    exact Set.mem_univ _
  ent_con := by
    intro u a _
    exact Set.mem_univ _
  ent_bot := by
    intro u _
    exact Or.inl rfl
  ent_refl := by
    intro u a _ ha
    exact Or.inr ⟨a, ha, le_rfl⟩
  ent_trans := by
    intro u v c _ _ hvEnt huEnt
    rcases huEnt with rfl | ⟨n, hn, hcn⟩
    · exact Or.inl rfl
    · -- `u ⊢ c` via witness `n ∈ u` with `c ≤ n`; use `v ⊢ n`
      rcases hvEnt n hn with rfl | ⟨k, hk, hnk⟩
      · -- `n = 0`, so `c ≤ 0` ⇒ `c = 0`
        exact Or.inl (Nat.le_zero.mp hcn)
      · exact Or.inr ⟨k, hk, le_trans hcn hnk⟩

end Factoid24

end Scott1982
