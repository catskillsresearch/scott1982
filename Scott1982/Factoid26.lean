/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.InfoSys

/-!
# Factoid 2.6 — third example: partial-function graphs plus `Δ`

**Scott 1982, §2 (“A third example”).** Fix sets `A` and `B`. Data objects are pairs
`(a, b) ∈ A × B` (meaning “the function maps `a` to `b`”) together with a least-informative
`Δ`. A finite set of pairs is consistent iff it is functional:

```
{(aᵢ, bᵢ)} ∈ Con  iff  (aᵢ = aⱼ → bᵢ = bⱼ for all i, j);
```

adjoining `Δ` preserves consistency. Entailment is the minimal one:

```
u ⊢ X  iff  X = Δ  ∨  X ∈ u.
```
-/

namespace Scott1982

namespace Factoid26

/-- Tokens: `bot` ≃ `Δ`, or a graph atom `pair a b`. -/
inductive Token (A B : Type*) where
  | bot
  | pair (a : A) (b : B)
  deriving DecidableEq

/-- Scott’s consistency: the pairs in `u` form a partial function `A ⇀ B`
(`bot` is ignored). -/
def Consistent {A B : Type*} (u : Finset (Token A B)) : Prop :=
  ∀ ⦃a : A⦄ ⦃b b' : B⦄,
    Token.pair a b ∈ u → Token.pair a b' ∈ u → b = b'

theorem consistent_empty {A B : Type*} :
    Consistent (∅ : Finset (Token A B)) := by
  intro _a _b _b' hb _
  exact False.elim (Finset.notMem_empty _ hb)

theorem consistent_singleton {A B : Type*} [DecidableEq A] [DecidableEq B]
    (t : Token A B) : Consistent ({t} : Finset (Token A B)) := by
  intro a b b' hb hb'
  rw [Finset.mem_singleton] at hb hb'
  -- both equal `t`; cases on `t`
  cases t with
  | bot =>
    cases hb
  | pair a0 b0 =>
    cases hb
    cases hb'
    rfl

theorem consistent_subset {A B : Type*} {u v : Finset (Token A B)} (huv : v ⊆ u)
    (hu : Consistent u) : Consistent v :=
  fun _a _b _b' hb hb' => hu (huv hb) (huv hb')

theorem consistent_insert_bot {A B : Type*} [DecidableEq A] [DecidableEq B]
    {u : Finset (Token A B)} (hu : Consistent u) :
    Consistent (insert (Token.bot : Token A B) u) := by
  intro a b b' hb hb'
  have hb1 : Token.pair a b ∈ u := by
    rcases Finset.mem_insert.mp hb with h | h
    · cases h
    · exact h
  have hb2 : Token.pair a b' ∈ u := by
    rcases Finset.mem_insert.mp hb' with h | h
    · cases h
    · exact h
  exact hu hb1 hb2

theorem consistent_insert_mem {A B : Type*} [DecidableEq A] [DecidableEq B]
    {u : Finset (Token A B)} {t : Token A B}
    (ht : t ∈ u) (hu : Consistent u) : Consistent (insert t u) := by
  simpa [Finset.insert_eq_of_mem ht] using hu

/-- Minimal entailment, with LHS consistency baked in (Scott types `⊢` on `Con`). -/
def Ent {A B : Type*} (u : Finset (Token A B)) (X : Token A B) : Prop :=
  Consistent u ∧ (X = Token.bot ∨ X ∈ u)

/-- **Factoid 2.6.** Partial-function information system of Scott 1982, §2. -/
def partialFunctionSystem (A B : Type*) [DecidableEq A] [DecidableEq B] :
    InfoSys (Token A B) where
  bot := Token.bot
  Con := {u | Consistent u}
  Ent := Ent
  con_subset := by
    intro u v hu hv
    exact consistent_subset hv hu
  con_sing := fun t => consistent_singleton t
  ent_con := by
    rintro u a ⟨hu, hX⟩
    rcases hX with rfl | hmem
    · exact consistent_insert_bot hu
    · exact consistent_insert_mem hmem hu
  ent_bot := by
    intro u hu
    exact ⟨hu, Or.inl rfl⟩
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, Or.inr ha⟩
  ent_trans := by
    intro u v c hv _hu hvu ⟨_, hc⟩
    refine ⟨hv, ?_⟩
    rcases hc with rfl | hc
    · exact Or.inl rfl
    · have ⟨_, hcv⟩ := hvu c hc
      exact hcv

/-- Instantiation for concrete carrier sets (Scott: “two fixed sets”). -/
example : InfoSys (Token ℕ Bool) := partialFunctionSystem ℕ Bool

end Factoid26

end Scott1982
