/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Factoid41

/-!
# Factoid 4.2 — conditional completeness for meets

**Factoid 4.2 (Scott §4).** For any *non-empty* family of elements, the set-theoretic
intersection of the family is again an element. Thus `|A|` is a conditionally complete
inf-semilattice.
-/

namespace Scott1982

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Carrier intersection of a family of elements. -/
def familyInfCarrier (S : Set sys.Element) : Set α :=
  {a | ∀ x ∈ S, a ∈ x.carrier}

/-- **Factoid 4.2.** Meet of a nonempty family of elements (set-theoretic intersection). -/
def familyInf (S : Set sys.Element) (hne : S.Nonempty) : sys.Element where
  carrier := sys.familyInfCarrier S
  consistent := by
    intro Y hY
    obtain ⟨x₀, hx₀⟩ := hne
    have hYx : (Y : Set α) ⊆ x₀.carrier := fun a ha => (hY ha) x₀ hx₀
    exact x₀.consistent Y hYx
  closed := by
    intro Y a hY hEnt x hx
    have hYx : (Y : Set α) ⊆ x.carrier := fun b hb => (hY hb) x hx
    exact x.closed Y a hYx hEnt

theorem familyInf_le (S : Set sys.Element) (hne : S.Nonempty) {x : sys.Element}
    (hx : x ∈ S) : sys.familyInf S hne ≤ x :=
  fun _a ha => ha x hx

theorem le_familyInf (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element}
    (h : ∀ x ∈ S, z ≤ x) : z ≤ sys.familyInf S hne :=
  fun _a ha x hx => h x hx ha

/-- `familyInf` is the greatest lower bound of the family. -/
theorem familyInf_le_iff (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element} :
    z ≤ sys.familyInf S hne ↔ ∀ x ∈ S, z ≤ x :=
  ⟨fun hz _x hx => le_trans hz (sys.familyInf_le S hne hx), sys.le_familyInf S hne⟩

/-- Binary meet agrees with the two-element family meet. -/
theorem familyInf_pair (x y : sys.Element) :
    sys.familyInf ({x, y} : Set sys.Element) ⟨x, Set.mem_insert x {y}⟩ = sys.inf x y := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf
      (sys.familyInf_le _ _ (Set.mem_insert x {y}))
      (sys.familyInf_le _ _ (Set.mem_insert_of_mem _ rfl))
  · apply sys.le_familyInf
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hy
    · exact sys.inf_le_left _ _
    · have : z = y := hy
      subst this
      exact sys.inf_le_right _ _

end InfoSys

end Scott1982
