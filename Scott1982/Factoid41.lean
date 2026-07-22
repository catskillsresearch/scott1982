/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Factoid33

/-!
# Factoid 4.1 — `|A|` is an inf-semilattice under intersection

**Factoid 4.1 (Scott §4 / inventory).** The intersection of two elements is again an
element, so `|A|` is an inf-semilattice under `∩`. In particular
`x ⊆ y ↔ x ∩ y = x`. Scott also records that `∩` is idempotent, commutative, and
associative, and that `⊥` is a zero for `∩`.
-/

namespace Scott1982

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 4.1.** Binary meet of elements is set-theoretic intersection. -/
def inf (x y : sys.Element) : sys.Element where
  carrier := x.carrier ∩ y.carrier
  consistent := fun Y hY =>
    x.consistent Y (Set.Subset.trans hY Set.inter_subset_left)
  closed := fun Y a hY hEnt =>
    ⟨x.closed Y a (Set.Subset.trans hY Set.inter_subset_left) hEnt,
     y.closed Y a (Set.Subset.trans hY Set.inter_subset_right) hEnt⟩

theorem inf_le_left (x y : sys.Element) : sys.inf x y ≤ x :=
  Set.inter_subset_left

theorem inf_le_right (x y : sys.Element) : sys.inf x y ≤ y :=
  Set.inter_subset_right

theorem le_inf {x y z : sys.Element} (hxy : x ≤ y) (hxz : x ≤ z) : x ≤ sys.inf y z :=
  fun _ ha => ⟨hxy ha, hxz ha⟩

/-- Meet is the greatest lower bound. -/
theorem inf_le_iff {x y z : sys.Element} : z ≤ sys.inf x y ↔ z ≤ x ∧ z ≤ y :=
  ⟨fun h => ⟨le_trans h (sys.inf_le_left x y), le_trans h (sys.inf_le_right x y)⟩,
   fun ⟨hx, hy⟩ => sys.le_inf hx hy⟩

/-- **Factoid 4.1.** `x ⊆ y` iff `x ∩ y = x`. -/
theorem le_iff_inf_eq {x y : sys.Element} : x ≤ y ↔ sys.inf x y = x := by
  constructor
  · intro h
    refine le_antisymm (sys.inf_le_left x y) ?_
    intro a ha
    exact ⟨ha, h ha⟩
  · intro heq
    have hc : x.carrier = x.carrier ∩ y.carrier :=
      Eq.symm (congrArg Element.carrier heq)
    intro a ha
    exact ((Set.ext_iff.1 hc a).1 ha).2

theorem inf_idem (x : sys.Element) : sys.inf x x = x :=
  (sys.le_iff_inf_eq (y := x)).1 (le_refl x)

theorem inf_comm (x y : sys.Element) : sys.inf x y = sys.inf y x := by
  refine le_antisymm ?_ ?_
  · exact sys.le_inf (sys.inf_le_right x y) (sys.inf_le_left x y)
  · exact sys.le_inf (sys.inf_le_right y x) (sys.inf_le_left y x)

theorem inf_assoc (x y z : sys.Element) : sys.inf (sys.inf x y) z = sys.inf x (sys.inf y z) := by
  refine le_antisymm ?_ ?_
  · refine sys.le_inf ?_ (sys.le_inf ?_ ?_)
    · exact le_trans (sys.inf_le_left _ _) (sys.inf_le_left _ _)
    · exact le_trans (sys.inf_le_left _ _) (sys.inf_le_right _ _)
    · exact sys.inf_le_right _ _
  · refine sys.le_inf (sys.le_inf ?_ ?_) ?_
    · exact sys.inf_le_left _ _
    · exact le_trans (sys.inf_le_right _ _) (sys.inf_le_left _ _)
    · exact le_trans (sys.inf_le_right _ _) (sys.inf_le_right _ _)

theorem inf_mono {x₁ x₂ y₁ y₂ : sys.Element} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    sys.inf x₁ y₁ ≤ sys.inf x₂ y₂ :=
  sys.le_inf (le_trans (sys.inf_le_left _ _) hx) (le_trans (sys.inf_le_right _ _) hy)

/-- `⊥` is a zero for meet: `⊥ ∩ x = ⊥`. -/
theorem botElement_inf (x : sys.Element) : sys.inf sys.botElement x = sys.botElement :=
  (sys.le_iff_inf_eq (x := sys.botElement) (y := x)).1 (sys.botElement_le x)

theorem inf_botElement (x : sys.Element) : sys.inf x sys.botElement = sys.botElement := by
  rw [sys.inf_comm, sys.botElement_inf]

end InfoSys

end Scott1982
