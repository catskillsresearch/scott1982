/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.InfoSys

/-!
# Factoid 3.4 — top element and total elements

**Factoid 3.4 (inventory / Scott §3).** There need be no top element `⊤`. Such an
element exists if and only if every finite subset of the token set is consistent, in
which case `⊤ = D` as a set. When it exists, it is the unique *total* (maximal)
element of the domain.
-/

namespace Scott1982

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- A **total** element is a maximal element of `|A|` under inclusion. -/
def IsTotal (x : sys.Element) : Prop := ∀ y, x ≤ y → y ≤ x

/-- Every finite set of tokens is consistent. -/
def AllConsistent : Prop := ∀ u : Finset α, u ∈ sys.Con

/-- **Factoid 3.4.** When every finite set is consistent, the top element is `D` itself. -/
def topElement (h : sys.AllConsistent) : sys.Element where
  carrier := Set.univ
  consistent := fun Y _ => h Y
  closed := fun _ _ _ _ => trivial

theorem le_topElement (h : sys.AllConsistent) (x : sys.Element) :
    x ≤ sys.topElement h := fun _ _ => trivial

theorem topElement_isTotal (h : sys.AllConsistent) :
    sys.IsTotal (sys.topElement h) := fun y _ => sys.le_topElement h y

/-- When `⊤` exists, it is the unique total element. -/
theorem eq_topElement_of_isTotal (h : sys.AllConsistent) {x : sys.Element}
    (hx : sys.IsTotal x) : x = sys.topElement h :=
  le_antisymm (sys.le_topElement h x) (hx _ (sys.le_topElement h x))

theorem isTotal_iff_eq_topElement (h : sys.AllConsistent) {x : sys.Element} :
    sys.IsTotal x ↔ x = sys.topElement h :=
  ⟨sys.eq_topElement_of_isTotal h, fun hx => hx ▸ sys.topElement_isTotal h⟩

theorem exists_unique_total_of_allConsistent (h : sys.AllConsistent) :
    ∃! x : sys.Element, sys.IsTotal x :=
  ⟨sys.topElement h, ⟨sys.topElement_isTotal h, fun _ hy =>
    sys.eq_topElement_of_isTotal h hy⟩⟩

/-- An element whose carrier is the whole token set is total (hence the greatest element). -/
theorem isTotal_of_carrier_univ {x : sys.Element} (hx : x.carrier = Set.univ) :
    sys.IsTotal x := fun _ _ _ _ => hx ▸ trivial

/-- Conversely: any total element equals an element with carrier `D`. -/
theorem eq_of_carrier_univ_of_isTotal {x t : sys.Element}
    (hx : x.carrier = Set.univ) (ht : sys.IsTotal t) : t = x :=
  le_antisymm (fun _ _ => hx ▸ trivial) (ht x (fun _ _ => hx ▸ trivial))

/-- **Factoid 3.4.** Top `⊤ = D` exists as an element iff every finite subset is consistent. -/
theorem exists_top_iff_allConsistent :
    (∃ x : sys.Element, x.carrier = Set.univ) ↔ sys.AllConsistent := by
  constructor
  · intro ⟨x, hx⟩ u
    exact x.consistent u (hx ▸ Set.subset_univ _)
  · intro h
    exact ⟨sys.topElement h, rfl⟩

end InfoSys

end Scott1982
