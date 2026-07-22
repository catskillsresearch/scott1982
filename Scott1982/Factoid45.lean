/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Factoid36
import Scott1982.Factoid44

/-!
# Factoid 4.5 — algebraicity via finite elements

**Factoid 4.5 (Scott §4).** Finite elements `ū` are compact, and every element is the
directed lub of the finite elements below it (algebraicity). The carrier identity
`x = ⋃{ū | u ⊆ x}` is Factoid 3.6; here we package directedness, the lub form, and
compactness.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- `⊥ = ∅̄`. -/
theorem botElement_eq_closure_empty :
    sys.botElement = sys.closure (∅ : Finset α) sys.con_empty := by
  refine le_antisymm ?_ ?_
  · intro a ha
    -- ha : Ent {bot} a; show Ent ∅ a
    exact sys.ent_trans sys.con_empty (sys.con_sing sys.bot)
      (fun y hy => by
        have : y = sys.bot := Finset.mem_singleton.mp hy
        subst this
        exact sys.ent_bot sys.con_empty)
      ha
  · intro a ha
    -- ha : Ent ∅ a; show Ent {bot} a
    exact sys.ent_trans (sys.con_sing sys.bot) sys.con_empty
      (fun _ hy => False.elim (Finset.notMem_empty _ hy)) ha

/-- Finite approximations of `x`: the set `{ū | u ∈ Con, u ⊆ x}`. -/
def finiteApproximants (x : sys.Element) : Set sys.Element :=
  {y | ∃ (u : Finset α) (hu : u ∈ sys.Con), ↑u ⊆ x.carrier ∧ y = sys.closure u hu}

theorem nonempty_finiteApproximants (x : sys.Element) :
    (sys.finiteApproximants x).Nonempty := by
  refine ⟨sys.botElement, ∅, sys.con_empty, ?_, sys.botElement_eq_closure_empty⟩
  intro a ha
  exact False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha))

theorem directed_finiteApproximants (x : sys.Element) :
    sys.IsDirected (sys.finiteApproximants x) := by
  intro y₁ y₂ hy₁ hy₂
  obtain ⟨u, hu, huX, rfl⟩ := hy₁
  obtain ⟨v, hv, hvX, rfl⟩ := hy₂
  obtain ⟨w, hw, hwX, huw, hvw⟩ := sys.closures_directed x hu hv huX hvX
  exact ⟨sys.closure w hw, ⟨w, hw, hwX, rfl⟩, huw, hvw⟩

/-- **Factoid 4.5 / algebraicity.** `x` is the directed lub of its finite approximants. -/
theorem eq_directedSup_finiteApproximants (x : sys.Element) :
    x = sys.directedSup (sys.finiteApproximants x)
      (sys.nonempty_finiteApproximants x) (sys.directed_finiteApproximants x) := by
  refine le_antisymm ?_ ?_
  · -- x ≤ directedSup: every token of x lies in some ū ⊆ x
    intro a ha
    have : a ∈ sys.approxUnion x := (sys.mem_element_iff_mem_closure x a).1 ha
    obtain ⟨u, hu, huX, ha'⟩ := this
    rw [sys.directedSup_carrier_eq_union]
    exact ⟨sys.closure u hu, ⟨u, hu, huX, rfl⟩, ha'⟩
  · -- directedSup ≤ x: each approximant is ≤ x
    apply sys.directedSup_le
    intro y hy
    obtain ⟨u, hu, huX, rfl⟩ := hy
    exact sys.closure_le_element x hu huX

/-- Compactness of finite elements: if `ū ≤ ⊔ S` for directed nonempty `S`, then
`ū ≤` some member of `S`. -/
theorem compact_closure (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {u : Finset α} (hu : u ∈ sys.Con)
    (hle : sys.closure u hu ≤ sys.directedSup S hne hdir) :
    ∃ z ∈ S, sys.closure u hu ≤ z := by
  have huU : (u : Set α) ⊆ sys.familyUnionCarrier S := by
    intro a ha
    have : a ∈ (sys.directedSup S hne hdir).carrier :=
      hle (sys.subset_closure hu (Finset.mem_coe.2 ha))
    rwa [sys.directedSup_carrier_eq_union S hne hdir] at this
  obtain ⟨z, hz, huZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir u huU
  exact ⟨z, hz, sys.closure_le_element z hu huZ⟩

end InfoSys

end Scott1982
