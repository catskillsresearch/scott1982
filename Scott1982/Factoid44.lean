import Scott1982.Constructive
import Scott1982.Factoid43

/-!
# Factoid 4.4 — directed (and chain) unions are elements

**Factoid 4.4 (Scott §4).** The union of a nonempty directed family of elements is again
an element (hence a lub). In particular, unions of increasing chains are elements, so
`|A|` is a cpo under inclusion.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- Upward-directed family of elements: any two have a common upper bound in the family. -/
def IsDirected (S : Set sys.Element) : Prop :=
  ∀ (x y : sys.Element), x ∈ S → y ∈ S → ∃ z ∈ S, x ≤ z ∧ y ≤ z

/-- A chain: any two elements are comparable. -/
def IsChain (S : Set sys.Element) : Prop :=
  ∀ (x y : sys.Element), x ∈ S → y ∈ S → x ≤ y ∨ y ≤ x

theorem IsDirected_of_IsChain {S : Set sys.Element} (h : sys.IsChain S) : sys.IsDirected S := by
  intro x y hx hy
  rcases h x y hx hy with hxy | hyx
  · exact ⟨y, hy, hxy, le_rfl⟩
  · exact ⟨x, hx, le_rfl, hyx⟩

/-- Given `Y` whose tokens each lie in some member of a nonempty directed family, find a
single member containing all of `Y`. -/
theorem exists_mem_of_subset_directedUnion (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) (Y : Finset α)
    (hY : (Y : Set α) ⊆ sys.familyUnionCarrier S) :
    ∃ z ∈ S, (Y : Set α) ⊆ z.carrier := by
  induction Y using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, fun _ ha => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha))⟩
  | insert a s _ha ih =>
    have ha' : ∃ x ∈ S, a ∈ x.carrier :=
      hY (Finset.mem_coe.2 (Finset.mem_insert_self a s))
    have hs' : (s : Set α) ⊆ sys.familyUnionCarrier S := by
      intro b hb
      exact hY (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hb)))
    obtain ⟨xa, hxa, haS⟩ := ha'
    obtain ⟨xs, hxs, hsS⟩ := ih hs'
    obtain ⟨z, hz, hxa_le, hxs_le⟩ := hdir xa xs hxa hxs
    refine ⟨z, hz, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hb) with rfl | hb'
    · exact hxa_le haS
    · exact hxs_le (hsS (Finset.mem_coe.2 hb'))

/-- Directed families are finitely consistent on their carrier union. -/
theorem finitelyConsistent_of_directed (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    sys.IsFinitelyConsistent (sys.familyUnionCarrier S) := by
  intro Y hY
  obtain ⟨z, _hz, hYZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir Y hY
  exact z.consistent Y hYZ

/-- **Factoid 4.4.** Union of a nonempty directed family is an element (as `familySup`). -/
def directedSup (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S) :
    sys.Element :=
  sys.familySup S (sys.finitelyConsistent_of_directed S hne hdir)

theorem le_directedSup (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {x : sys.Element} (hx : x ∈ S) : x ≤ sys.directedSup S hne hdir :=
  sys.le_familySup S (sys.finitelyConsistent_of_directed S hne hdir) hx

theorem directedSup_le (S : Set sys.Element) (hne : S.Nonempty) (hdir : sys.IsDirected S)
    {z : sys.Element} (h : ∀ x ∈ S, x ≤ z) : sys.directedSup S hne hdir ≤ z :=
  sys.familySup_le S (sys.finitelyConsistent_of_directed S hne hdir) h

/-- For directed families, the lub carrier equals the raw union (already deductively closed). -/
theorem directedSup_carrier_eq_union (S : Set sys.Element) (hne : S.Nonempty)
    (hdir : sys.IsDirected S) :
    (sys.directedSup S hne hdir).carrier = sys.familyUnionCarrier S := by
  let hU := sys.finitelyConsistent_of_directed S hne hdir
  refine Set.Subset.antisymm ?_ (sys.subset_deductiveClosure _ hU)
  intro a ha
  obtain ⟨u, huU, hEnt⟩ := (ha : a ∈ (sys.deductiveClosure _ hU).carrier)
  obtain ⟨z, hz, huZ⟩ := sys.exists_mem_of_subset_directedUnion S hne hdir u huU
  exact ⟨z, hz, z.closed u a huZ hEnt⟩

/-- Chain unions are elements. -/
def chainSup (S : Set sys.Element) (hne : S.Nonempty) (hchain : sys.IsChain S) : sys.Element :=
  sys.directedSup S hne (sys.IsDirected_of_IsChain hchain)

end InfoSys

end Scott1982
