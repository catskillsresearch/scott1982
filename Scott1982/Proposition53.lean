import Scott1982.Approximable

/-!
# Proposition 5.3 — images, order, and the closure bridge

**Scott 1982, Proposition 5.3.** Remaining clauses after Def 5.2 / `toElement`:
singleton reduction (Scott’s remark before Def 5.2); (v) the bridge
`u f v ↔ v̄ ⊆ f(ū)`; (iii) pointwise order; (ii) extensionality via elements.
(i) and (iv) are already `toElement` / `toElement_mono` in `Approximable.lean`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}

private theorem singleton_funion_eq (a : β) (s : Finset β) :
    ({a} : Finset β) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with ha | hs
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp ha))
    · exact Finset.mem_insert_of_mem hs
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | hs
    · exact mem_funion.mpr (Or.inl (Finset.mem_singleton.mpr ha))
    · exact mem_funion.mpr (Or.inr hs)

/-- **Singleton reduction** (Scott, before Def 5.2). -/
theorem rel_iff_forall_singleton (f : ApproximableMap A B)
    {u : Finset α} {v : Finset β} (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    f.rel u v ↔ ∀ Y ∈ v, f.rel u ({Y} : Finset β) := by
  constructor
  · intro hrel Y hY
    exact f.mono hrel (proposition_2_3_iii A hu)
      (fun Z hZ => by
        rw [Finset.mem_singleton] at hZ
        subst hZ
        exact B.ent_refl hv hY)
      hu (B.con_sing Y)
  · intro hsing
    induction v using Finset.induction_on with
    | empty =>
      exact f.mono f.empty_rel (A.entSet_empty u) (B.entSet_empty ∅) hu B.con_empty
    | insert a s ha ih =>
      have hv' : insert a s ∈ B.Con := hv
      have hsCon : s ∈ B.Con := B.con_subset hv' (Finset.subset_insert a s)
      have h1 : f.rel u {a} := hsing a (Finset.mem_insert_self a s)
      have h2 : f.rel u s :=
        ih hsCon fun Y hY => hsing Y (Finset.mem_insert_of_mem hY)
      have hU : f.rel u ({a} ∪' s) := f.union_right h1 h2
      simpa [singleton_funion_eq] using hU

/-- **Proposition 5.3(v).** `u f v` iff `v̄ ⊆ f(ū)`. -/
theorem rel_iff_closure_le (f : ApproximableMap A B)
    {u : Finset α} {v : Finset β} (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    f.rel u v ↔ B.closure v hv ≤ f.toElement (A.closure u hu) := by
  constructor
  · intro hrel Y hY
    refine ⟨u, A.subset_closure hu, ?_⟩
    exact f.mono hrel (proposition_2_3_iii A hu)
      (fun Z hZ => by
        rw [Finset.mem_singleton] at hZ
        subst hZ
        exact hY)
      hu (B.con_sing Y)
  · intro hsub
    have hv_sub : ↑v ⊆ (f.toElement (A.closure u hu)).carrier :=
      fun y hy => hsub (B.subset_closure hv hy)
    obtain ⟨u', hu', hrel'⟩ := exists_rel_of_subset_image f (A.closure u hu) v hv_sub
    have hEnt : A.EntSet u u' := fun y hy => hu' (Finset.mem_coe.2 hy)
    exact f.mono hrel' hEnt (proposition_2_3_iii B hv) hu hv

/-- Relation inclusion of approximable maps. -/
def Le (f g : ApproximableMap A B) : Prop := ∀ ⦃u v⦄, f.rel u v → g.rel u v

/-- **Proposition 5.3(iii).** `f ⊆ g` iff `f(x) ⊆ g(x)` for all elements `x`. -/
theorem le_iff_toElement_le (f g : ApproximableMap A B) :
    Le f g ↔ ∀ x : A.Element, f.toElement x ≤ g.toElement x := by
  constructor
  · intro hfg x Y ⟨u, hu, hrel⟩
    exact ⟨u, hu, hfg hrel⟩
  · intro hpoint u v hrel
    have hu : u ∈ A.Con := f.rel_dom hrel
    have hv : v ∈ B.Con := f.rel_cod hrel
    have hbridge : B.closure v hv ≤ f.toElement (A.closure u hu) :=
      (f.rel_iff_closure_le hu hv).1 hrel
    have hsub : B.closure v hv ≤ g.toElement (A.closure u hu) :=
      le_trans hbridge (hpoint (A.closure u hu))
    exact (g.rel_iff_closure_le hu hv).2 hsub

/-- **Proposition 5.3(ii).** `f = g` iff `f(x) = g(x)` for all elements `x`. -/
theorem ext_iff_toElement (f g : ApproximableMap A B) :
    f = g ↔ ∀ x : A.Element, f.toElement x = g.toElement x := by
  constructor
  · intro h x
    rw [h]
  · intro hpoint
    refine ApproximableMap.ext fun u v => ?_
    constructor
    · intro hrel
      exact (le_iff_toElement_le f g).2 (fun x => (hpoint x) ▸ le_rfl) hrel
    · intro hrel
      exact (le_iff_toElement_le g f).2 (fun x => (hpoint x).symm ▸ le_rfl) hrel

end ApproximableMap

end InfoSys

end Scott1982
