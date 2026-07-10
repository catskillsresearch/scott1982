import Scott1982.Approximable

/-!
# Proposition 5.4 — the identity approximable mapping

**Scott 1982, Proposition 5.4.** `u I_A v ↔ u ⊢_A v`, and `I_A(x) = x`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- **Proposition 5.4(i).** Identity approximable mapping given by entailment. -/
def idMap : ApproximableMap A A where
  rel u v := u ∈ A.Con ∧ v ∈ A.Con ∧ A.EntSet u v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, A.con_empty, A.entSet_empty ∅⟩
  union_right := by
    rintro u v v' ⟨hu, _hv, huv⟩ ⟨_, _hv', huv'⟩
    have hEnt : A.EntSet u (v ∪' v') := proposition_2_3_vi (sys := A) huv huv'
    have hBig : u ∪' (v ∪' v') ∈ A.Con :=
      proposition_2_3_ii (sys := A) (u := u) (v := v ∪' v') hu hEnt
    have hCon : v ∪' v' ∈ A.Con :=
      A.con_subset hBig (subset_funion_right u (v ∪' v'))
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, huv⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    exact proposition_2_3_iv A hu' hv
      (proposition_2_3_iv A hu' hu hEntu huv) hEntv

/-- **Proposition 5.4(ii).** `I_A(x) = x`. -/
theorem idMap_toElement (x : A.Element) : (idMap A).toElement x = x := by
  apply le_antisymm
  · intro Y ⟨u, hu, hrel⟩
    -- hrel.2.2 : EntSet u {Y}, so Ent u Y
    have hEnt : A.Ent u Y := hrel.2.2 Y (Finset.mem_singleton_self Y)
    exact x.closed u Y hu hEnt
  · intro Y hY
    refine ⟨{Y}, ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ ({Y} : Finset α) := Finset.mem_coe.1 hz
      rw [Finset.mem_singleton] at hz'
      rw [hz']
      exact hY
    · refine ⟨A.con_sing Y, A.con_sing Y, ?_⟩
      exact proposition_2_3_iii A (A.con_sing Y)

end InfoSys

end Scott1982
