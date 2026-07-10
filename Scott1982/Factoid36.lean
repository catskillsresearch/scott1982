import Scott1982.Constructive
import Scott1982.Factoid35

/-!
# Factoid 3.6 — every element is the directed union of its finite approximations

**Factoid 3.6 (Scott §3 / inventory).** For every element `x ∈ |A|`,
`x` equals the union of all `ū` with `u ∈ Con` and `u ⊆ x`.
Intuitively: every element is the limit of its finite approximations. The union is directed.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- If `w` entails every member of `u`, then `ū ⊆ w̄`. -/
theorem closure_le_of_entSet {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (h : sys.EntSet w u) : sys.closure u hu ≤ sys.closure w hw := by
  intro a ha
  exact sys.ent_trans hw hu h ha

/-- Monotonicity of closure under inclusion of consistent sets. -/
theorem closure_le_of_subset {u w : Finset α} (hu : u ∈ sys.Con) (hw : w ∈ sys.Con)
    (hsub : u ⊆ w) : sys.closure u hu ≤ sys.closure w hw :=
  sys.closure_le_of_entSet hu hw fun _ hy => sys.ent_refl hw (hsub hy)

/-- Finite approximations below `x` really do approximate `x`. -/
theorem closure_le_element (x : sys.Element) {u : Finset α} (hu : u ∈ sys.Con)
    (hsub : ↑u ⊆ x.carrier) : sys.closure u hu ≤ x := by
  intro a ha
  exact x.closed u a hsub ha

/-- The set-theoretic union of all finite approximations of `x`. -/
def approxUnion (x : sys.Element) : Set α :=
  {a | ∃ (u : Finset α) (hu : u ∈ sys.Con),
    ↑u ⊆ x.carrier ∧ a ∈ (sys.closure u hu).carrier}

/-- **Factoid 3.6.** Membership in `x` iff membership in some finite approximation `ū ⊆ x`. -/
theorem mem_element_iff_mem_closure (x : sys.Element) (a : α) :
    a ∈ x.carrier ↔ a ∈ sys.approxUnion x := by
  constructor
  · intro ha
    refine ⟨{a}, sys.con_sing a, ?_, ?_⟩
    · intro b hb
      have hb' : b ∈ ({a} : Finset α) := Finset.mem_coe.1 hb
      rw [Finset.mem_singleton] at hb'
      subst hb'
      exact ha
    · exact sys.ent_refl (sys.con_sing a) (Finset.mem_singleton_self a)
  · rintro ⟨u, hu, hsub, ha⟩
    exact x.closed u a hsub ha

/-- **Factoid 3.6.** Carrier form: `x = ⋃{ū | u ∈ Con, u ⊆ x}`. -/
theorem element_eq_approxUnion (x : sys.Element) : x.carrier = sys.approxUnion x := by
  ext a
  exact sys.mem_element_iff_mem_closure x a

/-- The family of finite approximations to `x` is directed under `≤`. -/
theorem closures_directed (x : sys.Element) {u v : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huX : ↑u ⊆ x.carrier) (hvX : ↑v ⊆ x.carrier) :
    ∃ (w : Finset α) (hw : w ∈ sys.Con),
      ↑w ⊆ x.carrier ∧
        sys.closure u hu ≤ sys.closure w hw ∧
        sys.closure v hv ≤ sys.closure w hw := by
  let w := u ∪' v
  have hwX : ↑w ⊆ x.carrier := by
    intro a ha
    rcases mem_funion.1 (Finset.mem_coe.1 ha) with h | h
    · exact huX (Finset.mem_coe.2 h)
    · exact hvX (Finset.mem_coe.2 h)
  have hw : w ∈ sys.Con := x.consistent w hwX
  refine ⟨w, hw, hwX, ?_, ?_⟩
  · exact sys.closure_le_of_subset hu hw (subset_funion_left u v)
  · exact sys.closure_le_of_subset hv hw (subset_funion_right u v)

end InfoSys

end Scott1982
