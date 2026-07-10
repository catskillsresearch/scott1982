import Scott1982.Proposition56
import Scott1982.Factoid33

/-!
# Factoid 6.5 — the unit domain

**Scott 1982 (end of §6, after Prop 6.2).** The trivial product of no factors is the
*unit* information system `1` with `D_1 = {Δ_1}`. It has a unique element `⊥_1`.
Every approximable map `1 → A` is constant, and there is a unique approximable map
`A → 1`, namely `const(⊥_1)`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

/-- **Factoid 6.5.** The unit information system on a singleton token type. -/
def unitSystem : InfoSys PUnit where
  bot := ⟨⟩
  Con := Set.univ
  Ent := fun _ _ => True
  con_subset := by
    intro u v _ _
    exact trivial
  con_sing := by
    intro _
    exact trivial
  ent_con := by
    intro u a _
    exact trivial
  ent_bot := by
    intro u _
    exact trivial
  ent_refl := by
    intro u a _ _
    exact trivial
  ent_trans := by
    intro u v c _ _ _ _
    exact trivial

/-- The unique element of `|1|` is `⊥`. -/
theorem unitElement_eq_bot (x : unitSystem.Element) : x = unitSystem.botElement := by
  apply le_antisymm
  · intro a ha
    cases a
    exact trivial
  · exact botElement_le unitSystem x

namespace ApproximableMap

variable {α : Type*} [DecidableEq α] {A : InfoSys α}

/-- Every approximable map out of `1` is constant (Scott Factoid 6.5). -/
theorem approxMap_from_unit_eq_const (f : ApproximableMap unitSystem A) :
    f = constMap (A := unitSystem) (f.toElement unitSystem.botElement) :=
  constMap_unique (f.toElement unitSystem.botElement) f fun x => by
    rw [unitElement_eq_bot x]

/-- There is a unique approximable map into `1`, namely `const(⊥_1)`. -/
theorem approxMap_to_unit_eq_const (f : ApproximableMap A unitSystem) :
    f = constMap (A := A) unitSystem.botElement :=
  constMap_unique unitSystem.botElement f fun x => unitElement_eq_bot (f.toElement x)

/-- Elements of `|A|` are in bijection with approximable maps `1 → A` via `const`. -/
theorem toElement_constMap_bot (b : A.Element) :
    (constMap (A := unitSystem) b).toElement unitSystem.botElement = b :=
  constMap_toElement b unitSystem.botElement

end ApproximableMap

end InfoSys

end Scott1982
