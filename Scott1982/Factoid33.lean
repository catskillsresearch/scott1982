import Scott1982.Factoid32

/-!
# Factoid 3.3 — the bottom element ⊥

**Factoid 3.3 (inventory).** Scott defines
`⊥_A = {X ∈ D_A ∣ {Δ_A} ⊢_A X}` and notes it is the least element of `|A|`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.3.** The bottom element `⊥ = {X ∣ {Δ} ⊢ X}`. -/
def botElement : sys.Element where
  carrier := {X | sys.Ent {sys.bot} X}
  consistent := by
    intro Y hY
    have hbot : ({sys.bot} : Finset α) ∈ sys.Con := sys.con_sing sys.bot
    have hEnt : sys.EntSet {sys.bot} Y := fun X hX => hY (Finset.mem_coe.2 hX)
    have hunion : {sys.bot} ∪' Y ∈ sys.Con := proposition_2_3_ii sys hbot hEnt
    exact sys.con_subset hunion (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    have hbot : ({sys.bot} : Finset α) ∈ sys.Con := sys.con_sing sys.bot
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet {sys.bot} Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (proposition_2_3_ii sys hbot hEntY) (subset_funion_right _ _)
    exact sys.ent_trans hbot hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt

/-- `⊥` is least. -/
theorem botElement_le (x : sys.Element) : sys.botElement ≤ x := by
  intro a ha
  have hsub : (↑({sys.bot} : Finset α) : Set α) ⊆ x.carrier := by
    intro b hb
    have hb' : b ∈ ({sys.bot} : Finset α) := Finset.mem_coe.1 hb
    rw [Finset.mem_singleton] at hb'
    subst hb'
    exact factoid_3_2 sys x
  exact x.closed {sys.bot} a hsub ha

end InfoSys

end Scott1982
