import Scott1982.Proposition23

/-!
# Factoid 3.2 — every element contains Δ

**Factoid 3.2 (inventory).** Scott remarks after Def 3.1 that every element contains `Δ`,
because the least informative proposition is true of all elements.
-/

namespace Scott1982

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.2.** Every element contains `Δ`. -/
theorem factoid_3_2 (x : sys.Element) : sys.bot ∈ x.carrier := by
  have hempty : (↑(∅ : Finset α) : Set α) ⊆ x.carrier := by
    intro a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
  have hEnt : sys.Ent ∅ sys.bot := sys.ent_bot sys.con_empty
  exact x.closed ∅ sys.bot hempty hEnt

end InfoSys

end Scott1982
