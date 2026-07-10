import Scott1982.Proposition55
import Scott1982.Factoid34
import Scott1982.Factoid35

/-!
# Factoid 8.4 — a domain of domains (Scott’s sketch)

**Scott 1982, §8 (final remark).** Scott is deliberately sketchy: finite information
about a domain is packaged as an approximable map `r : P → P` on the powerset
domain `P` of the non-negative integers (with `0` as `Δ` and `1` as a reserved
rogue like `∇`). The maps satisfying (1)–(5) below are exactly the *elements* of
the domain of domains; the token-level InfoSys is said to arise from
`(P → P)` by a construction “similar to” `U` from `V`, with details deferred.

We formalize `P`, state (1)–(5) on `ApproximableMap P P`, package
`DomainApprox`, record Scott’s consistency remark, and exhibit one inhabitant
(the “flat” map that treats `1` as rogue). Functors-as-approximable-maps and
powerdomains are left external, as in the source.
-/

namespace Scott1982

open Scott1982.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84

/-! ## The powerset domain `P` (Scott) -/

/-- Minimal entailment on `ℕ` with `0 = Δ`: `u ⊢ n` iff `n = 0` or `n ∈ u`. -/
def PEnt (u : Finset ℕ) (n : ℕ) : Prop :=
  n = 0 ∨ n ∈ u

/-- **Powerset information system.** Tokens `ℕ`, bot `0`, every finite set
consistent, minimal entailment. -/
def P : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := PEnt
  con_subset := fun _ _ => trivial
  con_sing := fun _ => trivial
  ent_con := fun _ => trivial
  ent_bot := fun _ => Or.inl rfl
  ent_refl := fun _ ha => Or.inr ha
  ent_trans := by
    intro u v c _ _ hEnts hc
    rcases hc with rfl | hc
    · exact Or.inl rfl
    · exact hEnts c hc

theorem P_AllConsistent : P.AllConsistent := fun _ => trivial

/-- Scott’s shorthand `\bar n = {n}` as a finite set of tokens. -/
def bar (n : ℕ) : Finset ℕ := {n}

/-- Finite element `\bar n` (entailment closure of `{n}`). -/
def barElement (n : ℕ) : P.Element :=
  P.closure (bar n) trivial

theorem mem_barElement (n x : ℕ) :
    x ∈ (barElement n).carrier ↔ x = 0 ∨ x = n := by
  constructor
  · intro hx
    have : PEnt (bar n) x := (P.mem_closure_iff (by trivial : bar n ∈ P.Con)).1 hx
    rcases this with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_singleton.mp hx')
  · intro h
    rcases h with rfl | hn
    · exact (P.mem_closure_iff (by trivial : bar n ∈ P.Con)).2 (Or.inl rfl)
    · rw [hn]
      exact (P.mem_closure_iff (by trivial : bar n ∈ P.Con)).2
        (Or.inr (Finset.mem_singleton_self n))

/-- Bottom element `⊥` of `|P|` (closure of `∅`). -/
def botElement : P.Element :=
  P.closure ∅ trivial

theorem mem_botElement (x : ℕ) : x ∈ botElement.carrier ↔ x = 0 := by
  constructor
  · intro hx
    have : PEnt ∅ x := (P.mem_closure_iff (by trivial : (∅ : Finset ℕ) ∈ P.Con)).1 hx
    rcases this with rfl | hx'
    · rfl
    · exact False.elim (Finset.notMem_empty _ hx')
  · rintro rfl
    exact (P.mem_closure_iff (by trivial : (∅ : Finset ℕ) ∈ P.Con)).2 (Or.inl rfl)

/-- Top element `⊤` of `|P|` (all tokens). -/
def topElement : P.Element :=
  P.topElement P_AllConsistent

theorem mem_topElement (x : ℕ) : x ∈ topElement.carrier := trivial

theorem barElement_zero_eq_bot : barElement 0 = botElement := by
  apply le_antisymm
  · intro x hx
    rcases (mem_barElement 0 x).1 hx with rfl | rfl
    · exact (mem_botElement 0).2 rfl
    · exact (mem_botElement 0).2 rfl
  · intro x hx
    have : x = 0 := (mem_botElement x).1 hx
    subst this
    exact (mem_barElement 0 0).2 (Or.inl rfl)

/-! ## Scott’s conditions (1)–(5) on `r : P → P` -/

/-- (1) `I_P ⊆ r` (reflexivity of the induced entailment). -/
def ReflApprox (r : ApproximableMap P P) : Prop :=
  ∀ {u v : Finset ℕ}, (idMap P).rel u v → r.rel u v

/-- (2) `r ∘ r = r` (transitivity / idempotence). -/
def IdemApprox (r : ApproximableMap P P) : Prop :=
  ApproximableMap.comp r r = r

/-- (3) `\bar 0 ⊆ r(⊥)` — `0` plays the rôle of `Δ`. -/
def BotApprox (r : ApproximableMap P P) : Prop :=
  (barElement 0).carrier ⊆ (r.toElement botElement).carrier

/-- (4) `⊤ = r(\bar 1)` — `1` plays the rôle of the rogue `∇`. -/
def RogueApprox (r : ApproximableMap P P) : Prop :=
  r.toElement (barElement 1) = topElement

/-- (5) `\bar 1 ⊈ r(\bar 0)` — `1` is excluded as inconsistent at the bottom. -/
def ConsistentApprox (r : ApproximableMap P P) : Prop :=
  ¬ ((barElement 1).carrier ⊆ (r.toElement (barElement 0)).carrier)

/-- Scott (1)–(5): approximable maps that present entailment relations / domains. -/
structure IsDomainApprox (r : ApproximableMap P P) : Prop where
  refl : ReflApprox r
  idem : IdemApprox r
  bot : BotApprox r
  rogue : RogueApprox r
  consistent : ConsistentApprox r

/-- Elements of the domain of domains (Scott’s assertion after (1)–(5)). -/
def DomainApprox : Type :=
  { r : ApproximableMap P P // IsDomainApprox r }

/-- Scott’s consistency remark: for such an `r`, a finite `u` is “consistent”
when `\bar 1 ⊈ r(\bar u)`. -/
def scottCon (r : ApproximableMap P P) (u : Finset ℕ) : Prop :=
  ¬ ((barElement 1).carrier ⊆
      (r.toElement (P.closure u (by trivial))).carrier)

theorem scottCon_empty_iff_consistent (r : ApproximableMap P P) :
    scottCon r ∅ ↔ ConsistentApprox r := by
  simp only [scottCon, ConsistentApprox, barElement_zero_eq_bot]
  rfl

/-! ## (3) is automatic for any approximable map -/

theorem BotApprox_any (r : ApproximableMap P P) : BotApprox r := by
  intro x hx
  have hx0 : x = 0 := by
    rcases (mem_barElement 0 x).1 hx with rfl | rfl <;> rfl
  subst hx0
  refine ⟨∅, fun a ha => False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha)), ?_⟩
  have hempty := r.empty_rel
  have hbot : P.EntSet ∅ ({0} : Finset ℕ) := by
    intro z hz
    rw [Finset.mem_singleton] at hz; subst hz
    exact Or.inl rfl
  exact r.mono hempty (P.entSet_empty ∅) hbot trivial trivial

/-! ## Example: flat domain map (treat `1` as rogue) -/

/-- If `1 ∈ u`, accept any `v`; else require `v ⊆ u ∪ {0}` and `1 ∉ v`. -/
def flatRel (u v : Finset ℕ) : Prop :=
  (1 ∈ u) ∨ ((∀ n ∈ v, n = 0 ∨ n ∈ u) ∧ 1 ∉ v)

theorem flatRel_of_mem_one {u v : Finset ℕ} (h : 1 ∈ u) : flatRel u v :=
  Or.inl h

theorem flatRel_empty : flatRel ∅ ∅ :=
  Or.inr ⟨fun _ hn => False.elim (Finset.notMem_empty _ hn), Finset.notMem_empty _⟩

def flatMap : ApproximableMap P P where
  rel := flatRel
  rel_dom := fun _ => trivial
  rel_cod := fun _ => trivial
  empty_rel := flatRel_empty
  union_right := by
    intro u v v' hv hv'
    rcases hv with h1 | ⟨hv, hv1⟩
    · exact Or.inl h1
    · rcases hv' with h1 | ⟨hv', hv1'⟩
      · exact Or.inl h1
      · refine Or.inr ⟨?_, ?_⟩
        · intro n hn
          rcases mem_funion.1 hn with h | h
          · exact hv n h
          · exact hv' n h
        · intro h1
          rcases mem_funion.1 h1 with h | h
          · exact hv1 h
          · exact hv1' h
  mono := by
    intro u u' v v' hrel hEntu hEntv _ _
    rcases hrel with h1 | ⟨hv, hv1⟩
    · -- 1 ∈ u; show 1 ∈ u' from EntSet
      have h := hEntu 1 h1
      rcases h with h0 | h1'
      · exact False.elim (by cases h0)
      · exact Or.inl h1'
    · refine Or.inr ⟨?_, ?_⟩
      · intro n hn
        have hn' := hEntv n hn
        rcases hn' with rfl | hn'
        · exact Or.inl rfl
        · have hn'' := hv n hn'
          rcases hn'' with rfl | hn''
          · exact Or.inl rfl
          · have hu' := hEntu n hn''
            rcases hu' with rfl | hu'
            · exact Or.inl rfl
            · exact Or.inr hu'
      · intro h1v
        have h := hEntv 1 h1v
        rcases h with h0 | h1v'
        · exact False.elim (by cases h0)
        · exact hv1 h1v'

theorem flatMap_refl : ReflApprox flatMap := by
  intro u v ⟨_, _, hEnt⟩
  by_cases h1 : 1 ∈ u
  · exact Or.inl h1
  · refine Or.inr ⟨?_, ?_⟩
    · intro n hn; exact hEnt n hn
    · intro h1v
      have h := hEnt 1 h1v
      rcases h with h0 | h
      · exact absurd h0 (by decide)
      · exact h1 h

theorem flatMap_toElement_of_mem_one {x : P.Element} (h1 : 1 ∈ x.carrier) :
    flatMap.toElement x = topElement := by
  apply le_antisymm
  · intro _ _; exact mem_topElement _
  · intro n _
    refine ⟨{1}, ?_, Or.inl (Finset.mem_singleton_self 1)⟩
    intro a ha
    have : a = 1 := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
    subst this; exact h1

theorem flatMap_rogue : RogueApprox flatMap :=
  flatMap_toElement_of_mem_one ((mem_barElement 1 1).2 (Or.inr rfl))

theorem flatMap_consistent : ConsistentApprox flatMap := by
  intro hsub
  have h1 : 1 ∈ (barElement 1).carrier := (mem_barElement 1 1).2 (Or.inr rfl)
  have h1' : 1 ∈ (flatMap.toElement (barElement 0)).carrier := hsub h1
  rcases (mem_toElement flatMap (barElement 0)).1 h1' with ⟨u, hu, hrel⟩
  rcases hrel with h1u | ⟨_, hv1⟩
  · have : 1 ∈ (barElement 0).carrier := hu (Finset.mem_coe.2 h1u)
    rcases (mem_barElement 0 1).1 this with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact hv1 (Finset.mem_singleton_self 1)

theorem flatMap_idem : IdemApprox flatMap := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨w, hf, hg⟩
    rcases hf with h1u | ⟨hw, hw1⟩
    · exact Or.inl h1u
    · rcases hg with h1w | ⟨hv, hv1⟩
      · exact False.elim (hw1 h1w)
      · refine Or.inr ⟨?_, hv1⟩
        · intro n hn
          have hn' := hv n hn
          rcases hn' with rfl | hn'
          · exact Or.inl rfl
          · exact hw n hn'
  · intro h
    rcases h with h1u | ⟨hv, hv1⟩
    · exact ⟨insert 1 v, Or.inl h1u, Or.inl (Finset.mem_insert_self 1 v)⟩
    · exact ⟨v, Or.inr ⟨hv, hv1⟩, Or.inr ⟨fun n hn => Or.inr hn, hv1⟩⟩

theorem flatMap_isDomain : IsDomainApprox flatMap where
  refl := flatMap_refl
  idem := flatMap_idem
  bot := BotApprox_any flatMap
  rogue := flatMap_rogue
  consistent := flatMap_consistent

/-- Witness that Scott’s (1)–(5) are inhabited. -/
def flatDomainApprox : DomainApprox :=
  ⟨flatMap, flatMap_isDomain⟩

/-! ## Identity fails (4): `I_P` is not a domain map -/

theorem not_RogueApprox_idMap : ¬ RogueApprox (idMap P) := by
  intro h
  have h2 : 2 ∈ ((idMap P).toElement (barElement 1)).carrier := by
    rw [h]; exact mem_topElement 2
  rcases (mem_toElement (idMap P) (barElement 1)).1 h2 with ⟨u, hu, hrel⟩
  have hEnt : P.EntSet u {2} := hrel.2.2
  have h2u := hEnt 2 (Finset.mem_singleton_self 2)
  rcases h2u with h0 | h2u
  · exact absurd h0 (by decide)
  · have : 2 ∈ (barElement 1).carrier := hu (Finset.mem_coe.2 h2u)
    rcases (mem_barElement 1 2).1 this with h0 | h1'
    · exact absurd h0 (by decide)
    · exact absurd h1' (by decide)

end Factoid84

end Scott1982
