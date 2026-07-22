/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Constructive
import Scott1982.Proposition23

/-!
# Product of information systems — Definition 6.1

**Scott 1982, Definition 6.1.** Tokens of `A × B` are pairs of the form
`(X, Δ_B)` or `(Δ_A, Y)`, with `Δ = (Δ_A, Δ_B)`. Consistency and entailment act
independently on the two projections `fst u` and `snd u`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Scott 6.1(i): a product token is `(X, Δ_B)` or `(Δ_A, Y)`. -/
def IsProdToken (A : InfoSys α) (B : InfoSys β) (p : α × β) : Prop :=
  p.1 = A.bot ∨ p.2 = B.bot

instance (A : InfoSys α) (B : InfoSys β) (p : α × β) : Decidable (IsProdToken A B p) :=
  if h1 : p.1 = A.bot then isTrue (Or.inl h1)
  else if h2 : p.2 = B.bot then isTrue (Or.inr h2)
  else isFalse fun h => h.elim h1 h2

/-- Token type of the product system `A × B`. -/
def ProdToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : α × β // IsProdToken A B p}

instance (A : InfoSys α) (B : InfoSys β) : DecidableEq (ProdToken A B) :=
  Subtype.instDecidableEq

variable (A : InfoSys α) (B : InfoSys β)

/-- Product bottom `Δ_{A×B} = (Δ_A, Δ_B)`. -/
def prodBot : ProdToken A B :=
  ⟨(A.bot, B.bot), Or.inl rfl⟩

private instance instLeftCommutativeFstInsert :
    LeftCommutative fun p : ProdToken A B => (insert p.val.1 : Finset α → Finset α) :=
  ⟨fun p q s => insert_comm' p.val.1 q.val.1 s⟩

private instance instLeftCommutativeSndInsert :
    LeftCommutative fun p : ProdToken A B => (insert p.val.2 : Finset β → Finset β) :=
  ⟨fun p q s => insert_comm' p.val.2 q.val.2 s⟩

/-- Left projection of a finite set of product tokens (Scott 6.1). -/
def fstFinset (u : Finset (ProdToken A B)) : Finset α :=
  Multiset.foldr (fun p : ProdToken A B => insert p.val.1) (∅ : Finset α)
    (u.filter (fun p => p.val.2 = B.bot)).1

/-- Right projection of a finite set of product tokens (Scott 6.1). -/
def sndFinset (u : Finset (ProdToken A B)) : Finset β :=
  Multiset.foldr (fun p : ProdToken A B => insert p.val.2) (∅ : Finset β)
    (u.filter (fun p => p.val.1 = A.bot)).1

private theorem mem_foldr_fst (s : Multiset (ProdToken A B)) (x : α) :
    x ∈ Multiset.foldr (fun p : ProdToken A B => insert p.val.1) (∅ : Finset α) s ↔
      ∃ p ∈ s, p.val.1 = x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨p, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hx | ⟨q, hq, hq1⟩)
      · exact ⟨p, Or.inl rfl, hx.symm⟩
      · exact ⟨q, Or.inr hq, hq1⟩
    · rintro ⟨q, hq, hq1⟩
      rcases hq with rfl | hq
      · exact Or.inl hq1.symm
      · exact Or.inr ⟨q, hq, hq1⟩

private theorem mem_foldr_snd (s : Multiset (ProdToken A B)) (y : β) :
    y ∈ Multiset.foldr (fun p : ProdToken A B => insert p.val.2) (∅ : Finset β) s ↔
      ∃ p ∈ s, p.val.2 = y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨p, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hy | ⟨q, hq, hq2⟩)
      · exact ⟨p, Or.inl rfl, hy.symm⟩
      · exact ⟨q, Or.inr hq, hq2⟩
    · rintro ⟨q, hq, hq2⟩
      rcases hq with rfl | hq
      · exact Or.inl hq2.symm
      · exact Or.inr ⟨q, hq, hq2⟩

theorem mem_fstFinset {u : Finset (ProdToken A B)} {x : α} :
    x ∈ fstFinset A B u ↔ ∃ p ∈ u, p.val.2 = B.bot ∧ p.val.1 = x := by
  unfold fstFinset
  rw [mem_foldr_fst]
  constructor
  · rintro ⟨p, hp, hx⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hx⟩
  · rintro ⟨p, hp, hbot, hx⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hx⟩

theorem mem_sndFinset {u : Finset (ProdToken A B)} {y : β} :
    y ∈ sndFinset A B u ↔ ∃ p ∈ u, p.val.1 = A.bot ∧ p.val.2 = y := by
  unfold sndFinset
  rw [mem_foldr_snd]
  constructor
  · rintro ⟨p, hp, hy⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hy⟩
  · rintro ⟨p, hp, hbot, hy⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hy⟩

theorem fstFinset_empty : fstFinset A B (∅ : Finset (ProdToken A B)) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨_, hp, _, _⟩
    exact False.elim (Finset.notMem_empty _ hp)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem sndFinset_empty : sndFinset A B (∅ : Finset (ProdToken A B)) = ∅ := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨_, hp, _, _⟩
    exact False.elim (Finset.notMem_empty _ hp)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem fstFinset_mono {u v : Finset (ProdToken A B)} (h : v ⊆ u) :
    fstFinset A B v ⊆ fstFinset A B u := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
  exact (mem_fstFinset A B).2 ⟨p, h hp, hbot, hx'⟩

theorem sndFinset_mono {u v : Finset (ProdToken A B)} (h : v ⊆ u) :
    sndFinset A B v ⊆ sndFinset A B u := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  exact (mem_sndFinset A B).2 ⟨p, h hp, hbot, hy'⟩

theorem fstFinset_insert_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 = B.bot) :
    fstFinset A B (insert p u) = insert p.val.1 (fstFinset A B u) := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hx'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩))
  · intro hx
    rcases Finset.mem_insert.mp hx with hx' | hx'
    · exact (mem_fstFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hx'.symm⟩
    · rcases (mem_fstFinset A B).1 hx' with ⟨q, hq, hbot, hxq⟩
      exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hxq⟩

theorem fstFinset_insert_not_left (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.2 ≠ B.bot) :
    fstFinset A B (insert p u) = fstFinset A B u := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_fstFinset A B).2 ⟨q, hq, hbot, hx'⟩
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot, hx'⟩
    exact (mem_fstFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hx'⟩

theorem sndFinset_insert_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 = A.bot) :
    sndFinset A B (insert p u) = insert p.val.2 (sndFinset A B u) := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert.mpr (Or.inl hy'.symm)
    · exact Finset.mem_insert.mpr (Or.inr ((mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_sndFinset A B).2 ⟨p, Finset.mem_insert_self p u, hp, hy'.symm⟩
    · rcases (mem_sndFinset A B).1 hy' with ⟨q, hq, hbot, hyq⟩
      exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hyq⟩

theorem sndFinset_insert_not_right (u : Finset (ProdToken A B)) (p : ProdToken A B)
    (hp : p.val.1 ≠ A.bot) :
    sndFinset A B (insert p u) = sndFinset A B u := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact False.elim (hp hbot)
    · exact (mem_sndFinset A B).2 ⟨q, hq, hbot, hy'⟩
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot, hy'⟩
    exact (mem_sndFinset A B).2 ⟨q, Finset.mem_insert_of_mem hq, hbot, hy'⟩

theorem fstFinset_singleton_left (p : ProdToken A B) (hp : p.val.2 = B.bot) :
    fstFinset A B {p} = {p.val.1} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, fstFinset_insert_left A B ∅ p hp,
    fstFinset_empty]
  rfl

theorem sndFinset_singleton_right (p : ProdToken A B) (hp : p.val.1 = A.bot) :
    sndFinset A B {p} = {p.val.2} := by
  rw [show ({p} : Finset _) = insert p ∅ from rfl, sndFinset_insert_right A B ∅ p hp,
    sndFinset_empty]
  rfl

theorem fstFinset_funion (u v : Finset (ProdToken A B)) :
    fstFinset A B (u ∪' v) = fstFinset A B u ∪' fstFinset A B v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_fstFinset A B).2 ⟨p, hp, hbot, hx'⟩))
  · intro hx
    rcases mem_funion.mp hx with hx | hx
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hx'⟩
    · rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
      exact (mem_fstFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hx'⟩

theorem sndFinset_funion (u v : Finset (ProdToken A B)) :
    sndFinset A B (u ∪' v) = sndFinset A B u ∪' sndFinset A B v := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_sndFinset A B).2 ⟨p, hp, hbot, hy'⟩))
  · intro hy
    rcases mem_funion.mp hy with hy | hy
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hbot, hy'⟩
    · rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
      exact (mem_sndFinset A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hbot, hy'⟩

/-- Consistency for the product system (Scott 6.1(iii)). -/
def ProdCon (u : Finset (ProdToken A B)) : Prop :=
  fstFinset A B u ∈ A.Con ∧ sndFinset A B u ∈ B.Con

/-- Entailment for the product system (Scott 6.1(iv'), (iv'')).
Includes `ProdCon` so both projections stay available for `ent_con`. -/
def ProdEnt (u : Finset (ProdToken A B)) (p : ProdToken A B) : Prop :=
  ProdCon A B u ∧
    (p.val.2 = B.bot → A.Ent (fstFinset A B u) p.val.1) ∧
      (p.val.1 = A.bot → B.Ent (sndFinset A B u) p.val.2)

/-- **Definition 6.1.** The product information system `A × B`. -/
def productSystem : InfoSys (ProdToken A B) where
  bot := prodBot A B
  Con := {u | ProdCon A B u}
  Ent := ProdEnt A B
  con_subset := by
    intro u v hu hv
    exact ⟨A.con_subset hu.1 (fstFinset_mono A B hv),
      B.con_subset hu.2 (sndFinset_mono A B hv)⟩
  con_sing := by
    intro p
    refine ⟨?_, ?_⟩
    · rcases p.property with h1 | h2
      · by_cases h2 : p.val.2 = B.bot
        · have hpeq : p = prodBot A B := Subtype.ext (Prod.ext h1 h2)
          subst hpeq
          rw [fstFinset_singleton_left A B (prodBot A B) rfl]
          exact A.con_sing A.bot
        · have hfst : fstFinset A B {p} = ∅ := by
            ext x
            constructor
            · intro hx
              rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot', _⟩
              have hq' : q = p := Finset.mem_singleton.mp hq
              subst hq'
              exact False.elim (h2 hbot')
            · intro hx
              exact False.elim (Finset.notMem_empty x hx)
          rw [hfst]
          exact A.con_empty
      · rw [fstFinset_singleton_left A B p h2]
        exact A.con_sing p.val.1
    · rcases p.property with h1 | h2
      · rw [sndFinset_singleton_right A B p h1]
        exact B.con_sing p.val.2
      · by_cases h1 : p.val.1 = A.bot
        · have hpeq : p = prodBot A B := Subtype.ext (Prod.ext h1 h2)
          subst hpeq
          rw [sndFinset_singleton_right A B (prodBot A B) rfl]
          exact B.con_sing B.bot
        · have hsnd : sndFinset A B {p} = ∅ := by
            ext y
            constructor
            · intro hy
              rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot', _⟩
              have hq' : q = p := Finset.mem_singleton.mp hq
              subst hq'
              exact False.elim (h1 hbot')
            · intro hy
              exact False.elim (Finset.notMem_empty y hy)
          rw [hsnd]
          exact B.con_empty
  ent_con := by
    intro u p ⟨⟨hfst, hsnd⟩, hL, hR⟩
    refine ⟨?_, ?_⟩
    · by_cases hp2 : p.val.2 = B.bot
      · rw [fstFinset_insert_left A B u p hp2]
        exact A.ent_con (hL hp2)
      · rw [fstFinset_insert_not_left A B u p hp2]
        exact hfst
    · by_cases hp1 : p.val.1 = A.bot
      · rw [sndFinset_insert_right A B u p hp1]
        exact B.ent_con (hR hp1)
      · rw [sndFinset_insert_not_right A B u p hp1]
        exact hsnd
  ent_bot := by
    intro u hu
    exact ⟨hu, fun _ => A.ent_bot hu.1, fun _ => B.ent_bot hu.2⟩
  ent_refl := by
    intro u p hu hp
    refine ⟨hu, ?_, ?_⟩
    · intro hbot
      exact A.ent_refl hu.1 ((mem_fstFinset A B).2 ⟨p, hp, hbot, rfl⟩)
    · intro hbot
      exact B.ent_refl hu.2 ((mem_sndFinset A B).2 ⟨p, hp, hbot, rfl⟩)
  ent_trans := by
    intro u v c hv hu hEnts hEntc
    refine ⟨hv, ?_, ?_⟩
    · intro hbot
      have hfst : ∀ y ∈ fstFinset A B u, A.Ent (fstFinset A B v) y := by
        intro y hy
        rcases (mem_fstFinset A B).1 hy with ⟨q, hq, hq2, rfl⟩
        exact (hEnts q hq).2.1 hq2
      exact A.ent_trans hv.1 hu.1 hfst (hEntc.2.1 hbot)
    · intro hbot
      have hsnd : ∀ y ∈ sndFinset A B u, B.Ent (sndFinset A B v) y := by
        intro y hy
        rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hq1, rfl⟩
        exact (hEnts q hq).2.2 hq1
      exact B.ent_trans hv.2 hu.2 hsnd (hEntc.2.2 hbot)

end InfoSys

end Scott1982
