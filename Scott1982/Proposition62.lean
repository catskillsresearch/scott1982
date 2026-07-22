/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Product
import Scott1982.Proposition53
import Scott1982.Proposition55

/-!
# Proposition 6.2 — product projections and pairing

**Scott 1982, Proposition 6.2.** Approximable `fst`, `snd`, and unique pairing
`⟨f, g⟩` with `fst ∘ ⟨f, g⟩ = f` and `snd ∘ ⟨f, g⟩ = g`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

/-- Left-tagged product token `(X, Δ_B)`. -/
def mkLeft (x : α) : ProdToken A B :=
  ⟨(x, B.bot), Or.inr rfl⟩

/-- Right-tagged product token `(Δ_A, Y)`. -/
def mkRight (y : β) : ProdToken A B :=
  ⟨(A.bot, y), Or.inl rfl⟩

private instance instLeftCommutativeMkLeftInsert :
    LeftCommutative fun x : α =>
      (insert (mkLeft A B x) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkLeft A B x) (mkLeft A B y) s⟩

private instance instLeftCommutativeMkRightInsert :
    LeftCommutative fun y : β =>
      (insert (mkRight A B y) : Finset (ProdToken A B) → Finset (ProdToken A B)) :=
  ⟨fun x y s => insert_comm' (mkRight A B x) (mkRight A B y) s⟩

/-- Embed a finite set of `A`-tokens as left product tokens. -/
def liftLeft (v : Finset α) : Finset (ProdToken A B) :=
  Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) v.1

/-- Embed a finite set of `B`-tokens as right product tokens. -/
def liftRight (w : Finset β) : Finset (ProdToken A B) :=
  Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) w.1

private theorem mem_foldr_liftLeft (s : Multiset α) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ x ∈ s, p = mkLeft A B x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hx, _⟩
      exact False.elim (by cases hx)
  · intro x t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨y, hy, hp⟩)
      · exact ⟨x, Or.inl rfl, hp⟩
      · exact ⟨y, Or.inr hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      rcases hy with rfl | hy
      · exact Or.inl hp
      · exact Or.inr ⟨y, hy, hp⟩

private theorem mem_foldr_liftRight (s : Multiset β) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ y ∈ s, p = mkRight A B y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hy, _⟩
      exact False.elim (by cases hy)
  · intro y t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨z, hz, hp⟩)
      · exact ⟨y, Or.inl rfl, hp⟩
      · exact ⟨z, Or.inr hz, hp⟩
    · rintro ⟨z, hz, hp⟩
      rcases hz with rfl | hz
      · exact Or.inl hp
      · exact Or.inr ⟨z, hz, hp⟩
theorem mem_liftLeft {v : Finset α} {p : ProdToken A B} :
    p ∈ liftLeft A B v ↔ ∃ x ∈ v, p = mkLeft A B x := by
  unfold liftLeft
  exact mem_foldr_liftLeft A B v.1 p

theorem mem_liftRight {w : Finset β} {p : ProdToken A B} :
    p ∈ liftRight A B w ↔ ∃ y ∈ w, p = mkRight A B y := by
  unfold liftRight
  exact mem_foldr_liftRight A B w.1 p

theorem fstFinset_liftLeft (v : Finset α) : fstFinset A B (liftLeft A B v) = v := by
  ext x
  constructor
  · intro hx
    rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
    rcases (mem_liftLeft A B).1 hp with ⟨y, hy, hp'⟩
    subst hp'
    exact (show y = x from hx').symm ▸ hy
  · intro hx
    exact (mem_fstFinset A B).2
      ⟨mkLeft A B x, (mem_liftLeft A B).2 ⟨x, hx, rfl⟩, rfl, rfl⟩

theorem sndFinset_liftRight (w : Finset β) : sndFinset A B (liftRight A B w) = w := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases (mem_liftRight A B).1 hp with ⟨z, hz, hp'⟩
    subst hp'
    exact (show z = y from hy').symm ▸ hz
  · intro hy
    exact (mem_sndFinset A B).2
      ⟨mkRight A B y, (mem_liftRight A B).2 ⟨y, hy, rfl⟩, rfl, rfl⟩

theorem sndFinset_liftLeft (v : Finset α) :
    sndFinset A B (liftLeft A B v) ⊆ ({B.bot} : Finset β) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  rcases (mem_liftLeft A B).1 hp with ⟨x, _, hp'⟩
  subst hp'
  -- mkLeft x has first component x; filter requires x = A.bot, and second is B.bot
  have : y = B.bot := hy'.symm
  exact Finset.mem_singleton.mpr this

theorem fstFinset_liftRight (w : Finset β) :
    fstFinset A B (liftRight A B w) ⊆ ({A.bot} : Finset α) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, hx'⟩
  rcases (mem_liftRight A B).1 hp with ⟨y, _, hp'⟩
  subst hp'
  have : x = A.bot := hx'.symm
  exact Finset.mem_singleton.mpr this

theorem ProdCon_liftLeft {v : Finset α} (hv : v ∈ A.Con) :
    ProdCon A B (liftLeft A B v) := by
  refine ⟨?_, ?_⟩
  · rw [fstFinset_liftLeft]
    exact hv
  · exact B.con_subset (B.con_sing B.bot) (sndFinset_liftLeft A B v)

theorem ProdCon_liftRight {w : Finset β} (hw : w ∈ B.Con) :
    ProdCon A B (liftRight A B w) := by
  refine ⟨?_, ?_⟩
  · exact A.con_subset (A.con_sing A.bot) (fstFinset_liftRight A B w)
  · rw [sndFinset_liftRight]
    exact hw

theorem ProdCon_empty : ProdCon A B (∅ : Finset (ProdToken A B)) :=
  ⟨by rw [fstFinset_empty]; exact A.con_empty,
    by rw [sndFinset_empty]; exact B.con_empty⟩

/-- Product entailment of a set projects to component entailment on `fst`. -/
theorem entSet_fst_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    A.EntSet (fstFinset A B u) (fstFinset A B v) := by
  intro x hx
  rcases (mem_fstFinset A B).1 hx with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.1 hbot

/-- Product entailment of a set projects to component entailment on `snd`. -/
theorem entSet_snd_of_prodEntSet {u v : Finset (ProdToken A B)}
    (h : (productSystem A B).EntSet u v) :
    B.EntSet (sndFinset A B u) (sndFinset A B v) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, rfl⟩
  exact (h p hp).2.2 hbot

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.2(1).** Approximable first projection. -/
def fstMap : ApproximableMap (productSystem A B) A where
  rel u v := u ∈ (productSystem A B).Con ∧ v ∈ A.Con ∧ A.EntSet (fstFinset A B u) v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, A.con_empty, by
    rw [fstFinset_empty]; exact A.entSet_empty ∅⟩
  union_right := by
    rintro u v v' ⟨hu, hv, huv⟩ ⟨_, hv', huv'⟩
    have hEnt : A.EntSet (fstFinset A B u) (v ∪' v') :=
      proposition_2_3_vi (sys := A) huv huv'
    have hBig : fstFinset A B u ∪' (v ∪' v') ∈ A.Con :=
      proposition_2_3_ii (sys := A) hu.1 hEnt
    have hCon : v ∪' v' ∈ A.Con :=
      A.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, huv⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    exact proposition_2_3_iv A hu'.1 hv
      (proposition_2_3_iv A hu'.1 hu.1 (entSet_fst_of_prodEntSet A B hEntu) huv) hEntv

/-- **Proposition 6.2(2).** Approximable second projection. -/
def sndMap : ApproximableMap (productSystem A B) B where
  rel u w := u ∈ (productSystem A B).Con ∧ w ∈ B.Con ∧ B.EntSet (sndFinset A B u) w
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨ProdCon_empty A B, B.con_empty, by
    rw [sndFinset_empty]; exact B.entSet_empty ∅⟩
  union_right := by
    rintro u w w' ⟨hu, hw, huw⟩ ⟨_, hw', huw'⟩
    have hEnt : B.EntSet (sndFinset A B u) (w ∪' w') :=
      proposition_2_3_vi (sys := B) huw huw'
    have hBig : sndFinset A B u ∪' (w ∪' w') ∈ B.Con :=
      proposition_2_3_ii (sys := B) hu.2 hEnt
    have hCon : w ∪' w' ∈ B.Con :=
      B.con_subset hBig (subset_funion_right _ _)
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' w w' ⟨hu, hw, huw⟩ hEntu hEntw hu' hw'
    refine ⟨hu', hw', ?_⟩
    exact proposition_2_3_iv B hu'.2 hw
      (proposition_2_3_iv B hu'.2 hu.2 (entSet_snd_of_prodEntSet A B hEntu) huw) hEntw

/-- Helper: `g` relates `s` to any subset of `{Δ_B}` once it relates to `∅`. -/
private theorem rel_bot_subset {D : InfoSys β} {s : Finset γ} {w : Finset β}
    (g : ApproximableMap C D) (hs : s ∈ C.Con)
    (hg : g.rel s (∅ : Finset β)) (hw : w ⊆ ({D.bot} : Finset β)) :
    g.rel s w := by
  have hwCon : w ∈ D.Con := D.con_subset (D.con_sing D.bot) hw
  have hEnt : D.EntSet (∅ : Finset β) w := by
    intro y hy
    have : y = D.bot := Finset.mem_singleton.mp (hw hy)
    subst this
    exact D.ent_bot D.con_empty
  exact g.mono hg (proposition_2_3_iii C hs) hEnt hs hwCon

/-- Helper: `f` relates `s` to any subset of `{Δ_A}` once it relates to `∅`. -/
private theorem rel_bot_subset_left {D : InfoSys α} {s : Finset γ} {v : Finset α}
    (f : ApproximableMap C D) (hs : s ∈ C.Con)
    (hf : f.rel s (∅ : Finset α)) (hv : v ⊆ ({D.bot} : Finset α)) :
    f.rel s v := by
  have hvCon : v ∈ D.Con := D.con_subset (D.con_sing D.bot) hv
  have hEnt : D.EntSet (∅ : Finset α) v := by
    intro x hx
    have : x = D.bot := Finset.mem_singleton.mp (hv hx)
    subst this
    exact D.ent_bot D.con_empty
  exact f.mono hf (proposition_2_3_iii C hs) hEnt hs hvCon

/-- **Proposition 6.2(3).** Pairing of approximable maps. -/
def pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    ApproximableMap C (productSystem A B) where
  rel s u := f.rel s (fstFinset A B u) ∧ g.rel s (sndFinset A B u)
  rel_dom h := f.rel_dom h.1
  rel_cod h := ⟨f.rel_cod h.1, g.rel_cod h.2⟩
  empty_rel := by
    rw [fstFinset_empty, sndFinset_empty]
    exact ⟨f.empty_rel, g.empty_rel⟩
  union_right := by
    rintro s u u' ⟨hf, hg⟩ ⟨hf', hg'⟩
    rw [fstFinset_funion A B u u', sndFinset_funion A B u u']
    exact ⟨f.union_right hf hf', g.union_right hg hg'⟩
  mono := by
    rintro s s' u u' ⟨hf, hg⟩ hEnts hEntu hs' hu'
    refine ⟨?_, ?_⟩
    · exact f.mono hf hEnts (entSet_fst_of_prodEntSet A B hEntu) hs' hu'.1
    · exact g.mono hg hEnts (entSet_snd_of_prodEntSet A B hEntu) hs' hu'.2

/-- Product elements are determined by their projections (Scott’s uniqueness lemma). -/
theorem element_eq_of_fst_snd (z z' : (productSystem A B).Element)
    (hfst : (fstMap A B).toElement z = (fstMap A B).toElement z')
    (hsnd : (sndMap A B).toElement z = (sndMap A B).toElement z') :
    z = z' := by
  apply le_antisymm
  · intro p hp
    have hpz : (↑({p} : Finset (ProdToken A B)) : Set _) ⊆ z.carrier := by
      intro q hq
      have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
      subst this
      exact hp
    have hCon : ProdCon A B {p} := z.consistent {p} hpz
    rcases p.property with h1 | h2
    · -- right-tagged (or bottom): use `snd`
      have hy : p.val.2 ∈ ((sndMap A B).toElement z).carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, B.con_sing p.val.2, ?_⟩
        intro y hy
        have : y = p.val.2 := Finset.mem_singleton.mp hy
        subst this
        exact B.ent_refl hCon.2 ((mem_sndFinset A B).2 ⟨p, Finset.mem_singleton_self p, h1, rfl⟩)
      have hy' : p.val.2 ∈ ((sndMap A B).toElement z').carrier := by
        rw [← hsnd]
        exact hy
      rcases hy' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          simpa [h1] using A.ent_bot huCon.1
        · intro _
          exact hEnt p.val.2 (Finset.mem_singleton_self _)
      exact z'.closed u p hu hEntp
    · -- left-tagged: use `fst`
      have hx : p.val.1 ∈ ((fstMap A B).toElement z).carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, A.con_sing p.val.1, ?_⟩
        intro x hx
        have : x = p.val.1 := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_refl hCon.1 ((mem_fstFinset A B).2 ⟨p, Finset.mem_singleton_self p, h2, rfl⟩)
      have hx' : p.val.1 ∈ ((fstMap A B).toElement z').carrier := by
        rw [← hfst]
        exact hx
      rcases hx' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          exact hEnt p.val.1 (Finset.mem_singleton_self _)
        · intro _
          simpa [h2] using B.ent_bot huCon.2
      exact z'.closed u p hu hEntp
  · intro p hp
    have hpz : (↑({p} : Finset (ProdToken A B)) : Set _) ⊆ z'.carrier := by
      intro q hq
      have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
      subst this
      exact hp
    have hCon : ProdCon A B {p} := z'.consistent {p} hpz
    rcases p.property with h1 | h2
    · have hy : p.val.2 ∈ ((sndMap A B).toElement z').carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, B.con_sing p.val.2, ?_⟩
        intro y hy
        have : y = p.val.2 := Finset.mem_singleton.mp hy
        subst this
        exact B.ent_refl hCon.2 ((mem_sndFinset A B).2 ⟨p, Finset.mem_singleton_self p, h1, rfl⟩)
      have hy' : p.val.2 ∈ ((sndMap A B).toElement z).carrier := by
        rw [hsnd]
        exact hy
      rcases hy' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          simpa [h1] using A.ent_bot huCon.1
        · intro _
          exact hEnt p.val.2 (Finset.mem_singleton_self _)
      exact z.closed u p hu hEntp
    · have hx : p.val.1 ∈ ((fstMap A B).toElement z').carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, A.con_sing p.val.1, ?_⟩
        intro x hx
        have : x = p.val.1 := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_refl hCon.1 ((mem_fstFinset A B).2 ⟨p, Finset.mem_singleton_self p, h2, rfl⟩)
      have hx' : p.val.1 ∈ ((fstMap A B).toElement z).carrier := by
        rw [hfst]
        exact hx
      rcases hx' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          exact hEnt p.val.1 (Finset.mem_singleton_self _)
        · intro _
          simpa [h2] using B.ent_bot huCon.2
      exact z.closed u p hu hEntp

/-- `fst ∘ ⟨f, g⟩ = f`. -/
theorem comp_fstMap_pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (fstMap A B) (pairMap A B f g) = f := by
  refine ApproximableMap.ext fun s v => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hv, hEnt⟩⟩
    exact f.mono hf (proposition_2_3_iii C (f.rel_dom hf)) hEnt (f.rel_dom hf) hv
  · intro hf
    refine ⟨liftLeft A B v, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [fstFinset_liftLeft]
        exact hf
      · have hs : s ∈ C.Con := f.rel_dom hf
        have hg0 : g.rel s (∅ : Finset β) :=
          g.mono g.empty_rel (C.entSet_empty s) (B.entSet_empty ∅) hs B.con_empty
        exact rel_bot_subset g hs hg0 (sndFinset_liftLeft A B v)
    · refine ⟨ProdCon_liftLeft A B (f.rel_cod hf), f.rel_cod hf, ?_⟩
      rw [fstFinset_liftLeft]
      exact proposition_2_3_iii A (f.rel_cod hf)

/-- `snd ∘ ⟨f, g⟩ = g`. -/
theorem comp_sndMap_pairMap (f : ApproximableMap C A) (g : ApproximableMap C B) :
    comp (sndMap A B) (pairMap A B f g) = g := by
  refine ApproximableMap.ext fun s w => ?_
  constructor
  · rintro ⟨u, ⟨hf, hg⟩, ⟨hu, hw, hEnt⟩⟩
    exact g.mono hg (proposition_2_3_iii C (g.rel_dom hg)) hEnt (g.rel_dom hg) hw
  · intro hg
    refine ⟨liftRight A B w, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have hs : s ∈ C.Con := g.rel_dom hg
        have hf0 : f.rel s (∅ : Finset α) :=
          f.mono f.empty_rel (C.entSet_empty s) (A.entSet_empty ∅) hs A.con_empty
        exact rel_bot_subset_left f hs hf0 (fstFinset_liftRight A B w)
      · rw [sndFinset_liftRight]
        exact hg
    · refine ⟨ProdCon_liftRight A B (g.rel_cod hg), g.rel_cod hg, ?_⟩
      rw [sndFinset_liftRight]
      exact proposition_2_3_iii B (g.rel_cod hg)

/-- Uniqueness of pairing (Scott Prop 6.2). -/
theorem pairMap_unique (f : ApproximableMap C A) (g : ApproximableMap C B)
    (h : ApproximableMap C (productSystem A B))
    (hfst : comp (fstMap A B) h = f) (hsnd : comp (sndMap A B) h = g) :
    h = pairMap A B f g :=
  (ext_iff_toElement h (pairMap A B f g)).2 fun x =>
    element_eq_of_fst_snd A B (h.toElement x) ((pairMap A B f g).toElement x)
      (by
        have h1 : (fstMap A B).toElement (h.toElement x) = f.toElement x := by
          rw [← comp_toElement, hfst]
        have h2 : (fstMap A B).toElement ((pairMap A B f g).toElement x) = f.toElement x := by
          rw [← comp_toElement, comp_fstMap_pairMap]
        exact h1.trans h2.symm)
      (by
        have h1 : (sndMap A B).toElement (h.toElement x) = g.toElement x := by
          rw [← comp_toElement, hsnd]
        have h2 : (sndMap A B).toElement ((pairMap A B f g).toElement x) = g.toElement x := by
          rw [← comp_toElement, comp_sndMap_pairMap]
        exact h1.trans h2.symm)

end ApproximableMap

end InfoSys

end Scott1982
