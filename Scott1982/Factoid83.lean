/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Product

/-!
# Factoid 8.3 — universal domain via `V` (with top) and `U` (top removed)

**Scott 1982, §8.** Construct `V` with bottom `Δ` and top `∇`, close under product
flavours `(X, Δ)` / `(Δ, Y)`, take all finite sets consistent, and define entailment
by Scott’s clauses (3)–(6). Then form `U` by deleting `∇` and retaining only those
finite sets that do not entail `∇` (clauses (7)–(10)).

The retract/universality theorem (every countably based domain is a retract of `U`)
is stated by Scott without proof here; we package `vSystem` / `uSystem` and the
domain equation `V ≅ V × V` on the product-shaped tokens.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-! ## Tokens of `V` (Scott (1)–(2)) -/

/-- Data objects of `V`: bottom `Δ`, top `∇`, and product left/right copies. -/
inductive VToken where
  | bot : VToken
  | top : VToken
  | pairL : VToken → VToken
  | pairR : VToken → VToken
  deriving DecidableEq

/-- Bottom `Δ_V`. -/
def vBot : VToken := .bot

/-- Top / rogue `∇`. -/
def vTop : VToken := .top

/-! ## Projections `{X | (X,Δ) ∈ u}` and `{Y | (Δ,Y) ∈ u}` -/

private def pairLInsert : VToken → Finset VToken → Finset VToken
  | .pairL t => insert t
  | .bot | .top | .pairR _ => id

private def pairRInsert : VToken → Finset VToken → Finset VToken
  | .pairR t => insert t
  | .bot | .top | .pairL _ => id

private instance :
    LeftCommutative (pairLInsert : VToken → Finset VToken → Finset VToken) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance :
    LeftCommutative (pairRInsert : VToken → Finset VToken → Finset VToken) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

/-- Left projection: `{X | (X, Δ) ∈ u}`. -/
def vPairLFinset (u : Finset VToken) : Finset VToken :=
  Multiset.foldr pairLInsert (∅ : Finset VToken) u.1

/-- Right projection: `{Y | (Δ, Y) ∈ u}`. -/
def vPairRFinset (u : Finset VToken) : Finset VToken :=
  Multiset.foldr pairRInsert (∅ : Finset VToken) u.1

private theorem mem_foldr_pairL (s : Multiset VToken) (t : VToken) :
    t ∈ Multiset.foldr pairLInsert (∅ : Finset VToken) s ↔
      ∃ p ∈ s, p = .pairL t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    cases p with
    | pairL a =>
      simp only [Multiset.foldr_cons, pairLInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, hq'⟩)
        · exact ⟨.pairL a, Or.inl rfl, congrArg VToken.pairL ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | top | pairR _ =>
      simp only [Multiset.foldr_cons, pairLInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

private theorem mem_foldr_pairR (s : Multiset VToken) (t : VToken) :
    t ∈ Multiset.foldr pairRInsert (∅ : Finset VToken) s ↔
      ∃ p ∈ s, p = .pairR t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    cases p with
    | pairR a =>
      simp only [Multiset.foldr_cons, pairRInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, hq'⟩)
        · exact ⟨.pairR a, Or.inl rfl, congrArg VToken.pairR ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | top | pairL _ =>
      simp only [Multiset.foldr_cons, pairRInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_vPairLFinset {u : Finset VToken} {t : VToken} :
    t ∈ vPairLFinset u ↔ .pairL t ∈ u := by
  simpa [vPairLFinset] using mem_foldr_pairL u.1 t

theorem mem_vPairRFinset {u : Finset VToken} {t : VToken} :
    t ∈ vPairRFinset u ↔ .pairR t ∈ u := by
  simpa [vPairRFinset] using mem_foldr_pairR u.1 t

theorem vPairLFinset_empty : vPairLFinset (∅ : Finset VToken) = ∅ := rfl
theorem vPairRFinset_empty : vPairRFinset (∅ : Finset VToken) = ∅ := rfl

theorem vPairLFinset_mono {u v : Finset VToken} (h : u ⊆ v) :
    vPairLFinset u ⊆ vPairLFinset v := by
  intro t ht
  exact mem_vPairLFinset.2 (h (mem_vPairLFinset.1 ht))

theorem vPairRFinset_mono {u v : Finset VToken} (h : u ⊆ v) :
    vPairRFinset u ⊆ vPairRFinset v := by
  intro t ht
  exact mem_vPairRFinset.2 (h (mem_vPairRFinset.1 ht))

theorem vPairLFinset_insert_pairL (u : Finset VToken) (t : VToken) :
    vPairLFinset (insert (.pairL t) u) = insert t (vPairLFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_vPairLFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (VToken.pairL.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem vPairRFinset_insert_pairR (u : Finset VToken) (t : VToken) :
    vPairRFinset (insert (.pairR t) u) = insert t (vPairRFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_vPairRFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (VToken.pairR.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem vPairLFinset_insert_bot (u : Finset VToken) :
    vPairLFinset (insert (.bot : VToken) u) = vPairLFinset u := by
  ext t; simp only [mem_vPairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem vPairRFinset_insert_bot (u : Finset VToken) :
    vPairRFinset (insert (.bot : VToken) u) = vPairRFinset u := by
  ext t; simp only [mem_vPairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem vPairLFinset_insert_top (u : Finset VToken) :
    vPairLFinset (insert (.top : VToken) u) = vPairLFinset u := by
  ext t; simp only [mem_vPairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem vPairRFinset_insert_top (u : Finset VToken) :
    vPairRFinset (insert (.top : VToken) u) = vPairRFinset u := by
  ext t; simp only [mem_vPairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem vPairLFinset_insert_pairR (u : Finset VToken) (t : VToken) :
    vPairLFinset (insert (.pairR t) u) = vPairLFinset u := by
  ext s; simp only [mem_vPairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem vPairRFinset_insert_pairL (u : Finset VToken) (t : VToken) :
    vPairRFinset (insert (.pairL t) u) = vPairRFinset u := by
  ext s; simp only [mem_vPairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

/-! ## Entailment for `V` (Scott (3)–(6)); all finite sets consistent -/

/-- Entailment on `V` (Scott (3)–(6)). -/
inductive VEnt : Finset VToken → VToken → Prop where
  | bot {u : Finset VToken} : VEnt u .bot
  | top_mem {u : Finset VToken} (h : .top ∈ u) : VEnt u .top
  | top_both {u : Finset VToken}
      (hL : VEnt (vPairLFinset u) .top) (hR : VEnt (vPairRFinset u) .top) :
      VEnt u .top
  | pairL_top {u : Finset VToken} {x : VToken} (h : .top ∈ u) : VEnt u (.pairL x)
  | pairL_proj {u : Finset VToken} {x : VToken}
      (h : VEnt (vPairLFinset u) x) : VEnt u (.pairL x)
  | pairR_top {u : Finset VToken} {y : VToken} (h : .top ∈ u) : VEnt u (.pairR y)
  | pairR_proj {u : Finset VToken} {y : VToken}
      (h : VEnt (vPairRFinset u) y) : VEnt u (.pairR y)

/-- Scott: all finite subsets of `D_V` are consistent. -/
def VCon (_u : Finset VToken) : Prop := True

theorem VCon_any (u : Finset VToken) : VCon u := trivial

/-- If `u ⊢ ∇`, then `u` entails every token (rogue top). -/
theorem VEnt_of_ent_top {u : Finset VToken} (h : VEnt u .top) (c : VToken) :
    VEnt u c := by
  match c with
  | .bot => exact VEnt.bot
  | .top => exact h
  | .pairL x =>
    cases h with
    | top_mem hm => exact VEnt.pairL_top hm
    | top_both hL _ => exact VEnt.pairL_proj (VEnt_of_ent_top hL x)
  | .pairR y =>
    cases h with
    | top_mem hm => exact VEnt.pairR_top hm
    | top_both _ hR => exact VEnt.pairR_proj (VEnt_of_ent_top hR y)

theorem VEnt_mono {u v : Finset VToken} {c : VToken}
    (huv : u ⊆ v) (h : VEnt u c) : VEnt v c := by
  induction h generalizing v with
  | bot => exact VEnt.bot
  | top_mem hm => exact VEnt.top_mem (huv hm)
  | top_both _ _ ihL ihR =>
    exact VEnt.top_both (ihL (vPairLFinset_mono huv)) (ihR (vPairRFinset_mono huv))
  | pairL_top hm => exact VEnt.pairL_top (huv hm)
  | pairL_proj _ ih => exact VEnt.pairL_proj (ih (vPairLFinset_mono huv))
  | pairR_top hm => exact VEnt.pairR_top (huv hm)
  | pairR_proj _ ih => exact VEnt.pairR_proj (ih (vPairRFinset_mono huv))

theorem VEnt_of_mem {u : Finset VToken} {c : VToken}
    (hc : c ∈ u) : VEnt u c := by
  induction c generalizing u with
  | bot => exact VEnt.bot
  | top => exact VEnt.top_mem hc
  | pairL x ih =>
    exact VEnt.pairL_proj (ih (mem_vPairLFinset.2 hc))
  | pairR y ih =>
    exact VEnt.pairR_proj (ih (mem_vPairRFinset.2 hc))

/-- Empty set does not entail top (no derivation bottoms out). -/
theorem not_VEnt_empty_top : ¬ VEnt (∅ : Finset VToken) .top := by
  have aux : ∀ {u : Finset VToken} {c : VToken},
      VEnt u c → c = .top → u = ∅ → False := by
    intro u c h
    induction h with
    | bot => intro hc; exact nomatch hc
    | top_mem hm =>
      intro _ hu; exact Finset.notMem_empty _ (hu ▸ hm)
    | top_both _ _ ihL _ =>
      intro _ hu
      exact ihL rfl (by rw [hu]; exact vPairLFinset_empty)
    | pairL_top => intro hc; exact nomatch hc
    | pairL_proj => intro hc; exact nomatch hc
    | pairR_top => intro hc; exact nomatch hc
    | pairR_proj => intro hc; exact nomatch hc
  exact fun h => aux h rfl rfl

/-- From `v ⊢ (X, Δ)`, either `∇ ∈ v` or the left projection entails `X`. -/
theorem VEnt_pairL_inv {v : Finset VToken} {x : VToken}
    (h : VEnt v (.pairL x)) : .top ∈ v ∨ VEnt (vPairLFinset v) x := by
  cases h with
  | pairL_top hm => exact Or.inl hm
  | pairL_proj h' => exact Or.inr h'

theorem VEnt_pairR_inv {v : Finset VToken} {y : VToken}
    (h : VEnt v (.pairR y)) : .top ∈ v ∨ VEnt (vPairRFinset v) y := by
  cases h with
  | pairR_top hm => exact Or.inl hm
  | pairR_proj h' => exact Or.inr h'

/-- Push an `EntSet` through the left projection (or absorb via top). -/
theorem VEnt_pairLFinset_of_EntSet {u v : Finset VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) :
    .top ∈ v ∨ (∀ y ∈ vPairLFinset u, VEnt (vPairLFinset v) y) := by
  by_cases htop : .top ∈ v
  · exact Or.inl htop
  · refine Or.inr ?_
    intro y hy
    have hy' := hEnts _ (mem_vPairLFinset.1 hy)
    rcases VEnt_pairL_inv hy' with hm | hproj
    · exact False.elim (htop hm)
    · exact hproj

theorem VEnt_pairRFinset_of_EntSet {u v : Finset VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) :
    .top ∈ v ∨ (∀ y ∈ vPairRFinset u, VEnt (vPairRFinset v) y) := by
  by_cases htop : .top ∈ v
  · exact Or.inl htop
  · refine Or.inr ?_
    intro y hy
    have hy' := hEnts _ (mem_vPairRFinset.1 hy)
    rcases VEnt_pairR_inv hy' with hm | hproj
    · exact False.elim (htop hm)
    · exact hproj

theorem VEnt_trans {u v : Finset VToken} {c : VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) (h : VEnt u c) : VEnt v c := by
  induction h generalizing v with
  | bot => exact VEnt.bot
  | top_mem hm => exact hEnts _ hm
  | top_both _ _ ihL ihR =>
    rcases VEnt_pairLFinset_of_EntSet hEnts with hm | hL
    · exact VEnt_of_ent_top (VEnt.top_mem hm) .top
    · rcases VEnt_pairRFinset_of_EntSet hEnts with hm | hR
      · exact VEnt_of_ent_top (VEnt.top_mem hm) .top
      · exact VEnt.top_both (ihL hL) (ihR hR)
  | pairL_top hm => exact VEnt_of_ent_top (hEnts _ hm) _
  | pairL_proj _ ih =>
    rcases VEnt_pairLFinset_of_EntSet hEnts with hm | hL
    · exact VEnt.pairL_top hm
    · exact VEnt.pairL_proj (ih hL)
  | pairR_top hm => exact VEnt_of_ent_top (hEnts _ hm) _
  | pairR_proj _ ih =>
    rcases VEnt_pairRFinset_of_EntSet hEnts with hm | hR
    · exact VEnt.pairR_top hm
    · exact VEnt.pairR_proj (ih hR)

/-- **Scott (1)–(6).** The information system `V` (all finite sets consistent). -/
def vSystem : InfoSys VToken where
  bot := vBot
  Con := {u | VCon u}
  Ent := VEnt
  con_subset := fun _ _ => trivial
  con_sing := fun _ => trivial
  ent_con := fun _ => trivial
  ent_bot := fun _ => VEnt.bot
  ent_refl := fun _ hp => VEnt_of_mem hp
  ent_trans := fun _ _ hEnts h => VEnt_trans hEnts h

/-! ## Domain equation `V ≅ V × V` (product-shaped tokens) -/

/-- Unfold product-shaped tokens into `V × V`. Top `∇` has no single product-token
image (it generates the top *element*); we send it to `(∇, Δ)` as a left witness. -/
def vUnfold (t : VToken) : ProdToken vSystem vSystem :=
  match t with
  | .bot => prodBot vSystem vSystem
  | .top => ⟨(.top, .bot), Or.inr rfl⟩
  | .pairL x => ⟨(x, .bot), Or.inr rfl⟩
  | .pairR y => ⟨(.bot, y), Or.inl rfl⟩

theorem vUnfold_bot : vUnfold .bot = prodBot vSystem vSystem := rfl

theorem vUnfold_pairL (x : VToken) :
    vUnfold (.pairL x) = ⟨(x, .bot), Or.inr rfl⟩ := rfl

theorem vUnfold_pairR (y : VToken) :
    vUnfold (.pairR y) = ⟨(.bot, y), Or.inl rfl⟩ := rfl

/-- Right-hand side of Scott’s equation `V ≅ V × V`. -/
def vRhs : InfoSys (ProdToken vSystem vSystem) :=
  productSystem vSystem vSystem

theorem vRhs_eq_product : vRhs = productSystem vSystem vSystem := rfl

/-! ## The universal domain `U` (Scott (7)–(10)) -/

/-- Tokens of `U`: `D_V` without `∇` (Scott (7)). -/
def IsUToken (t : VToken) : Prop := t ≠ .top

instance : DecidablePred IsUToken := fun t =>
  if h : t = .top then isFalse fun ht => ht h
  else isTrue h

def UToken : Type := { t : VToken // IsUToken t }

instance : DecidableEq UToken := Subtype.instDecidableEq

/-- Bottom `Δ_U = Δ_V` (Scott (8)). -/
def uBot : UToken := ⟨.bot, by decide⟩

def uForget (t : UToken) : VToken := t.val

private def uForgetInsert : UToken → Finset VToken → Finset VToken :=
  fun t => insert (uForget t)

private instance : LeftCommutative uForgetInsert :=
  ⟨fun p q s => insert_comm' (uForget p) (uForget q) s⟩

def uForgetFinset (u : Finset UToken) : Finset VToken :=
  Multiset.foldr uForgetInsert ∅ u.1

private theorem mem_foldr_uForget (s : Multiset UToken) (t : VToken) :
    t ∈ Multiset.foldr uForgetInsert ∅ s ↔ ∃ p ∈ s, p.val = t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    simp only [Multiset.foldr_cons, uForgetInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (rfl | ⟨q, hq, hq'⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem mem_uForgetFinset {u : Finset UToken} {t : VToken} :
    t ∈ uForgetFinset u ↔ ∃ p ∈ u, p.val = t := by
  simpa [uForgetFinset] using mem_foldr_uForget u.1 t

theorem uForgetFinset_empty : uForgetFinset (∅ : Finset UToken) = ∅ := rfl

theorem uForgetFinset_singleton (p : UToken) :
    uForgetFinset {p} = {p.val} := by
  ext t
  constructor
  · intro ht
    rcases (mem_uForgetFinset).1 ht with ⟨q, hq, hq'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this; exact Finset.mem_singleton.mpr hq'.symm
  · intro ht
    exact (mem_uForgetFinset).2
      ⟨p, Finset.mem_singleton_self p, (Finset.mem_singleton.mp ht).symm⟩

theorem uForgetFinset_insert (u : Finset UToken) (p : UToken) :
    uForgetFinset (insert p u) = insert p.val (uForgetFinset u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_uForgetFinset).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_uForgetFinset).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_uForgetFinset).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_uForgetFinset).1 ht with ⟨q, hq, rfl⟩
      exact (mem_uForgetFinset).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

theorem uForgetFinset_mono {u v : Finset UToken} (h : v ⊆ u) :
    uForgetFinset v ⊆ uForgetFinset u := by
  intro t ht
  rcases (mem_uForgetFinset).1 ht with ⟨p, hp, rfl⟩
  exact (mem_uForgetFinset).2 ⟨p, h hp, rfl⟩

theorem not_mem_uForget_top (u : Finset UToken) : .top ∉ uForgetFinset u := by
  intro ht
  rcases (mem_uForgetFinset).1 ht with ⟨p, _, hp⟩
  exact p.property hp

/-- Consistency for `U`: finite `u ⊆ D_U` with `u ⊬_V ∇` (Scott (9)). -/
def UCon (u : Finset UToken) : Prop :=
  ¬ VEnt (uForgetFinset u) .top

/-- Entailment for `U` (Scott (10)). -/
def UEnt (u : Finset UToken) (p : UToken) : Prop :=
  UCon u ∧ VEnt (uForgetFinset u) p.val

theorem UCon_empty : UCon (∅ : Finset UToken) := by
  simpa [UCon, uForgetFinset_empty] using not_VEnt_empty_top

/-- Singleton of a non-top token does not entail top. -/
theorem not_VEnt_singleton_ne_top {t : VToken} (ht : t ≠ .top) :
    ¬ VEnt ({t} : Finset VToken) .top := by
  intro h
  match t, h with
  | .bot, .top_mem hm =>
    exact False.elim (nomatch Finset.mem_singleton.mp hm)
  | .bot, .top_both hL _ =>
    have hL' : vPairLFinset ({.bot} : Finset VToken) = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch mem_vPairLFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    exact not_VEnt_empty_top (by rwa [hL'] at hL)
  | .top, _ => exact ht rfl
  | .pairL x, .top_mem hm =>
    exact False.elim (nomatch Finset.mem_singleton.mp hm)
  | .pairL x, .top_both _ hR =>
    have hR' : vPairRFinset ({.pairL x} : Finset VToken) = ∅ := by
      ext y; constructor
      · intro hy; exact False.elim (nomatch mem_vPairRFinset.1 hy)
      · intro hy; exact False.elim (Finset.notMem_empty y hy)
    exact not_VEnt_empty_top (by rwa [hR'] at hR)
  | .pairR y, .top_mem hm =>
    exact False.elim (nomatch Finset.mem_singleton.mp hm)
  | .pairR y, .top_both hL _ =>
    have hL' : vPairLFinset ({.pairR y} : Finset VToken) = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch mem_vPairLFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    exact not_VEnt_empty_top (by rwa [hL'] at hL)

theorem UCon_singleton (p : UToken) : UCon {p} := by
  rw [UCon, uForgetFinset_singleton]
  exact not_VEnt_singleton_ne_top p.property

theorem UCon_subset {u v : Finset UToken}
    (hu : UCon u) (hv : v ⊆ u) : UCon v :=
  fun h => hu (VEnt_mono (uForgetFinset_mono hv) h)

/-- If inserting a non-top `y` creates a top-entailment and `u ⊢ y`, then already `u ⊢ ∇`. -/
theorem VEnt_insert_top_imp {u : Finset VToken} {y : VToken}
    (hy : y ≠ .top) (hEnt : VEnt u y) (hIns : VEnt (insert y u) .top) :
    VEnt u .top := by
  induction y generalizing u with
  | bot =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_bot] at hL
      rw [vPairRFinset_insert_bot] at hR
      exact VEnt.top_both hL hR
  | top => exact False.elim (hy rfl)
  | pairL x ih =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_pairL] at hL
      rw [vPairRFinset_insert_pairL] at hR
      rcases VEnt_pairL_inv hEnt with htop | hx
      · exact VEnt.top_mem htop
      · by_cases hxTop : x = .top
        · subst hxTop; exact VEnt.top_both hx hR
        · exact VEnt.top_both (ih hxTop hx hL) hR
  | pairR z ih =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_pairR] at hL
      rw [vPairRFinset_insert_pairR] at hR
      rcases VEnt_pairR_inv hEnt with htop | hz
      · exact VEnt.top_mem htop
      · by_cases hzTop : z = .top
        · subst hzTop; exact VEnt.top_both hL hz
        · exact VEnt.top_both hL (ih hzTop hz hR)

/-- Adding an entailed non-top token cannot create a top-entailment. -/
theorem not_VEnt_insert_top_of_ent {u : Finset VToken} {y : VToken}
    (hy : y ≠ .top) (hEnt : VEnt u y) (hNot : ¬ VEnt u .top) :
    ¬ VEnt (insert y u) .top :=
  fun hIns => hNot (VEnt_insert_top_imp hy hEnt hIns)

theorem UCon_insert_of_ent {u : Finset UToken} {p : UToken}
    (h : UEnt u p) : UCon (insert p u) := by
  rcases h with ⟨hCon, hEnt⟩
  rw [UCon, uForgetFinset_insert]
  exact not_VEnt_insert_top_of_ent p.property hEnt hCon

theorem UEnt_bot {u : Finset UToken} (hu : UCon u) : UEnt u uBot :=
  ⟨hu, VEnt.bot⟩

theorem UEnt_of_mem {u : Finset UToken} {p : UToken}
    (hu : UCon u) (hp : p ∈ u) : UEnt u p :=
  ⟨hu, VEnt_of_mem ((mem_uForgetFinset).2 ⟨p, hp, rfl⟩)⟩

theorem UEnt_trans {u v : Finset UToken} {c : UToken}
    (hv : UCon v) (_hu : UCon u)
    (hEnts : ∀ y ∈ u, UEnt v y) (h : UEnt u c) : UEnt v c :=
  ⟨hv, VEnt_trans
    (fun y hy => by
      rcases (mem_uForgetFinset).1 hy with ⟨p, hp, rfl⟩
      exact (hEnts p hp).2)
    h.2⟩

/-- **Scott (7)–(10).** The universal-domain information system `U`. -/
def uSystem : InfoSys UToken where
  bot := uBot
  Con := {u | UCon u}
  Ent := UEnt
  con_subset := fun hu hv => UCon_subset hu hv
  con_sing := UCon_singleton
  ent_con := fun h => UCon_insert_of_ent h
  ent_bot := fun hu => UEnt_bot hu
  ent_refl := fun hu hp => UEnt_of_mem hu hp
  ent_trans := fun hv hu hEnts h => UEnt_trans hv hu hEnts h

end InfoSys

end Scott1982
