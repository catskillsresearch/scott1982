/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Mathlib.Data.Multiset.MapFold
import Scott1982.FunctionSpace
import Scott1982.Theorem72
import Scott1982.Factoid25
import Scott1982.Factoid33
import Scott1982.Factoid35

/-!
# Factoid 7.5 — strict mappings, `strictify`, BOOL, and the conditional

**Scott 1982 (after Prop 7.4).** Strict approximable maps; Scott’s `strict` /
`strictify` operator; InfoSys `A →ₛ B`; flat BOOL; `A × A ≅ (BOOL →ₛ A)`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- `∅ ⊢ u`. -/
def EmptyEntails (A : InfoSys α) (u : Finset α) : Prop :=
  A.EntSet (∅ : Finset α) u

theorem emptyEntails_empty (A : InfoSys α) : EmptyEntails A (∅ : Finset α) :=
  A.entSet_empty ∅

theorem emptyEntails_mem_botElement (A : InfoSys α) {X : α}
    (h : A.Ent (∅ : Finset α) X) : X ∈ A.botElement.carrier :=
  A.ent_trans (A.con_sing A.bot) A.con_empty (A.entSet_empty _) h

theorem mem_botElement_emptyEntails (A : InfoSys α) {X : α}
    (h : X ∈ A.botElement.carrier) : A.Ent (∅ : Finset α) X :=
  A.ent_trans A.con_empty (A.con_sing A.bot)
    (fun x hx => by
      have : x = A.bot := Finset.mem_singleton.mp hx
      subst this
      exact A.ent_bot A.con_empty)
    h

theorem emptyEntails_funion {γ : Type*} [DecidableEq γ] (sys : InfoSys γ)
    {u v : Finset γ} :
    EmptyEntails sys (u ∪' v) ↔ EmptyEntails sys u ∧ EmptyEntails sys v := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (subset_funion_left _ _ hx),
      fun x hx => h x (subset_funion_right _ _ hx)⟩
  · intro ⟨hu, hv⟩ x hx
    rcases mem_funion.mp hx with hx | hx
    · exact hu x hx
    · exact hv x hx

/-- `f` is strict when `f(⊥) = ⊥`. -/
def IsStrict (A : InfoSys α) (B : InfoSys β) (f : ApproximableMap A B) : Prop :=
  f.toElement A.botElement = B.botElement

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

/-- **Factoid 7.5.** Largest strict approximable map contained in `f` (Scott’s `strict`). -/
def strictify (f : ApproximableMap A B) : ApproximableMap A B where
  rel u v :=
    u ∈ A.Con ∧ v ∈ B.Con ∧
      (EmptyEntails B v ∨ (f.rel u v ∧ ¬ EmptyEntails A u))
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, B.con_empty, Or.inl (emptyEntails_empty B)⟩
  union_right := by
    rintro u v v' ⟨hu, hv, hvcase⟩ ⟨_, hv', hv'case⟩
    have hvU : v ∪' v' ∈ B.Con := by
      rcases hvcase with hE | ⟨hf, _⟩
      · rcases hv'case with hE' | ⟨hf', _⟩
        · exact B.con_subset
            (proposition_2_3_ii B B.con_empty (proposition_2_3_vi B hE hE'))
            (subset_funion_right _ _)
        · exact f.rel_cod (f.union_right
            (f.mono f.empty_rel (A.entSet_empty u) hE hu hv) hf')
      · rcases hv'case with hE' | ⟨hf', _⟩
        · exact f.rel_cod (f.union_right hf
            (f.mono f.empty_rel (A.entSet_empty u) hE' hu hv'))
        · exact f.rel_cod (f.union_right hf hf')
    refine ⟨hu, hvU, ?_⟩
    rcases hvcase with hE | ⟨hf, hn⟩
    · rcases hv'case with hE' | ⟨hf', hn'⟩
      · exact Or.inl (proposition_2_3_vi B hE hE')
      · exact Or.inr ⟨f.union_right
          (f.mono f.empty_rel (A.entSet_empty u) hE hu hv) hf', hn'⟩
    · rcases hv'case with hE' | ⟨hf', hn'⟩
      · exact Or.inr ⟨f.union_right hf
          (f.mono f.empty_rel (A.entSet_empty u) hE' hu hv'), hn⟩
      · exact Or.inr ⟨f.union_right hf hf', hn⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, hcase⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    rcases hcase with hE | ⟨hf, hn⟩
    · exact Or.inl (fun y hy => B.ent_trans B.con_empty hv hE (hEntv y hy))
    · refine Or.inr ⟨f.mono hf hEntu hEntv hu' hv', fun hE' => hn ?_⟩
      exact fun x hx => A.ent_trans A.con_empty hu' hE' (hEntu x hx)

theorem IsStrict_strictify (f : ApproximableMap A B) :
    IsStrict A B (strictify A B f) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨_, _, hcase⟩⟩
    have huE : EmptyEntails A u := fun x hx =>
      mem_botElement_emptyEntails A (hu (Finset.mem_coe.2 hx))
    rcases hcase with hE | ⟨_, hn⟩
    · exact emptyEntails_mem_botElement B (hE Z (Finset.mem_singleton_self _))
    · exact False.elim (hn huE)
  · exact botElement_le B _

theorem strictify_toElement_le (f : ApproximableMap A B) (x : A.Element) :
    (strictify A B f).toElement x ≤ f.toElement x := by
  intro Z ⟨u, hu, ⟨_, _, hcase⟩⟩
  rcases hcase with hE | ⟨hf, _⟩
  · exact (botElement_le B (f.toElement x))
      (emptyEntails_mem_botElement B (hE Z (Finset.mem_singleton_self _)))
  · exact ⟨u, hu, hf⟩

end ApproximableMap

/-! ## BOOL -/

inductive BoolToken
  | bot
  | tru
  | fls
  deriving DecidableEq

/-- Points of the flat BOOL domain: undefined, true, or false. -/
inductive BoolPoint
  | undef
  | isTrue
  | isFalse

def boolSat : BoolPoint → BoolToken → Prop
  | .undef, .bot => True
  | .undef, _ => False
  | .isTrue, .bot => True
  | .isTrue, .tru => True
  | .isTrue, .fls => False
  | .isFalse, .bot => True
  | .isFalse, .fls => True
  | .isFalse, .tru => False

theorem boolSat_bot (p : BoolPoint) : boolSat p .bot := by
  cases p <;> trivial

theorem boolSat_sing (t : BoolToken) : ∃ p, boolSat p t := by
  cases t with
  | bot => exact ⟨.undef, trivial⟩
  | tru => exact ⟨.isTrue, trivial⟩
  | fls => exact ⟨.isFalse, trivial⟩

/-- **Factoid 7.5.** Flat BOOL information system. -/
def boolSystem : InfoSys BoolToken :=
  Factoid25.ofSatisfaction boolSat .bot boolSat_bot boolSat_sing

/-! ## Strict function space `A →ₛ B` -/

/-- Token of `A →ₛ B`: a function-space token that itself respects empty input. -/
def IsStrictToken (p : FunToken A B) : Prop :=
  EmptyEntails A p.val.1 → EmptyEntails B p.val.2

def StrictFunToken : Type _ :=
  {p : FunToken A B // IsStrictToken A B p}

instance : DecidableEq (StrictFunToken A B) :=
  fun p q =>
    match (inferInstance : DecidableEq (FunToken A B)) p.val q.val with
    | isTrue h => isTrue (Subtype.ext h)
    | isFalse n => isFalse fun h => n (congrArg Subtype.val h)

/-- Forget strict tokens to ordinary function-space tokens. -/
def toFunFinset (w : Finset (StrictFunToken A B)) : Finset (FunToken A B) :=
  ⟨Multiset.map (Subtype.val : StrictFunToken A B → FunToken A B) w.1,
    (Multiset.nodup_map_iff_of_injective Subtype.val_injective).2 w.nodup⟩

theorem mem_toFunFinset {w : Finset (StrictFunToken A B)} {p : FunToken A B} :
    p ∈ toFunFinset A B w ↔ ∃ q ∈ w, q.val = p := by
  change (p ∈ Multiset.map (Subtype.val : StrictFunToken A B → FunToken A B) w.1) ↔ _
  constructor
  · intro hp
    rcases Multiset.mem_map.mp hp with ⟨q, hq, heq⟩
    refine ⟨q, hq, heq⟩
  · intro ⟨q, hq, heq⟩
    exact Multiset.mem_map.mpr ⟨q, hq, heq⟩

theorem toFunFinset_subset {s w : Finset (StrictFunToken A B)} (h : s ⊆ w) :
    toFunFinset A B s ⊆ toFunFinset A B w := by
  intro p hp
  rcases (mem_toFunFinset A B).1 hp with ⟨q, hq, rfl⟩
  exact (mem_toFunFinset A B).2 ⟨q, h hq, rfl⟩

theorem toFunFinset_insert (w : Finset (StrictFunToken A B)) (p : StrictFunToken A B) :
    toFunFinset A B (insert p w) = insert p.val (toFunFinset A B w) := by
  ext q
  constructor
  · intro hq
    rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_toFunFinset A B).2 ⟨r, hr, rfl⟩)
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact (mem_toFunFinset A B).2 ⟨p, Finset.mem_insert_self _ _, rfl⟩
    · rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
      exact (mem_toFunFinset A B).2 ⟨r, Finset.mem_insert_of_mem hr, rfl⟩

theorem toFunFinset_singleton (p : StrictFunToken A B) :
    toFunFinset A B ({p} : Finset (StrictFunToken A B)) = {p.val} := by
  ext q
  constructor
  · intro hq
    rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
    exact Finset.mem_singleton.mpr (congrArg Subtype.val (Finset.mem_singleton.mp hr))
  · intro hq
    have : q = p.val := Finset.mem_singleton.mp hq
    subst this
    exact (mem_toFunFinset A B).2 ⟨p, Finset.mem_singleton_self p, rfl⟩

theorem toFunFinset_empty :
    toFunFinset A B (∅ : Finset (StrictFunToken A B)) = (∅ : Finset (FunToken A B)) := by
  ext p
  constructor
  · intro hp
    rcases (mem_toFunFinset A B).1 hp with ⟨_, hq, _⟩
    exact False.elim (Finset.notMem_empty _ hq)
  · intro hp
    exact False.elim (Finset.notMem_empty _ hp)

/-- Consistency for `A →ₛ B` (Scott 7.5: FunCon plus empty-input clause). -/
def StrictFunCon (w : Finset (StrictFunToken A B)) : Prop :=
  FunCon A B (toFunFinset A B w) ∧
    (∀ s ⊆ w,
      EmptyEntails A (funInputUnion A B (toFunFinset A B s)) →
        EmptyEntails B (funOutputUnion A B (toFunFinset A B s)))

/-- Entailment for `A →ₛ B`. -/
def StrictFunEnt (w : Finset (StrictFunToken A B)) (p : StrictFunToken A B) : Prop :=
  StrictFunCon A B w ∧ FunEnt A B (toFunFinset A B w) p.val

def strictBot : StrictFunToken A B :=
  ⟨funBot A B, fun _ => emptyEntails_empty B⟩

private theorem insert_filter_ne_strict {p : StrictFunToken A B}
    {t : Finset (StrictFunToken A B)} (hp : p ∈ t) :
    insert p (t.filter (· ≠ p)) = t := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (Finset.mem_filter.mp hq).1
  · intro hq
    if h : q = p then
      exact Finset.mem_insert.mpr (Or.inl h)
    else
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hq, h⟩))

private theorem filter_ne_subset_of_subset_insert_strict {p : StrictFunToken A B}
    {t w : Finset (StrictFunToken A B)} (ht : t ⊆ insert p w) :
    t.filter (· ≠ p) ⊆ w := by
  intro q hq
  have ⟨hqt, hne⟩ := Finset.mem_filter.mp hq
  have : q ∈ insert p w := ht hqt
  rcases Finset.mem_insert.mp this with rfl | hqW
  · exact False.elim (hne rfl)
  · exact hqW

/-- **Factoid 7.5.** The strict function-space information system `A →ₛ B`. -/
def strictFunctionSystem : InfoSys (StrictFunToken A B) where
  bot := strictBot A B
  Con := {w | StrictFunCon A B w}
  Ent := StrictFunEnt A B
  con_subset := by
    intro w w' ⟨hwFun, hwE⟩ hw'
    refine ⟨fun s hs hin =>
      hwFun s (fun q hq => (toFunFinset_subset A B hw') (hs hq)) hin, ?_⟩
    intro s hs hE
    exact hwE s (fun q hq => hw' (hs hq)) hE
  con_sing := by
    intro p
    refine ⟨?_, ?_⟩
    · intro s hs _hin
      have hs' : s ⊆ {p.val} := by
        intro q hq
        have : q ∈ toFunFinset A B ({p} : Finset (StrictFunToken A B)) := hs hq
        rwa [toFunFinset_singleton] at this
      have hsub : funOutputUnion A B s ⊆ p.val.val.2 := by
        intro y hy
        rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
        have : q = p.val := Finset.mem_singleton.mp (hs' hq)
        cases this
        exact hy'
      exact B.con_subset p.val.property.2 hsub
    · intro s hs hE y hy
      rcases (mem_funOutputUnion A B).1 hy with ⟨q, hq, hy'⟩
      rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
      have hr' : r = p := Finset.mem_singleton.mp (hs hr)
      cases hr'
      have hEp : EmptyEntails A p.val.val.1 := by
        intro x hx
        exact hE x ((mem_funInputUnion A B).2
          ⟨p.val, (mem_toFunFinset A B).2 ⟨p, hr, rfl⟩, hx⟩)
      exact p.property hEp y hy'
  ent_con := by
    intro w p ⟨⟨hwFun, hwE⟩, hFunEnt⟩
    have hFunInsert : FunCon A B (insert p.val (toFunFinset A B w)) :=
      (functionSystem A B).ent_con hFunEnt
    have hFunInsert' : FunCon A B (toFunFinset A B (insert p w)) :=
      (toFunFinset_insert A B w p).symm ▸ hFunInsert
    refine ⟨hFunInsert', ?_⟩
    intro t ht hE
    if hp : p ∈ t then
      let t' := t.filter (· ≠ p)
      have ht_eq : insert p t' = t := insert_filter_ne_strict A B hp
      have ht'sub : t' ⊆ w := filter_ne_subset_of_subset_insert_strict A B ht
      have hE' : EmptyEntails A (p.val.val.1 ∪' funInputUnion A B (toFunFinset A B t')) := by
        rwa [← ht_eq, toFunFinset_insert, funInputUnion_insert] at hE
      have ⟨hEp, hEt'⟩ := (emptyEntails_funion A).1 hE'
      have hOutp : EmptyEntails B p.val.val.2 := p.property hEp
      have hOutt' : EmptyEntails B (funOutputUnion A B (toFunFinset A B t')) :=
        hwE t' ht'sub hEt'
      have : EmptyEntails B (p.val.val.2 ∪' funOutputUnion A B (toFunFinset A B t')) :=
        (emptyEntails_funion B).2 ⟨hOutp, hOutt'⟩
      rwa [← ht_eq, toFunFinset_insert, funOutputUnion_insert]
    else
      have ht' : t ⊆ w := by
        intro q hq
        have : q ∈ insert p w := ht hq
        rcases Finset.mem_insert.mp this with rfl | hqW
        · exact False.elim (hp hq)
        · exact hqW
      exact hwE t ht' hE
  ent_bot := by
    intro w hw
    refine ⟨hw, (functionSystem A B).ent_bot hw.1⟩
  ent_refl := by
    intro w p hw hp
    have hpFun : p.val ∈ toFunFinset A B w :=
      (mem_toFunFinset A B).2 ⟨p, hp, rfl⟩
    exact ⟨hw, (functionSystem A B).ent_refl hw.1 hpFun⟩
  ent_trans := by
    intro u v c hv hu hEnts ⟨_, hFunEnt⟩
    have hFunEnts : ∀ y ∈ toFunFinset A B u,
        FunEnt A B (toFunFinset A B v) y := by
      intro y hy
      rcases (mem_toFunFinset A B).1 hy with ⟨q, hq, rfl⟩
      exact (hEnts q hq).2
    have hFun : FunEnt A B (toFunFinset A B v) c.val :=
      (functionSystem A B).ent_trans hv.1 hu.1 hFunEnts hFunEnt
    exact ⟨hv, hFun⟩

/-! ## Strict maps as elements; retract via `strictify` -/

theorem IsStrictToken_of_IsStrict (f : ApproximableMap A B) (hf : IsStrict A B f)
    {p : FunToken A B} (hrel : f.rel p.val.1 p.val.2) : IsStrictToken A B p := by
  intro hE
  have hsub : ↑p.val.1 ⊆ A.botElement.carrier := fun x hx =>
    emptyEntails_mem_botElement A (hE x (Finset.mem_coe.1 hx))
  have hout : ↑p.val.2 ⊆ (f.toElement A.botElement).carrier := by
    intro y hy
    refine ⟨p.val.1, hsub, ?_⟩
    have hy' : y ∈ p.val.2 := Finset.mem_coe.1 hy
    exact f.mono hrel (proposition_2_3_iii A p.property.1)
      (fun z hz => by
        have : z = y := Finset.mem_singleton.mp hz
        subst this
        exact B.ent_refl p.property.2 hy')
      p.property.1 (B.con_sing y)
  rw [hf] at hout
  exact fun y hy => mem_botElement_emptyEntails B (hout (Finset.mem_coe.2 hy))

open ApproximableMap

/-- Package a strict approximable map as an element of `|A →ₛ B|`. -/
def approxMap_toStrictElement (f : ApproximableMap A B) (hf : IsStrict A B f) :
    (strictFunctionSystem A B).Element where
  carrier := {p : StrictFunToken A B | f.rel p.val.val.1 p.val.val.2}
  consistent := by
    intro Y hY
    refine ⟨?_, ?_⟩
    · exact funCon_of_approxMap A B f (toFunFinset A B Y) fun q hq => by
        rcases (mem_toFunFinset A B).1 hq with ⟨p, hp, rfl⟩
        exact hY (Finset.mem_coe.2 hp)
    · intro s hs hE
      have hrel : ∀ q ∈ toFunFinset A B s, f.rel q.val.1 q.val.2 := by
        intro q hq
        rcases (mem_toFunFinset A B).1 hq with ⟨p, hp, rfl⟩
        exact hY (Finset.mem_coe.2 (hs hp))
      have hin : funInputUnion A B (toFunFinset A B s) ∈ A.Con := by
        have hsub : ↑(funInputUnion A B (toFunFinset A B s)) ⊆ A.botElement.carrier :=
          fun x hx => emptyEntails_mem_botElement A (hE x (Finset.mem_coe.1 hx))
        exact A.botElement.consistent _ hsub
      have hIO := rel_input_output_union A B f (toFunFinset A B s) hrel hin
      exact IsStrictToken_of_IsStrict A B f hf
        (p := mkFunToken A B (funInputUnion A B (toFunFinset A B s))
          (funOutputUnion A B (toFunFinset A B s)) hin (f.rel_cod hIO))
        hIO hE
  closed := by
    intro Y p hY hEnt
    obtain ⟨_, hFunEnt⟩ := hEnt
    obtain ⟨_, s, hs, hEntIn, hEntOut⟩ := hFunEnt
    have hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2 := by
      intro q hq
      have hq' : q ∈ toFunFinset A B Y := hs hq
      rcases (mem_toFunFinset A B).1 hq' with ⟨r, hr, rfl⟩
      exact hY (Finset.mem_coe.2 hr)
    have hin_s : funInputUnion A B s ∈ A.Con :=
      A.con_subset
        (proposition_2_3_ii A p.val.property.1 (entSet_inputUnion_of_ent A B hEntIn))
        (subset_funion_right _ _)
    have hIO := rel_input_output_union A B f s hrel hin_s
    have hU : f.rel p.val.val.1 (funOutputUnion A B s) :=
      f.mono hIO (entSet_inputUnion_of_ent A B hEntIn)
        (proposition_2_3_iii B (f.rel_cod hIO)) p.val.property.1 (f.rel_cod hIO)
    exact f.mono hU (proposition_2_3_iii A p.val.property.1) hEntOut
      p.val.property.1 p.val.property.2

/-- Scott’s retract map `|A → B| → |A →ₛ B|` induced by `strictify`. -/
def strictifyElement (x : (functionSystem A B).Element) :
    (strictFunctionSystem A B).Element :=
  approxMap_toStrictElement A B (strictify A B (element_toApproxMap A B x))
    (IsStrict_strictify A B _)

/-! ## Conditional: `A × A ≅ (BOOL →ₛ A)` -/

def boolTrue : boolSystem.Element :=
  boolSystem.closure {BoolToken.tru} (boolSystem.con_sing _)

def boolFalse : boolSystem.Element :=
  boolSystem.closure {BoolToken.fls} (boolSystem.con_sing _)

theorem not_ent_empty_tru : ¬ boolSystem.Ent ∅ BoolToken.tru := by
  intro ⟨_, hAll⟩
  exact hAll .undef (fun _ h => absurd h (Finset.notMem_empty _))

theorem not_ent_empty_fls : ¬ boolSystem.Ent ∅ BoolToken.fls := by
  intro ⟨_, hAll⟩
  exact hAll .undef (fun _ h => absurd h (Finset.notMem_empty _))

theorem boolCon_trichotomy {u : Finset BoolToken} (hu : u ∈ boolSystem.Con) :
    EmptyEntails boolSystem u ∨ boolSystem.Ent u .tru ∨ boolSystem.Ent u .fls := by
  obtain ⟨p, hp⟩ := hu
  cases p with
  | undef =>
    refine Or.inl fun t ht => ?_
    have hsat := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.undef, fun _ h => False.elim (Finset.notMem_empty _ h)⟩,
        fun _ _ => boolSat_bot _⟩
    | tru => exact False.elim hsat
    | fls => exact False.elim hsat
  | isTrue =>
    if htru : BoolToken.tru ∈ u then
      exact Or.inr (Or.inl ⟨⟨.isTrue, hp⟩, fun q hq => hq _ htru⟩)
    else
      refine Or.inl fun t ht => ?_
      have hsat := hp t ht
      cases t with
      | bot =>
        exact ⟨⟨.undef, fun _ h => False.elim (Finset.notMem_empty _ h)⟩,
          fun _ _ => boolSat_bot _⟩
      | tru => exact False.elim (htru ht)
      | fls => exact False.elim hsat
  | isFalse =>
    if hfls : BoolToken.fls ∈ u then
      exact Or.inr (Or.inr ⟨⟨.isFalse, hp⟩, fun q hq => hq _ hfls⟩)
    else
      refine Or.inl fun t ht => ?_
      have hsat := hp t ht
      cases t with
      | bot =>
        exact ⟨⟨.undef, fun _ h => False.elim (Finset.notMem_empty _ h)⟩,
          fun _ _ => boolSat_bot _⟩
      | tru => exact False.elim hsat
      | fls => exact False.elim (hfls ht)

theorem subset_of_entSet_mem {x : A.Element} {v v' : Finset α}
    (hv : ↑v ⊆ x.carrier) (hEnt : A.EntSet v v') : ↑v' ⊆ x.carrier := by
  intro y hy
  exact x.closed v y hv (hEnt y (Finset.mem_coe.1 hy))

def condMap (x y : A.Element) : ApproximableMap boolSystem A where
  rel u v :=
    u ∈ boolSystem.Con ∧ v ∈ A.Con ∧
      (EmptyEntails boolSystem u → EmptyEntails A v) ∧
      (boolSystem.Ent u .tru → (↑v : Set α) ⊆ x.carrier) ∧
      (boolSystem.Ent u .fls → (↑v : Set α) ⊆ y.carrier)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := by
    refine ⟨boolSystem.con_empty, A.con_empty, fun _ => emptyEntails_empty A, ?_, ?_⟩
    · exact fun h => False.elim (not_ent_empty_tru h)
    · exact fun h => False.elim (not_ent_empty_fls h)
  union_right := by
    rintro u v v' ⟨hu, hv, hE, ht, hf⟩ ⟨_, hv', hE', ht', hf'⟩
    have hvU : v ∪' v' ∈ A.Con := by
      rcases boolCon_trichotomy hu with hEmp | hTru | hFls
      · have hsub : ↑(v ∪' v') ⊆ A.botElement.carrier := by
          intro z hz
          rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
          · exact emptyEntails_mem_botElement A (hE hEmp z hz)
          · exact emptyEntails_mem_botElement A (hE' hEmp z hz)
        exact A.botElement.consistent _ hsub
      · have hsub : ↑(v ∪' v') ⊆ x.carrier := by
          intro z hz
          rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
          · exact ht hTru (Finset.mem_coe.2 hz)
          · exact ht' hTru (Finset.mem_coe.2 hz)
        exact x.consistent _ hsub
      · have hsub : ↑(v ∪' v') ⊆ y.carrier := by
          intro z hz
          rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
          · exact hf hFls (Finset.mem_coe.2 hz)
          · exact hf' hFls (Finset.mem_coe.2 hz)
        exact y.consistent _ hsub
    refine ⟨hu, hvU, fun hEmp => (emptyEntails_funion A).2 ⟨hE hEmp, hE' hEmp⟩, ?_, ?_⟩
    · intro hTru z hz
      rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
      · exact ht hTru (Finset.mem_coe.2 hz)
      · exact ht' hTru (Finset.mem_coe.2 hz)
    · intro hFls z hz
      rcases mem_funion.mp (Finset.mem_coe.1 hz) with hz | hz
      · exact hf hFls (Finset.mem_coe.2 hz)
      · exact hf' hFls (Finset.mem_coe.2 hz)
  mono := by
    rintro u u' v v' ⟨hu, hv, hE, ht, hf⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_, ?_, ?_⟩
    · intro hEmp
      have hEmpu : EmptyEntails boolSystem u := fun t ht' =>
        boolSystem.ent_trans boolSystem.con_empty hu' hEmp (hEntu t ht')
      exact fun z hz => A.ent_trans A.con_empty hv (hE hEmpu) (hEntv z hz)
    · intro hTru
      rcases boolCon_trichotomy hu with hEmp | hTruU | hFlsU
      · have hEv' : EmptyEntails A v' := fun z hz =>
          A.ent_trans A.con_empty hv (hE hEmp) (hEntv z hz)
        exact fun z hz =>
          (botElement_le A x) (emptyEntails_mem_botElement A (hEv' z (Finset.mem_coe.1 hz)))
      · exact subset_of_entSet_mem A (ht hTruU) hEntv
      · exfalso
        have hFls' : boolSystem.Ent u' .fls :=
          boolSystem.ent_trans hu' hu (fun t ht' => hEntu t ht') hFlsU
        obtain ⟨⟨p, hp⟩, hAllT⟩ := hTru
        obtain ⟨_, hAllF⟩ := hFls'
        have htru : boolSat p .tru := hAllT p hp
        have hfls : boolSat p .fls := hAllF p hp
        cases p <;> simp only [boolSat] at htru hfls
    · intro hFls
      rcases boolCon_trichotomy hu with hEmp | hTruU | hFlsU
      · have hEv' : EmptyEntails A v' := fun z hz =>
          A.ent_trans A.con_empty hv (hE hEmp) (hEntv z hz)
        exact fun z hz =>
          (botElement_le A y) (emptyEntails_mem_botElement A (hEv' z (Finset.mem_coe.1 hz)))
      · exfalso
        have hTru' : boolSystem.Ent u' .tru :=
          boolSystem.ent_trans hu' hu (fun t ht' => hEntu t ht') hTruU
        obtain ⟨⟨p, hp⟩, hAllF⟩ := hFls
        obtain ⟨_, hAllT⟩ := hTru'
        have hfls : boolSat p .fls := hAllF p hp
        have htru : boolSat p .tru := hAllT p hp
        cases p <;> simp only [boolSat] at htru hfls
      · exact subset_of_entSet_mem A (hf hFlsU) hEntv

theorem IsStrict_condMap (x y : A.Element) : IsStrict boolSystem A (condMap A x y) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨_, _, hE, _, _⟩⟩
    have hEmp : EmptyEntails boolSystem u := fun t ht =>
      mem_botElement_emptyEntails boolSystem (hu (Finset.mem_coe.2 ht))
    exact emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _))
  · exact botElement_le A _

theorem not_ent_tru_fls : ¬ boolSystem.Ent {BoolToken.tru} BoolToken.fls := by
  intro ⟨⟨p, hp⟩, hAll⟩
  have htru : boolSat p .tru := hp .tru (Finset.mem_singleton_self _)
  have hfls : boolSat p .fls := hAll p hp
  cases p <;> simp only [boolSat] at htru hfls

theorem not_ent_fls_tru : ¬ boolSystem.Ent {BoolToken.fls} BoolToken.tru := by
  intro ⟨⟨p, hp⟩, hAll⟩
  have hfls : boolSat p .fls := hp .fls (Finset.mem_singleton_self _)
  have htru : boolSat p .tru := hAll p hp
  cases p <;> simp only [boolSat] at htru hfls

theorem not_emptyEntails_singleton_tru :
    ¬ EmptyEntails boolSystem ({BoolToken.tru} : Finset BoolToken) :=
  fun h => not_ent_empty_tru (h .tru (Finset.mem_singleton_self _))

theorem not_emptyEntails_singleton_fls :
    ¬ EmptyEntails boolSystem ({BoolToken.fls} : Finset BoolToken) :=
  fun h => not_ent_empty_fls (h .fls (Finset.mem_singleton_self _))

theorem condMap_toElement_boolTrue (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨huC, _, hE, ht, _⟩⟩
    rcases boolCon_trichotomy huC with hEmp | hTru | hFls
    · exact (botElement_le A x)
        (emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _)))
    · exact ht hTru (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    · exfalso
      obtain ⟨⟨_, _⟩, hAll⟩ := hFls
      have : boolSat .isTrue .fls := hAll .isTrue fun t ht' =>
        (hu (Finset.mem_coe.2 ht')).2 .isTrue fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial
      simp only [boolSat] at this
  · intro Z hZ
    refine ⟨{BoolToken.tru}, ?_, boolSystem.con_sing _, A.con_sing _, ?_, ?_, ?_⟩
    · intro t ht
      have : t = .tru := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
      subst this
      exact (boolSystem.subset_closure (boolSystem.con_sing _))
        (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    · exact fun hEmp => False.elim (not_emptyEntails_singleton_tru hEmp)
    · intro _ z hz
      have : z = Z := Finset.mem_singleton.mp (Finset.mem_coe.1 hz)
      subst this; exact hZ
    · exact fun hFls => False.elim (not_ent_tru_fls hFls)

theorem condMap_toElement_boolFalse (x y : A.Element) :
    (condMap A x y).toElement boolFalse = y := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨huC, _, hE, _, hf⟩⟩
    rcases boolCon_trichotomy huC with hEmp | hTru | hFls
    · exact (botElement_le A y)
        (emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _)))
    · exfalso
      obtain ⟨⟨_, _⟩, hAll⟩ := hTru
      have : boolSat .isFalse .tru := hAll .isFalse fun t ht' =>
        (hu (Finset.mem_coe.2 ht')).2 .isFalse fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial
      simp only [boolSat] at this
    · exact hf hFls (Finset.mem_coe.2 (Finset.mem_singleton_self _))
  · intro Z hZ
    refine ⟨{BoolToken.fls}, ?_, boolSystem.con_sing _, A.con_sing _, ?_, ?_, ?_⟩
    · intro t ht
      have : t = .fls := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
      subst this
      exact (boolSystem.subset_closure (boolSystem.con_sing _))
        (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    · exact fun hEmp => False.elim (not_emptyEntails_singleton_fls hEmp)
    · exact fun hTru => False.elim (not_ent_fls_tru hTru)
    · intro _ z hz
      have : z = Z := Finset.mem_singleton.mp (Finset.mem_coe.1 hz)
      subst this; exact hZ

/-- `cond` as an element of `|BOOL →ₛ A|`. -/
def condElement (z : (productSystem A A).Element) :
    (strictFunctionSystem boolSystem A).Element :=
  approxMap_toStrictElement boolSystem A
    (condMap A ((fstMap A A).toElement z) ((sndMap A A).toElement z))
    (IsStrict_condMap A _ _)

/-- One direction of the conditional isomorphism on pairs. -/
theorem condMap_pair_roundtrip (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x ∧
    (condMap A x y).toElement boolFalse = y :=
  ⟨condMap_toElement_boolTrue A x y, condMap_toElement_boolFalse A x y⟩

theorem entSet_singleton_tru_of_ent_tru {u : Finset BoolToken}
    (_hu : u ∈ boolSystem.Con) (h : boolSystem.Ent u .tru) :
    boolSystem.EntSet ({BoolToken.tru} : Finset BoolToken) u := by
  intro t ht
  obtain ⟨⟨p, hp⟩, hAll⟩ := h
  have htru : boolSat p .tru := hAll p hp
  cases p with
  | undef => simp only [boolSat] at htru
  | isFalse => simp only [boolSat] at htru
  | isTrue =>
    have hsat : boolSat .isTrue t := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.isTrue, fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun _ _ => boolSat_bot _⟩
    | tru =>
      exact ⟨⟨.isTrue, fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun q hq => hq .tru (Finset.mem_singleton_self _)⟩
    | fls => exact False.elim hsat

theorem entSet_singleton_fls_of_ent_fls {u : Finset BoolToken}
    (_hu : u ∈ boolSystem.Con) (h : boolSystem.Ent u .fls) :
    boolSystem.EntSet ({BoolToken.fls} : Finset BoolToken) u := by
  intro t ht
  obtain ⟨⟨p, hp⟩, hAll⟩ := h
  have hfls : boolSat p .fls := hAll p hp
  cases p with
  | undef => simp only [boolSat] at hfls
  | isTrue => simp only [boolSat] at hfls
  | isFalse =>
    have hsat : boolSat .isFalse t := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun _ _ => boolSat_bot _⟩
    | fls =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun q hq => hq .fls (Finset.mem_singleton_self _)⟩
    | tru => exact False.elim hsat

/-- Every strict BOOL-map is `cond` of its values at true and false. -/
theorem condMap_unique (f : ApproximableMap boolSystem A) (hf : IsStrict boolSystem A f) :
    f = condMap A (f.toElement boolTrue) (f.toElement boolFalse) := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · intro hrel
    refine ⟨f.rel_dom hrel, f.rel_cod hrel, ?_, ?_, ?_⟩
    · intro hEmp
      have hsub : ↑u ⊆ boolSystem.botElement.carrier := fun t ht =>
        emptyEntails_mem_botElement boolSystem (hEmp t (Finset.mem_coe.1 ht))
      have hout : ↑v ⊆ (f.toElement boolSystem.botElement).carrier := by
        intro y hy
        refine ⟨u, hsub, f.mono hrel (proposition_2_3_iii boolSystem (f.rel_dom hrel))
          (fun z hz => by
            have : z = y := Finset.mem_singleton.mp hz
            subst this
            exact A.ent_refl (f.rel_cod hrel) (Finset.mem_coe.1 hy))
          (f.rel_dom hrel) (A.con_sing y)⟩
      rw [hf] at hout
      exact fun y hy => mem_botElement_emptyEntails A (hout (Finset.mem_coe.2 hy))
    · intro hTru y hy
      have hEntU : boolSystem.EntSet {BoolToken.tru} u :=
        entSet_singleton_tru_of_ent_tru (f.rel_dom hrel) hTru
      refine ⟨{BoolToken.tru}, ?_, ?_⟩
      · exact boolSystem.subset_closure (boolSystem.con_sing _)
      · exact f.mono hrel hEntU
          (fun z hz => by
            have : z = y := Finset.mem_singleton.mp hz
            subst this
            exact A.ent_refl (f.rel_cod hrel) (Finset.mem_coe.1 hy))
          (boolSystem.con_sing _) (A.con_sing y)
    · intro hFls y hy
      have hEntU : boolSystem.EntSet {BoolToken.fls} u :=
        entSet_singleton_fls_of_ent_fls (f.rel_dom hrel) hFls
      refine ⟨{BoolToken.fls}, ?_, ?_⟩
      · exact boolSystem.subset_closure (boolSystem.con_sing _)
      · exact f.mono hrel hEntU
          (fun z hz => by
            have : z = y := Finset.mem_singleton.mp hz
            subst this
            exact A.ent_refl (f.rel_cod hrel) (Finset.mem_coe.1 hy))
          (boolSystem.con_sing _) (A.con_sing y)
  · intro ⟨hu, hv, hE, ht, hfl⟩
    rcases boolCon_trichotomy hu with hEmp | hTru | hFls
    · have hrel0 : f.rel u ∅ :=
        f.mono f.empty_rel (boolSystem.entSet_empty u) (A.entSet_empty ∅) hu A.con_empty
      exact f.mono hrel0 (proposition_2_3_iii boolSystem hu) (hE hEmp) hu hv
    · have hsub : ↑v ⊆ (f.toElement boolTrue).carrier := ht hTru
      obtain ⟨w, hw, hrelw⟩ := exists_rel_of_subset_image f boolTrue v hsub
      have hEntW : boolSystem.EntSet {BoolToken.tru} w := fun t ht' =>
        hw (Finset.mem_coe.2 ht')
      have hrelTru : f.rel {BoolToken.tru} v :=
        f.mono hrelw hEntW (proposition_2_3_iii A (f.rel_cod hrelw))
          (boolSystem.con_sing _) (f.rel_cod hrelw)
      have hEntU : boolSystem.EntSet u {BoolToken.tru} := fun t ht' => by
        have : t = .tru := Finset.mem_singleton.mp ht'
        subst this; exact hTru
      exact f.mono hrelTru hEntU (proposition_2_3_iii A hv) hu hv
    · have hsub : ↑v ⊆ (f.toElement boolFalse).carrier := hfl hFls
      obtain ⟨w, hw, hrelw⟩ := exists_rel_of_subset_image f boolFalse v hsub
      have hEntW : boolSystem.EntSet {BoolToken.fls} w := fun t ht' =>
        hw (Finset.mem_coe.2 ht')
      have hrelFls : f.rel {BoolToken.fls} v :=
        f.mono hrelw hEntW (proposition_2_3_iii A (f.rel_cod hrelw))
          (boolSystem.con_sing _) (f.rel_cod hrelw)
      have hEntU : boolSystem.EntSet u {BoolToken.fls} := fun t ht' => by
        have : t = .fls := Finset.mem_singleton.mp ht'
        subst this; exact hFls
      exact f.mono hrelFls hEntU (proposition_2_3_iii A hv) hu hv

/-- Domain isomorphism data: `A × A ≅ (BOOL →ₛ A)` via `cond`. -/
theorem conditional_iso (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x ∧
    (condMap A x y).toElement boolFalse = y ∧
    ∀ (f : ApproximableMap boolSystem A), IsStrict boolSystem A f →
      f = condMap A (f.toElement boolTrue) (f.toElement boolFalse) :=
  ⟨condMap_toElement_boolTrue A x y, condMap_toElement_boolFalse A x y,
    fun f hf => condMap_unique A f hf⟩

end InfoSys

end Scott1982
