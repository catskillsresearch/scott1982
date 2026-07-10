import Scott1982.Sum
import Scott1982.Factoid33
import Scott1982.Proposition53
import Scott1982.Proposition55

/-!
# Proposition 6.4 — sum injections and copairing

**Scott 1982, Proposition 6.4.** Approximable `inl`, `inr`, and unique copairing
`[f, g]` with `[f, g] ∘ inl = f`, `[f, g] ∘ inr = g`, and `[f, g](⊥) = ⊥`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

private instance instLeftCommutativeLiftSumLeft :
    LeftCommutative fun x : α =>
      (insert (SumToken.left (β := β) x) : Finset (SumToken α β) → Finset _) :=
  ⟨fun _ _ s => insert_comm' _ _ s⟩

private instance instLeftCommutativeLiftSumRight :
    LeftCommutative fun y : β =>
      (insert (SumToken.right (α := α) y) : Finset (SumToken α β) → Finset _) :=
  ⟨fun _ _ s => insert_comm' _ _ s⟩

/-- Embed `A`-tokens as left sum tokens. -/
def liftSumLeft (v : Finset α) : Finset (SumToken α β) :=
  Multiset.foldr (fun x : α => insert (SumToken.left (β := β) x))
    (∅ : Finset (SumToken α β)) v.1

/-- Embed `B`-tokens as right sum tokens. -/
def liftSumRight (w : Finset β) : Finset (SumToken α β) :=
  Multiset.foldr (fun y : β => insert (SumToken.right (α := α) y))
    (∅ : Finset (SumToken α β)) w.1

private theorem mem_foldr_liftSumLeft (s : Multiset α) (p : SumToken α β) :
    p ∈ Multiset.foldr (fun x : α => insert (SumToken.left (β := β) x))
        (∅ : Finset (SumToken α β)) s ↔
      ∃ x ∈ s, p = .left x := by
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

private theorem mem_foldr_liftSumRight (s : Multiset β) (p : SumToken α β) :
    p ∈ Multiset.foldr (fun y : β => insert (SumToken.right (α := α) y))
        (∅ : Finset (SumToken α β)) s ↔
      ∃ y ∈ s, p = .right y := by
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

theorem mem_liftSumLeft {v : Finset α} {p : SumToken α β} :
    p ∈ liftSumLeft (β := β) v ↔ ∃ x ∈ v, p = .left x := by
  simpa [liftSumLeft] using mem_foldr_liftSumLeft (β := β) v.1 p

theorem mem_liftSumRight {w : Finset β} {p : SumToken α β} :
    p ∈ liftSumRight (α := α) w ↔ ∃ y ∈ w, p = .right y := by
  simpa [liftSumRight] using mem_foldr_liftSumRight (α := α) w.1 p

theorem lftFinset_liftSumLeft (v : Finset α) :
    lftFinset (liftSumLeft (β := β) v) = v := by
  ext x
  simp only [mem_lftFinset, mem_liftSumLeft]
  exact ⟨fun ⟨y, hy, h⟩ => by injection h with h'; exact h' ▸ hy,
    fun hx => ⟨x, hx, rfl⟩⟩

theorem rhtFinset_liftSumLeft (v : Finset α) :
    rhtFinset (liftSumLeft (β := β) v) = ∅ := by
  ext y
  constructor
  · intro hy
    rcases (mem_liftSumLeft (β := β)).1 ((mem_rhtFinset).1 hy) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem rhtFinset_liftSumRight (w : Finset β) :
    rhtFinset (liftSumRight (α := α) w) = w := by
  ext y
  simp only [mem_rhtFinset, mem_liftSumRight]
  exact ⟨fun ⟨z, hz, h⟩ => by injection h with h'; exact h' ▸ hz,
    fun hy => ⟨y, hy, rfl⟩⟩

theorem lftFinset_liftSumRight (w : Finset β) :
    lftFinset (liftSumRight (α := α) w) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases (mem_liftSumRight (α := α)).1 ((mem_lftFinset).1 hx) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem SumCon_liftSumLeft {v : Finset α} (hv : v ∈ A.Con) :
    SumCon A B (liftSumLeft (β := β) v) :=
  Or.inl ⟨by rw [lftFinset_liftSumLeft]; exact hv, rhtFinset_liftSumLeft (β := β) v⟩

theorem SumCon_liftSumRight {w : Finset β} (hw : w ∈ B.Con) :
    SumCon A B (liftSumRight (α := α) w) :=
  Or.inr ⟨lftFinset_liftSumRight (α := α) w, by rw [rhtFinset_liftSumRight]; exact hw⟩

theorem rht_eq_empty_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hr : rhtFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    rhtFinset u' = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim ((hEnt _ ((mem_rhtFinset).1 hy)).2.1 hr)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem lft_eq_empty_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    lftFinset u' = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim ((hEnt _ ((mem_lftFinset).1 hx)).2.1 hl)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem entSet_lft_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    A.EntSet (lftFinset u) (lftFinset u') := fun _ hx =>
  (hEnt _ ((mem_lftFinset).1 hx)).2.2

theorem entSet_rht_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hEnt : (sumSystem A B).EntSet u u') :
    B.EntSet (rhtFinset u) (rhtFinset u') := fun _ hy =>
  (hEnt _ ((mem_rhtFinset).1 hy)).2.2

theorem lft_mem_Con_of_SumCon_rht_empty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (_hr : rhtFinset u = ∅) : lftFinset u ∈ A.Con := by
  rcases hu with ⟨hl, _⟩ | ⟨hl, _⟩
  · exact hl
  · rw [hl]; exact A.con_empty

theorem rht_mem_Con_of_SumCon_lft_empty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (_hl : lftFinset u = ∅) : rhtFinset u ∈ B.Con := by
  rcases hu with ⟨_, hr⟩ | ⟨_, hr⟩
  · rw [hr]; exact B.con_empty
  · exact hr

namespace ApproximableMap

variable {C : InfoSys γ}

/-- **Proposition 6.4(1).** Left injection. -/
def inlMap : ApproximableMap A (sumSystem A B) where
  rel v u := v ∈ A.Con ∧ SumCon A B u ∧ rhtFinset u = ∅ ∧ A.EntSet v (lftFinset u)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, SumCon_empty A B, by rw [rhtFinset_empty], A.entSet_empty ∅⟩
  union_right := by
    rintro v u u' ⟨hv, hu, hr, hEnt⟩ ⟨_, hu', hr', hEnt'⟩
    refine ⟨hv, ?_, ?_, ?_⟩
    · have hl : lftFinset (u ∪' u') ∈ A.Con := by
        rw [lftFinset_funion]
        exact A.con_subset
          (proposition_2_3_ii (sys := A) hv (proposition_2_3_vi (sys := A) hEnt hEnt'))
          (subset_funion_right _ _)
      exact Or.inl ⟨hl, by rw [rhtFinset_funion, hr, hr']; rfl⟩
    · rw [rhtFinset_funion, hr, hr']; rfl
    · rw [lftFinset_funion]; exact proposition_2_3_vi (sys := A) hEnt hEnt'
  mono := by
    rintro v v' u u' ⟨hv, hu, hr, hEnt⟩ hEntv hEntu hv' hu'
    refine ⟨hv', hu', rht_eq_empty_of_sumEntSet A B hr hEntu, ?_⟩
    exact proposition_2_3_iv (sys := A) hv'
      (lft_mem_Con_of_SumCon_rht_empty A B hu hr)
      (proposition_2_3_iv (sys := A) hv' hv hEntv hEnt)
      (entSet_lft_of_sumEntSet A B hEntu)

/-- **Proposition 6.4(2).** Right injection. -/
def inrMap : ApproximableMap B (sumSystem A B) where
  rel w u := w ∈ B.Con ∧ SumCon A B u ∧ lftFinset u = ∅ ∧ B.EntSet w (rhtFinset u)
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨B.con_empty, SumCon_empty A B, by rw [lftFinset_empty], B.entSet_empty ∅⟩
  union_right := by
    rintro w u u' ⟨hw, hu, hl, hEnt⟩ ⟨_, hu', hl', hEnt'⟩
    refine ⟨hw, ?_, ?_, ?_⟩
    · have hrC : rhtFinset (u ∪' u') ∈ B.Con := by
        rw [rhtFinset_funion]
        exact B.con_subset
          (proposition_2_3_ii (sys := B) hw (proposition_2_3_vi (sys := B) hEnt hEnt'))
          (subset_funion_right _ _)
      exact Or.inr ⟨by rw [lftFinset_funion, hl, hl']; rfl, hrC⟩
    · rw [lftFinset_funion, hl, hl']; rfl
    · rw [rhtFinset_funion]; exact proposition_2_3_vi (sys := B) hEnt hEnt'
  mono := by
    rintro w w' u u' ⟨hw, hu, hl, hEnt⟩ hEntw hEntu hw' hu'
    refine ⟨hw', hu', lft_eq_empty_of_sumEntSet A B hl hEntu, ?_⟩
    exact proposition_2_3_iv (sys := B) hw'
      (rht_mem_Con_of_SumCon_lft_empty A B hu hl)
      (proposition_2_3_iv (sys := B) hw' hw hEntw hEnt)
      (entSet_rht_of_sumEntSet A B hEntu)

private theorem copair_union_disj (f : ApproximableMap A C) (g : ApproximableMap B C)
    {u : Finset (SumToken α β)} {s s' : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hs' : s' ∈ C.Con)
    (h : C.EntSet ∅ s ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
    (h' : C.EntSet ∅ s' ∨ (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s') ∨
      (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s')) :
    C.EntSet ∅ (s ∪' s') ∨
      (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) (s ∪' s')) ∨
        (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) (s ∪' s')) := by
  rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩ <;> rcases h' with h' | ⟨hne', hf'⟩ | ⟨hne', hg'⟩
  · exact Or.inl (proposition_2_3_vi (sys := C) h h')
  · have hf0 : f.rel (lftFinset u) s :=
      f.mono f.empty_rel (A.entSet_empty _) h
        (SumCon_lft_con_of_lft_nonempty A B hu hne') hs
    exact Or.inr (Or.inl ⟨hne', f.union_right hf0 hf'⟩)
  · have hg0 : g.rel (rhtFinset u) s :=
      g.mono g.empty_rel (B.entSet_empty _) h
        (SumCon_rht_con_of_rht_nonempty A B hu hne') hs
    exact Or.inr (Or.inr ⟨hne', g.union_right hg0 hg'⟩)
  · have hf0 : f.rel (lftFinset u) s' :=
      f.mono f.empty_rel (A.entSet_empty _) h'
        (SumCon_lft_con_of_lft_nonempty A B hu hne) hs'
    exact Or.inr (Or.inl ⟨hne, f.union_right hf hf0⟩)
  · exact Or.inr (Or.inl ⟨hne, f.union_right hf hf'⟩)
  · exact False.elim (hne' (SumCon_rht_empty_of_lft_nonempty A B hu hne))
  · have hg0 : g.rel (rhtFinset u) s' :=
      g.mono g.empty_rel (B.entSet_empty _) h'
        (SumCon_rht_con_of_rht_nonempty A B hu hne) hs'
    exact Or.inr (Or.inr ⟨hne, g.union_right hg hg0⟩)
  · exact False.elim (hne' (SumCon_lft_empty_of_rht_nonempty A B hu hne))
  · exact Or.inr (Or.inr ⟨hne, g.union_right hg hg'⟩)

/-- **Proposition 6.4(3).** Copairing of approximable maps. -/
def copairMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    ApproximableMap (sumSystem A B) C where
  rel u s :=
    SumCon A B u ∧ s ∈ C.Con ∧
      (C.EntSet ∅ s ∨
        (lftFinset u ≠ ∅ ∧ f.rel (lftFinset u) s) ∨
          (rhtFinset u ≠ ∅ ∧ g.rel (rhtFinset u) s))
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨SumCon_empty A B, C.con_empty, Or.inl (C.entSet_empty ∅)⟩
  union_right := by
    rintro u s s' ⟨hu, hs, h⟩ ⟨_, hs', h'⟩
    have hU := copair_union_disj A B f g hu hs hs' h h'
    refine ⟨hu, ?_, hU⟩
    rcases hU with hE | ⟨_, hf⟩ | ⟨_, hg⟩
    · exact C.con_subset (proposition_2_3_ii (sys := C) C.con_empty hE)
        (subset_funion_right _ _)
    · exact f.rel_cod hf
    · exact g.rel_cod hg
  mono := by
    rintro u u' s s' ⟨hu, hs, h⟩ hEntu hEnts hu' hs'
    refine ⟨hu', hs', ?_⟩
    rcases h with h | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · exact Or.inl (proposition_2_3_iv (sys := C) C.con_empty hs h hEnts)
    · have hne' : lftFinset u' ≠ ∅ := by
        obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_lftFinset).1 hx)).2.1
      exact Or.inr (Or.inl ⟨hne',
        f.mono hf (entSet_lft_of_sumEntSet A B hEntu) hEnts
          (SumCon_lft_con_of_lft_nonempty A B hu' hne') hs'⟩)
    · have hne' : rhtFinset u' ≠ ∅ := by
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        exact (hEntu _ ((mem_rhtFinset).1 hy)).2.1
      exact Or.inr (Or.inr ⟨hne',
        g.mono hg (entSet_rht_of_sumEntSet A B hEntu) hEnts
          (SumCon_rht_con_of_rht_nonempty A B hu' hne') hs'⟩)

theorem comp_copairMap_inlMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inlMap A B) = f := by
  refine ApproximableMap.ext fun v s => ?_
  constructor
  · rintro ⟨u, ⟨hv, hu, hr, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨_, hf⟩ | ⟨hne, _⟩
    · exact f.mono f.empty_rel (A.entSet_empty v) hE hv hs
    · exact f.mono hf hEnt (proposition_2_3_iii C hs) hv hs
    · exact False.elim (hne hr)
  · intro hf
    -- Always lift `insert Δ v` so the left branch of copair is nonempty (avoids
    -- classical `by_cases` on `v = ∅`).
    let vBot := insert A.bot v
    have hvBot : vBot ∈ A.Con := A.ent_con (A.ent_bot (f.rel_dom hf))
    have hEntBot : A.EntSet vBot v :=
      fun _ hx => A.ent_refl hvBot (Finset.mem_insert_of_mem hx)
    have hfBot : f.rel vBot s :=
      f.mono hf hEntBot (proposition_2_3_iii C (f.rel_cod hf)) hvBot (f.rel_cod hf)
    refine ⟨liftSumLeft (β := β) vBot, ?_, ?_⟩
    · refine ⟨f.rel_dom hf, SumCon_liftSumLeft A B hvBot,
        rhtFinset_liftSumLeft (β := β) vBot, ?_⟩
      rw [lftFinset_liftSumLeft]
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst hx; exact A.ent_bot (f.rel_dom hf)
      · exact A.ent_refl (f.rel_dom hf) hx
    · refine ⟨SumCon_liftSumLeft A B hvBot, f.rel_cod hf, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
      · rw [lftFinset_liftSumLeft]; exact Finset.insert_ne_empty A.bot v
      · rw [lftFinset_liftSumLeft]; exact hfBot

theorem comp_copairMap_inrMap (f : ApproximableMap A C) (g : ApproximableMap B C) :
    comp (copairMap A B f g) (inrMap A B) = g := by
  refine ApproximableMap.ext fun w s => ?_
  constructor
  · rintro ⟨u, ⟨hw, hu, hl, hEnt⟩, ⟨_, hs, hcop⟩⟩
    rcases hcop with hE | ⟨hne, _⟩ | ⟨_, hg⟩
    · exact g.mono g.empty_rel (B.entSet_empty w) hE hw hs
    · exact False.elim (hne hl)
    · exact g.mono hg hEnt (proposition_2_3_iii C hs) hw hs
  · intro hg
    let wBot := insert B.bot w
    have hwBot : wBot ∈ B.Con := B.ent_con (B.ent_bot (g.rel_dom hg))
    have hEntBot : B.EntSet wBot w :=
      fun _ hy => B.ent_refl hwBot (Finset.mem_insert_of_mem hy)
    have hgBot : g.rel wBot s :=
      g.mono hg hEntBot (proposition_2_3_iii C (g.rel_cod hg)) hwBot (g.rel_cod hg)
    refine ⟨liftSumRight (α := α) wBot, ?_, ?_⟩
    · refine ⟨g.rel_dom hg, SumCon_liftSumRight A B hwBot,
        lftFinset_liftSumRight (α := α) wBot, ?_⟩
      rw [rhtFinset_liftSumRight]
      intro y hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · subst hy; exact B.ent_bot (g.rel_dom hg)
      · exact B.ent_refl (g.rel_dom hg) hy
    · refine ⟨SumCon_liftSumRight A B hwBot, g.rel_cod hg, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · rw [rhtFinset_liftSumRight]; exact Finset.insert_ne_empty B.bot w
      · rw [rhtFinset_liftSumRight]; exact hgBot

theorem copairMap_botElement (f : ApproximableMap A C) (g : ApproximableMap B C) :
    (copairMap A B f g).toElement (sumSystem A B).botElement = C.botElement := by
  apply le_antisymm
  · intro Y ⟨u, hu, ⟨huCon, hs, hcop⟩⟩
    have onlyBot : ∀ p ∈ u, p = SumToken.bot (α := α) (β := β) := by
      intro p hp
      have hEnt : (sumSystem A B).Ent {sumBot} p := hu (Finset.mem_coe.2 hp)
      cases p with
      | bot => rfl
      | left x =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : lftFinset ({sumBot} : Finset (SumToken α β)) = ∅ := lftFinset_singleton_bot
          exact hne this)
      | right y =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : rhtFinset ({sumBot} : Finset (SumToken α β)) = ∅ := rhtFinset_singleton_bot
          exact hne this)
    have hl : lftFinset u = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch onlyBot _ ((mem_lftFinset).1 hx))
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    have hr : rhtFinset u = ∅ := by
      ext y; constructor
      · intro hy; exact False.elim (nomatch onlyBot _ ((mem_rhtFinset).1 hy))
      · intro hy; exact False.elim (Finset.notMem_empty y hy)
    rcases hcop with hE | ⟨hne, _⟩ | ⟨hne, _⟩
    · exact C.ent_trans (C.con_sing C.bot) C.con_empty
        (fun _ hz => False.elim (Finset.notMem_empty _ hz))
        (hE Y (Finset.mem_singleton_self _))
    · exact False.elim (hne hl)
    · exact False.elim (hne hr)
  · intro Y hY
    refine ⟨∅, fun _ hp => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 hp)), ?_⟩
    refine ⟨SumCon_empty A B, C.con_sing Y, Or.inl ?_⟩
    intro Z hZ
    have : Z = Y := Finset.mem_singleton.mp hZ
    subst this
    exact C.ent_trans C.con_empty (C.con_sing C.bot)
      (fun _ hz => by
        have : _ = C.bot := Finset.mem_singleton.mp hz
        subst this
        exact C.ent_bot C.con_empty)
      hY

/-- Carrier of the left copy extracted from a sum element. -/
def sumLftCarrier (z : (sumSystem A B).Element) : Set α :=
  {x | SumToken.left x ∈ z.carrier}

/-- Carrier of the right copy extracted from a sum element. -/
def sumRhtCarrier (z : (sumSystem A B).Element) : Set β :=
  {y | SumToken.right y ∈ z.carrier}

/-- Left copy as an `A`-element, given some left token in `z`. -/
def sumElementLft (z : (sumSystem A B).Element)
    (x0 : α) (hx0 : SumToken.left x0 ∈ z.carrier) : A.Element where
  carrier := sumLftCarrier A B z
  consistent := by
    intro Y hY
    have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (mem_liftSumLeft (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
      exact hY (Finset.mem_coe.2 hx)
    have h := lft_mem_Con_of_SumCon_rht_empty A B (z.consistent _ hsub)
      (rhtFinset_liftSumLeft (β := β) Y)
    rwa [lftFinset_liftSumLeft] at h
  closed := by
    intro Y a hY hEnt
    if hempty : Y = ∅ then
      subst hempty
      have hEnt' : A.Ent {x0} a :=
        A.ent_trans (A.con_sing x0) A.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.left x0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .left x0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hx0
      have hSum : (sumSystem A B).Ent {SumToken.left x0} (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [lftFinset_singleton_left]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumLeft (β := β) Y) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (mem_liftSumLeft (β := β)).1 (Finset.mem_coe.1 hp) with ⟨x, hx, rfl⟩
        exact hY (Finset.mem_coe.2 hx)
      have hSum : (sumSystem A B).Ent (liftSumLeft (β := β) Y) (.left a) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [lftFinset_liftSumLeft]; exact hempty
        · rw [lftFinset_liftSumLeft]; exact hEnt
      exact z.closed _ _ hsub hSum

/-- Right copy as a `B`-element, given some right token in `z`. -/
def sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) : B.Element where
  carrier := sumRhtCarrier A B z
  consistent := by
    intro W hW
    have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
      intro p hp
      rcases (mem_liftSumRight (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
      exact hW (Finset.mem_coe.2 hy)
    have h := rht_mem_Con_of_SumCon_lft_empty A B (z.consistent _ hsub)
      (lftFinset_liftSumRight (α := α) W)
    rwa [rhtFinset_liftSumRight] at h
  closed := by
    intro W b hW hEnt
    if hempty : W = ∅ then
      subst hempty
      have hEnt' : B.Ent {y0} b :=
        B.ent_trans (B.con_sing y0) B.con_empty
          (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
      have hsub : (↑({SumToken.right y0} : Finset (SumToken α β)) : Set _) ⊆ z.carrier := by
        intro p hp
        have : p = .right y0 := Finset.mem_singleton.mp (Finset.mem_coe.1 hp)
        subst this; exact hy0
      have hSum : (sumSystem A B).Ent {SumToken.right y0} (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨Finset.singleton_ne_empty _, ?_⟩⟩
        rw [rhtFinset_singleton_right]; exact hEnt'
      exact z.closed _ _ hsub hSum
    else
      have hsub : (↑(liftSumRight (α := α) W) : Set _) ⊆ z.carrier := by
        intro p hp
        rcases (mem_liftSumRight (α := α)).1 (Finset.mem_coe.1 hp) with ⟨y, hy, rfl⟩
        exact hW (Finset.mem_coe.2 hy)
      have hSum : (sumSystem A B).Ent (liftSumRight (α := α) W) (.right b) := by
        refine ⟨z.consistent _ hsub, ⟨?_, ?_⟩⟩
        · rw [rhtFinset_liftSumRight]; exact hempty
        · rw [rhtFinset_liftSumRight]; exact hEnt
      exact z.closed _ _ hsub hSum

theorem not_mem_right_of_mem_left (z : (sumSystem A B).Element)
    {x : α} {y : β} (hx : SumToken.left x ∈ z.carrier)
    (hy : SumToken.right y ∈ z.carrier) : False := by
  let u : Finset (SumToken α β) := insert (.left x) {SumToken.right y}
  have hsub : (↑u : Set _) ⊆ z.carrier := by
    intro p hp
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hp) with h | h
    · subst h; exact hx
    · have : p = .right y := Finset.mem_singleton.mp h
      subst this; exact hy
  have hCon := z.consistent u hsub
  have hlne : lftFinset u ≠ ∅ := by
    intro h
    have : x ∈ lftFinset u := (mem_lftFinset).2 (Finset.mem_insert_self _ _)
    rw [h] at this
    exact Finset.notMem_empty _ this
  have hrne : rhtFinset u ≠ ∅ := by
    intro h
    have : y ∈ rhtFinset u :=
      (mem_rhtFinset).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [h] at this
    exact Finset.notMem_empty _ this
  rcases hCon with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact hrne hr
  · exact hlne hl

theorem inlMap_toElement_sumElementLft (z : (sumSystem A B).Element)
    (x0 : α) (hx0 : SumToken.left x0 ∈ z.carrier) :
    (inlMap A B).toElement (sumElementLft A B z x0 hx0) = z := by
  apply le_antisymm
  · intro p ⟨v, hv, ⟨hvCon, huCon, hr, hEnt⟩⟩
    cases p with
    | bot => exact factoid_3_2 (sumSystem A B) z
    | left x =>
      have hEntx : A.Ent v x := by
        have : lftFinset ({SumToken.left x} : Finset (SumToken α β)) = {x} :=
          lftFinset_singleton_left x
        simpa [this] using hEnt x (Finset.mem_singleton_self x)
      exact (sumElementLft A B z x0 hx0).closed v x hv hEntx
    | right y =>
      have : rhtFinset ({SumToken.right y} : Finset (SumToken α β)) = {y} :=
        rhtFinset_singleton_right y
      exact False.elim (Finset.singleton_ne_empty y (this ▸ hr))
  · intro p hp
    cases p with
    | bot =>
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h)), ?_⟩
      exact ⟨A.con_empty, (sumSystem A B).con_sing _, by rw [rhtFinset_singleton_bot],
        A.entSet_empty _⟩
    | left x =>
      refine ⟨{x}, ?_, ?_⟩
      · intro a ha
        have : a = x := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
        subst this; exact hp
      · refine ⟨A.con_sing x, (sumSystem A B).con_sing _, ?_, ?_⟩
        · ext y; constructor
          · intro hy
            have : SumToken.right y ∈ ({SumToken.left x} : Finset _) := (mem_rhtFinset).1 hy
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hy; exact False.elim (Finset.notMem_empty y hy)
        · rw [lftFinset_singleton_left]
          exact proposition_2_3_iii A (A.con_sing x)
    | right y =>
      exact False.elim (not_mem_right_of_mem_left A B z hx0 hp)

theorem inrMap_toElement_sumElementRht (z : (sumSystem A B).Element)
    (y0 : β) (hy0 : SumToken.right y0 ∈ z.carrier) :
    (inrMap A B).toElement (sumElementRht A B z y0 hy0) = z := by
  apply le_antisymm
  · intro p ⟨w, hw, ⟨hwCon, huCon, hl, hEnt⟩⟩
    cases p with
    | bot => exact factoid_3_2 (sumSystem A B) z
    | right y =>
      have hEnty : B.Ent w y := by
        have : rhtFinset ({SumToken.right y} : Finset (SumToken α β)) = {y} :=
          rhtFinset_singleton_right y
        simpa [this] using hEnt y (Finset.mem_singleton_self y)
      exact (sumElementRht A B z y0 hy0).closed w y hw hEnty
    | left x =>
      have : lftFinset ({SumToken.left x} : Finset (SumToken α β)) = {x} :=
        lftFinset_singleton_left x
      exact False.elim (Finset.singleton_ne_empty x (this ▸ hl))
  · intro p hp
    cases p with
    | bot =>
      refine ⟨∅, fun _ h => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 h)), ?_⟩
      exact ⟨B.con_empty, (sumSystem A B).con_sing _, by rw [lftFinset_singleton_bot],
        B.entSet_empty _⟩
    | right y =>
      refine ⟨{y}, ?_, ?_⟩
      · intro b hb
        have : b = y := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
        subst this; exact hp
      · refine ⟨B.con_sing y, (sumSystem A B).con_sing _, ?_, ?_⟩
        · ext x; constructor
          · intro hx
            have : SumToken.left x ∈ ({SumToken.right y} : Finset _) := (mem_lftFinset).1 hx
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hx; exact False.elim (Finset.notMem_empty x hx)
        · rw [rhtFinset_singleton_right]
          exact proposition_2_3_iii B (B.con_sing y)
    | left x =>
      exact False.elim (not_mem_right_of_mem_left A B z hp hy0)

theorem eq_botElement_of_no_injections (z : (sumSystem A B).Element)
    (hL : ∀ x : α, SumToken.left x ∉ z.carrier)
    (hR : ∀ y : β, SumToken.right y ∉ z.carrier) :
    z = (sumSystem A B).botElement := by
  apply le_antisymm
  · intro p hp
    cases p with
    | bot =>
      change SumToken.bot ∈ (sumSystem A B).botElement.carrier
      exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
    | left x => exact False.elim (hL x hp)
    | right y => exact False.elim (hR y hp)
  · exact botElement_le (sumSystem A B) z

/-- Choice-free emptiness dichotomy for `lftFinset` (avoids `Finset.decidableEq`). -/
theorem lftFinset_eq_empty_or_mem (u : Finset (SumToken α β)) :
    lftFinset u = ∅ ∨ ∃ x, x ∈ lftFinset u := by
  induction u using Finset.induction_on with
  | empty =>
    exact Or.inl lftFinset_empty
  | insert p s _hp ih =>
    cases p with
    | left x =>
      exact Or.inr ⟨x, by rw [lftFinset_insert_left]; exact Finset.mem_insert_self _ _⟩
    | right y =>
      rw [lftFinset_insert_right]; exact ih
    | bot =>
      rw [lftFinset_insert_bot]; exact ih

/-- Choice-free emptiness dichotomy for `rhtFinset`. -/
theorem rhtFinset_eq_empty_or_mem (u : Finset (SumToken α β)) :
    rhtFinset u = ∅ ∨ ∃ y, y ∈ rhtFinset u := by
  induction u using Finset.induction_on with
  | empty =>
    exact Or.inl rhtFinset_empty
  | insert p s _hp ih =>
    cases p with
    | right y =>
      exact Or.inr ⟨y, by rw [rhtFinset_insert_right]; exact Finset.mem_insert_self _ _⟩
    | left x =>
      rw [rhtFinset_insert_left]; exact ih
    | bot =>
      rw [rhtFinset_insert_bot]; exact ih

theorem entSet_liftLft_of_left_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumLeft (β := β) (lftFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
    refine ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), ⟨?_, ?_⟩⟩
    · rw [lftFinset_liftSumLeft]; exact Finset.ne_empty_of_mem hx
    · rw [lftFinset_liftSumLeft]
      exact A.ent_refl (lft_mem_Con_of_SumCon_rht_empty A B hu hr) hx
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      rw [hr] at this
      exact Finset.notMem_empty _ this)

theorem entSet_liftRht_of_right_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumRight (α := α) (rhtFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
    refine ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), ⟨?_, ?_⟩⟩
    · rw [rhtFinset_liftSumRight]; exact Finset.ne_empty_of_mem hy
    · rw [rhtFinset_liftSumRight]
      exact B.ent_refl (rht_mem_Con_of_SumCon_lft_empty A B hu hl) hy
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp
      rw [hl] at this
      exact Finset.notMem_empty _ this)

theorem subset_botElement_of_projections_empty {u : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅) :
    (↑u : Set (SumToken α β)) ⊆ (sumSystem A B).botElement.carrier := by
  intro p hp
  have hp' : p ∈ u := Finset.mem_coe.1 hp
  cases p with
  | bot =>
    exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp'
      rw [hl] at this; exact Finset.notMem_empty _ this)
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp'
      rw [hr] at this; exact Finset.notMem_empty _ this)

theorem entSet_empty_of_rel_bot_like (h : ApproximableMap (sumSystem A B) C)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement)
    {u : Finset (SumToken α β)} {s : Finset γ}
    (hu : SumCon A B u) (hs : s ∈ C.Con) (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅)
    (hh : h.rel u s) : C.EntSet ∅ s := by
  have hsub := subset_botElement_of_projections_empty A B hl hr
  have hcl : (sumSystem A B).closure u hu ≤ (sumSystem A B).botElement := by
    intro p hp
    exact (sumSystem A B).botElement.closed u p hsub hp
  have hle : C.closure s hs ≤ C.botElement := by
    have := (h.rel_iff_closure_le hu hs).1 hh
    have := le_trans this (toElement_mono h hcl)
    rwa [hbot] at this
  intro Y hY
  have hY' : Y ∈ (C.closure s hs).carrier := C.subset_closure hs hY
  have hbotY : Y ∈ C.botElement.carrier := hle hY'
  exact C.ent_trans C.con_empty (C.con_sing C.bot)
    (fun _ hz => by
      have : _ = C.bot := Finset.mem_singleton.mp hz
      subst this; exact C.ent_bot C.con_empty)
    hbotY

theorem entSet_u_of_inl_witness {u u' : Finset (SumToken α β)} {v : Finset α}
    (hlne : lftFinset u ≠ ∅) (hinl : (inlMap A B).rel v u')
    (huv : A.EntSet (lftFinset u) v) (hu : SumCon A B u)
    (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet u u' := by
  intro p hp
  have ⟨hv, hu', hr', hEnt⟩ := hinl
  cases p with
  | bot => exact ⟨hu, trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u' := (mem_lftFinset).2 hp
    have hAx : A.Ent v x := hEnt x hx
    have hAx' : A.Ent (lftFinset u) x :=
      A.ent_trans (lft_mem_Con_of_SumCon_rht_empty A B hu hr) hv huv hAx
    exact ⟨hu, ⟨hlne, hAx'⟩⟩
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u' := (mem_rhtFinset).2 hp
      rw [hr'] at this; exact Finset.notMem_empty _ this)

theorem entSet_u_of_inr_witness {u u' : Finset (SumToken α β)} {w : Finset β}
    (hrne : rhtFinset u ≠ ∅) (hinr : (inrMap A B).rel w u')
    (huw : B.EntSet (rhtFinset u) w) (hu : SumCon A B u)
    (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet u u' := by
  intro p hp
  have ⟨hw, hu', hl', hEnt⟩ := hinr
  cases p with
  | bot => exact ⟨hu, trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u' := (mem_rhtFinset).2 hp
    have hBy : B.Ent w y := hEnt y hy
    have hBy' : B.Ent (rhtFinset u) y :=
      B.ent_trans (rht_mem_Con_of_SumCon_lft_empty A B hu hl) hw huw hBy
    exact ⟨hu, ⟨hrne, hBy'⟩⟩
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u' := (mem_lftFinset).2 hp
      rw [hl'] at this; exact Finset.notMem_empty _ this)

/-- Uniqueness of copairing (Scott Prop 6.4). -/
theorem copairMap_unique (f : ApproximableMap A C) (g : ApproximableMap B C)
    (h : ApproximableMap (sumSystem A B) C)
    (hinl : comp h (inlMap A B) = f) (hinr : comp h (inrMap A B) = g)
    (hbot : h.toElement (sumSystem A B).botElement = C.botElement) :
    h = copairMap A B f g := by
  refine ApproximableMap.ext fun u s => ?_
  constructor
  · intro hh
    have hu : SumCon A B u := h.rel_dom hh
    have hs : s ∈ C.Con := h.rel_cod hh
    refine ⟨hu, hs, ?_⟩
    rcases lftFinset_eq_empty_or_mem u with hl | ⟨x0, hx0⟩
    · rcases rhtFinset_eq_empty_or_mem u with hr | ⟨y0, hy0⟩
      · exact Or.inl (entSet_empty_of_rel_bot_like A B h hbot hu hs hl hr hh)
      · have hl' : lftFinset u = ∅ := hl
        have hg : g.rel (rhtFinset u) s := by
          have hinr' : (comp h (inrMap A B)).rel (rhtFinset u) s := by
            refine ⟨liftSumRight (α := α) (rhtFinset u), ?_, ?_⟩
            · exact ⟨rht_mem_Con_of_SumCon_lft_empty A B hu hl',
                SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl'),
                lftFinset_liftSumRight (α := α) _, by
                  rw [rhtFinset_liftSumRight]
                  exact proposition_2_3_iii B
                    (rht_mem_Con_of_SumCon_lft_empty A B hu hl')⟩
            · exact h.mono hh (entSet_liftRht_of_right_only A B hu hl')
                (proposition_2_3_iii C hs)
                (SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl')) hs
          simpa [hinr] using hinr'
        exact Or.inr (Or.inr ⟨Finset.ne_empty_of_mem hy0, hg⟩)
    · have hne : lftFinset u ≠ ∅ := Finset.ne_empty_of_mem hx0
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      have hf : f.rel (lftFinset u) s := by
        have hinl' : (comp h (inlMap A B)).rel (lftFinset u) s := by
          refine ⟨liftSumLeft (β := β) (lftFinset u), ?_, ?_⟩
          · exact ⟨lft_mem_Con_of_SumCon_rht_empty A B hu hr,
              SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr),
              rhtFinset_liftSumLeft (β := β) _, by
                rw [lftFinset_liftSumLeft]
                exact proposition_2_3_iii A
                  (lft_mem_Con_of_SumCon_rht_empty A B hu hr)⟩
          · exact h.mono hh (entSet_liftLft_of_left_only A B hu hr)
              (proposition_2_3_iii C hs)
              (SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr)) hs
        simpa [hinl] using hinl'
      exact Or.inr (Or.inl ⟨hne, hf⟩)
  · intro hc
    rcases hc with ⟨hu, hs, hcop⟩
    rcases hcop with hE | ⟨hne, hf⟩ | ⟨hne, hg⟩
    · have hb : h.rel ∅ s :=
        h.mono h.empty_rel ((sumSystem A B).entSet_empty _) hE
          (sumSystem A B).con_empty hs
      exact h.mono hb ((sumSystem A B).entSet_empty _) (proposition_2_3_iii C hs) hu hs
    · have : (comp h (inlMap A B)).rel (lftFinset u) s := by simpa [hinl] using hf
      rcases this with ⟨u', hinl', hh'⟩
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet_u_of_inl_witness A B hne hinl'
          (proposition_2_3_iii A (lft_mem_Con_of_SumCon_rht_empty A B hu hr)) hu hr
      exact h.mono hh' hEnt (proposition_2_3_iii C hs) hu hs
    · have : (comp h (inrMap A B)).rel (rhtFinset u) s := by simpa [hinr] using hg
      rcases this with ⟨u', hinr', hh'⟩
      have hl : lftFinset u = ∅ := SumCon_lft_empty_of_rht_nonempty A B hu hne
      have hEnt : (sumSystem A B).EntSet u u' :=
        entSet_u_of_inr_witness A B hne hinr'
          (proposition_2_3_iii B (rht_mem_Con_of_SumCon_lft_empty A B hu hl)) hu hl
      exact h.mono hh' hEnt (proposition_2_3_iii C hs) hu hs

end ApproximableMap

end InfoSys

end Scott1982
