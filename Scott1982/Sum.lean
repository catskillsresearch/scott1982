import Scott1982.Constructive
import Scott1982.Proposition23

/-!
# Separated sum of information systems — Definition 6.3

**Scott 1982, Definition 6.3.** Tokens of `A + B` are left copies `(X, Δ)`, right
copies `(Δ, Y)`, and a fresh bottom `(Δ, Δ)`. Consistency and entailment are
disjunctive: a consistent set lives entirely on the left or entirely on the right
(or is empty / `{⊥}`).

We encode tokens as an inductive type so that `(Δ_A, Δ)`, `(Δ, Δ_B)`, and `(Δ, Δ)`
remain pairwise distinct, matching Scott’s remark after Def 6.3.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Token type of the separated sum `A + B` (Scott 6.3(i)–(ii)).
`left X` is `(X, Δ)`, `right Y` is `(Δ, Y)`, and `bot` is `(Δ, Δ)`. -/
inductive SumToken (α β : Type*) where
  | left : α → SumToken α β
  | right : β → SumToken α β
  | bot : SumToken α β

instance : DecidableEq (SumToken α β)
  | .left a, .left b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.left.inj h')
  | .right a, .right b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.right.inj h')
  | .bot, .bot => isTrue rfl
  | .left _, .right _ => isFalse fun h => nomatch h
  | .left _, .bot => isFalse fun h => nomatch h
  | .right _, .left _ => isFalse fun h => nomatch h
  | .right _, .bot => isFalse fun h => nomatch h
  | .bot, .left _ => isFalse fun h => nomatch h
  | .bot, .right _ => isFalse fun h => nomatch h

variable (A : InfoSys α) (B : InfoSys β)

/-- Sum bottom `Δ_{A+B} = (Δ, Δ)`. -/
def sumBot : SumToken α β := .bot

private def lftInsert : SumToken α β → Finset α → Finset α
  | .left x => insert x
  | .right _ => id
  | .bot => id

private def rhtInsert : SumToken α β → Finset β → Finset β
  | .right y => insert y
  | .left _ => id
  | .bot => id

private instance instLeftCommutativeLftInsert :
    LeftCommutative (lftInsert : SumToken α β → Finset α → Finset α) :=
  ⟨fun p q s => by
    cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance instLeftCommutativeRhtInsert :
    LeftCommutative (rhtInsert : SumToken α β → Finset β → Finset β) :=
  ⟨fun p q s => by
    cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

/-- Left projection `lft u` (Scott 6.3). -/
def lftFinset (u : Finset (SumToken α β)) : Finset α :=
  Multiset.foldr lftInsert (∅ : Finset α) u.1

/-- Right projection `rht u` (Scott 6.3). -/
def rhtFinset (u : Finset (SumToken α β)) : Finset β :=
  Multiset.foldr rhtInsert (∅ : Finset β) u.1

private theorem mem_foldr_lft (s : Multiset (SumToken α β)) (x : α) :
    x ∈ Multiset.foldr lftInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .left x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | left a =>
      simp only [Multiset.foldr_cons, lftInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hx | ⟨q, hq, hq'⟩)
        · exact ⟨.left a, Or.inl rfl, congrArg SumToken.left hx.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hx
          exact Or.inl hx.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | right b =>
      simp only [Multiset.foldr_cons, lftInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩
    | bot =>
      simp only [Multiset.foldr_cons, lftInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

private theorem mem_foldr_rht (s : Multiset (SumToken α β)) (y : β) :
    y ∈ Multiset.foldr rhtInsert (∅ : Finset β) s ↔ ∃ p ∈ s, p = .right y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | right b =>
      simp only [Multiset.foldr_cons, rhtInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hy | ⟨q, hq, hq'⟩)
        · exact ⟨.right b, Or.inl rfl, congrArg SumToken.right hy.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hy
          exact Or.inl hy.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | left a =>
      simp only [Multiset.foldr_cons, rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩
    | bot =>
      simp only [Multiset.foldr_cons, rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_lftFinset {u : Finset (SumToken α β)} {x : α} :
    x ∈ lftFinset u ↔ SumToken.left x ∈ u := by
  unfold lftFinset
  rw [mem_foldr_lft]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hx
    exact ⟨.left x, hx, rfl⟩

theorem mem_rhtFinset {u : Finset (SumToken α β)} {y : β} :
    y ∈ rhtFinset u ↔ SumToken.right y ∈ u := by
  unfold rhtFinset
  rw [mem_foldr_rht]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hy
    exact ⟨.right y, hy, rfl⟩

theorem lftFinset_empty : lftFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (Finset.notMem_empty _ ((mem_lftFinset).1 hx))
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem rhtFinset_empty : rhtFinset (∅ : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim (Finset.notMem_empty _ ((mem_rhtFinset).1 hy))
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem lftFinset_mono {u v : Finset (SumToken α β)} (h : v ⊆ u) :
    lftFinset v ⊆ lftFinset u := by
  intro x hx
  exact (mem_lftFinset).2 (h ((mem_lftFinset).1 hx))

theorem rhtFinset_mono {u v : Finset (SumToken α β)} (h : v ⊆ u) :
    rhtFinset v ⊆ rhtFinset u := by
  intro y hy
  exact (mem_rhtFinset).2 (h ((mem_rhtFinset).1 hy))

theorem lftFinset_insert_left (u : Finset (SumToken α β)) (x : α) :
    lftFinset (insert (.left x) u) = insert x (lftFinset u) := by
  ext y
  constructor
  · intro hy
    have : SumToken.left y ∈ insert (.left x) u := (mem_lftFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hy'
      exact Finset.mem_insert.mpr (Or.inl hy')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).2 h))
  · intro hy
    rcases Finset.mem_insert.mp hy with hy' | hy'
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.left hy')))
    · exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hy')))

theorem lftFinset_insert_right (u : Finset (SumToken α β)) (y : β) :
    lftFinset (insert (.right y) u) = lftFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ insert (.right y) u := (mem_lftFinset).1 hx
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_lftFinset).2 h
  · intro hx
    exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hx)))

theorem lftFinset_insert_bot (u : Finset (SumToken α β)) :
    lftFinset (insert (.bot : SumToken α β) u) = lftFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ insert .bot u := (mem_lftFinset).1 hx
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_lftFinset).2 h
  · intro hx
    exact (mem_lftFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_lftFinset).1 hx)))

theorem rhtFinset_insert_right (u : Finset (SumToken α β)) (y : β) :
    rhtFinset (insert (.right y) u) = insert y (rhtFinset u) := by
  ext z
  constructor
  · intro hz
    have : SumToken.right z ∈ insert (.right y) u := (mem_rhtFinset).1 hz
    rcases Finset.mem_insert.mp this with h | h
    · injection h with hz'
      exact Finset.mem_insert.mpr (Or.inl hz')
    · exact Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).2 h))
  · intro hz
    rcases Finset.mem_insert.mp hz with hz' | hz'
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inl (congrArg SumToken.right hz')))
    · exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hz')))

theorem rhtFinset_insert_left (u : Finset (SumToken α β)) (x : α) :
    rhtFinset (insert (.left x) u) = rhtFinset u := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ insert (.left x) u := (mem_rhtFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_rhtFinset).2 h
  · intro hy
    exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hy)))

theorem rhtFinset_insert_bot (u : Finset (SumToken α β)) :
    rhtFinset (insert (.bot : SumToken α β) u) = rhtFinset u := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ insert .bot u := (mem_rhtFinset).1 hy
    rcases Finset.mem_insert.mp this with h | h
    · exact False.elim (nomatch h)
    · exact (mem_rhtFinset).2 h
  · intro hy
    exact (mem_rhtFinset).2 (Finset.mem_insert.mpr (Or.inr ((mem_rhtFinset).1 hy)))

theorem lftFinset_singleton_left (x : α) :
    lftFinset ({.left x} : Finset (SumToken α β)) = {x} := by
  ext y
  simp only [mem_lftFinset, Finset.mem_singleton]
  exact ⟨SumToken.left.inj, fun h => h ▸ rfl⟩

theorem rhtFinset_singleton_right (y : β) :
    rhtFinset ({.right y} : Finset (SumToken α β)) = {y} := by
  ext z
  simp only [mem_rhtFinset, Finset.mem_singleton]
  exact ⟨SumToken.right.inj, fun h => h ▸ rfl⟩

theorem lftFinset_singleton_bot :
    lftFinset ({.bot} : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ ({.bot} : Finset _) := (mem_lftFinset).1 hx
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem rhtFinset_singleton_bot :
    rhtFinset ({.bot} : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ ({.bot} : Finset _) := (mem_rhtFinset).1 hy
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

/-- Consistency for the separated sum (Scott 6.3(iii)). -/
def SumCon (u : Finset (SumToken α β)) : Prop :=
  (lftFinset u ∈ A.Con ∧ rhtFinset u = ∅) ∨
    (lftFinset u = ∅ ∧ rhtFinset u ∈ B.Con)

/-- Entailment for the separated sum (Scott 6.3(iv')–(iv''')).
Includes `SumCon` so `ent_con` can update projections. -/
def SumEnt (u : Finset (SumToken α β)) (p : SumToken α β) : Prop :=
  SumCon A B u ∧
    match p with
    | .bot => True
    | .left x => lftFinset u ≠ ∅ ∧ A.Ent (lftFinset u) x
    | .right y => rhtFinset u ≠ ∅ ∧ B.Ent (rhtFinset u) y

theorem SumCon_empty : SumCon A B (∅ : Finset (SumToken α β)) :=
  Or.inl ⟨by rw [lftFinset_empty]; exact A.con_empty, by rw [rhtFinset_empty]⟩

theorem SumCon_rht_empty_of_lft_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : lftFinset u ≠ ∅) : rhtFinset u = ∅ := by
  rcases hu with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact hr
  · exact False.elim (hne hl)

theorem SumCon_lft_empty_of_rht_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : rhtFinset u ≠ ∅) : lftFinset u = ∅ := by
  rcases hu with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact False.elim (hne hr)
  · exact hl

theorem SumCon_lft_con_of_lft_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : lftFinset u ≠ ∅) : lftFinset u ∈ A.Con := by
  rcases hu with ⟨hl, _⟩ | ⟨hl, _⟩
  · exact hl
  · exact False.elim (hne hl)

theorem SumCon_rht_con_of_rht_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : rhtFinset u ≠ ∅) : rhtFinset u ∈ B.Con := by
  rcases hu with ⟨_, hr⟩ | ⟨_, hr⟩
  · exact False.elim (hne hr)
  · exact hr

/-- **Definition 6.3.** The separated sum information system `A + B`. -/
def sumSystem : InfoSys (SumToken α β) where
  bot := sumBot
  Con := {u | SumCon A B u}
  Ent := SumEnt A B
  con_subset := by
    intro u v hu hv
    rcases hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Or.inl ⟨A.con_subset hl (lftFinset_mono hv),
        Finset.Subset.antisymm (by
          intro y hy
          have : y ∈ rhtFinset u := rhtFinset_mono hv hy
          rw [hr] at this
          exact False.elim (Finset.notMem_empty y this))
          (Finset.empty_subset _)⟩
    · exact Or.inr ⟨Finset.Subset.antisymm (by
          intro x hx
          have : x ∈ lftFinset u := lftFinset_mono hv hx
          rw [hl] at this
          exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _),
        B.con_subset hr (rhtFinset_mono hv)⟩
  con_sing := by
    intro p
    cases p with
    | left x =>
      exact Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing x,
        by
          ext y
          constructor
          · intro hy
            have : SumToken.right y ∈ ({.left x} : Finset _) := (mem_rhtFinset).1 hy
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hy
            exact False.elim (Finset.notMem_empty y hy)⟩
    | right y =>
      exact Or.inr ⟨by
          ext x
          constructor
          · intro hx
            have : SumToken.left x ∈ ({.right y} : Finset _) := (mem_lftFinset).1 hx
            exact False.elim (nomatch Finset.mem_singleton.mp this)
          · intro hx
            exact False.elim (Finset.notMem_empty x hx),
        by rw [rhtFinset_singleton_right]; exact B.con_sing y⟩
    | bot =>
      exact Or.inl ⟨by rw [lftFinset_singleton_bot]; exact A.con_empty,
        rhtFinset_singleton_bot⟩
  ent_con := by
    intro u p ⟨hu, hEnt⟩
    cases p with
    | bot =>
      rcases hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact Or.inl ⟨by rw [lftFinset_insert_bot]; exact hl,
          by rw [rhtFinset_insert_bot]; exact hr⟩
      · exact Or.inr ⟨by rw [lftFinset_insert_bot]; exact hl,
          by rw [rhtFinset_insert_bot]; exact hr⟩
    | left x =>
      rcases hEnt with ⟨hne, hA⟩
      have hr : rhtFinset u = ∅ := SumCon_rht_empty_of_lft_nonempty A B hu hne
      exact Or.inl ⟨by
          rw [lftFinset_insert_left]
          exact A.ent_con hA,
        by rw [rhtFinset_insert_left]; exact hr⟩
    | right y =>
      rcases hEnt with ⟨hne, hB⟩
      have hl : lftFinset u = ∅ := SumCon_lft_empty_of_rht_nonempty A B hu hne
      exact Or.inr ⟨by rw [lftFinset_insert_right]; exact hl,
        by
          rw [rhtFinset_insert_right]
          exact B.ent_con hB⟩
  ent_bot := by
    intro u hu
    exact ⟨hu, trivial⟩
  ent_refl := by
    intro u p hu hp
    refine ⟨hu, ?_⟩
    cases p with
    | bot => exact trivial
    | left x =>
      have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
      have hne : lftFinset u ≠ ∅ := Finset.ne_empty_of_mem hx
      exact ⟨hne, A.ent_refl (SumCon_lft_con_of_lft_nonempty A B hu hne) hx⟩
    | right y =>
      have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      have hne : rhtFinset u ≠ ∅ := Finset.ne_empty_of_mem hy
      exact ⟨hne, B.ent_refl (SumCon_rht_con_of_rht_nonempty A B hu hne) hy⟩
  ent_trans := by
    intro u v c hv hu hEnts hEntc
    refine ⟨hv, ?_⟩
    cases c with
    | bot => exact trivial
    | left x =>
      rcases hEntc with ⟨_, ⟨hne, hA⟩⟩
      have hlft : ∀ y ∈ lftFinset u, A.Ent (lftFinset v) y := by
        intro y hy
        have hp : SumToken.left y ∈ u := (mem_lftFinset).1 hy
        have hEy : SumEnt A B v (.left y) := hEnts _ hp
        exact hEy.2.2
      have hne' : lftFinset v ≠ ∅ := by
        obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
        have hp : SumToken.left y ∈ u := (mem_lftFinset).1 hy
        exact (hEnts _ hp).2.1
      refine ⟨hne', ?_⟩
      exact A.ent_trans (SumCon_lft_con_of_lft_nonempty A B hv hne')
        (SumCon_lft_con_of_lft_nonempty A B hu hne) hlft hA
    | right y =>
      rcases hEntc with ⟨_, ⟨hne, hB⟩⟩
      have hrht : ∀ z ∈ rhtFinset u, B.Ent (rhtFinset v) z := by
        intro z hz
        have hp : SumToken.right z ∈ u := (mem_rhtFinset).1 hz
        have hEz : SumEnt A B v (.right z) := hEnts _ hp
        exact hEz.2.2
      have hne' : rhtFinset v ≠ ∅ := by
        obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
        have hp : SumToken.right z ∈ u := (mem_rhtFinset).1 hz
        exact (hEnts _ hp).2.1
      refine ⟨hne', ?_⟩
      exact B.ent_trans (SumCon_rht_con_of_rht_nonempty A B hv hne')
        (SumCon_rht_con_of_rht_nonempty A B hu hne) hrht hB

end InfoSys

end Scott1982
