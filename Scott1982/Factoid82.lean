import Scott1982.FunctionSpace
import Scott1982.Sum

/-!
# Factoid 8.2 — λ-calculus model `D ≅ A + (D → D)` (Partial)

**Scott 1982, §8.** `D` and `Con_D` are mutually recursive. Lean rejects putting the
FunCon-style clause (7) inside an inductive (negative occurrence), so we **stage**
consistency: `LamConN n` at stage `0` is atom/bot only; stage `n+1` may add function
tokens whose components and FunCon checks live at stage `n`. Then
`LamCon u := ∃ n, LamConN n u`. Entailment is staged the same way as `LamEntN`
(Scott (8)–(11)).

**Status:** Depth-based `LamConDepth` / `LamEntDepth` (wf; choice-free) is the
primary path for Def 2.1. Staged `LamConN` retained as scaffolding. Remaining:
finish depth `ent_con`/`ent_trans`, `lambdaSystem`, unfold into
`sumSystem A (functionSystem D D)`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

/-! ## Raw tokens + decidable equality -/

inductive RawLamToken (α : Type*) where
  | bot : RawLamToken α
  | atom : α → RawLamToken α
  | funTok : List (RawLamToken α) → List (RawLamToken α) → RawLamToken α

def listToFinset {β : Type*} [DecidableEq β] : List β → Finset β
  | [] => ∅
  | x :: xs => insert x (listToFinset xs)

theorem mem_listToFinset {β : Type*} [DecidableEq β] {x : β} {xs : List β} :
    x ∈ listToFinset xs ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; exact False.elim (Finset.notMem_empty x h)
    · intro h; cases h
  | cons a as ih =>
    simp only [listToFinset, Finset.mem_insert, List.mem_cons, ih]

mutual
  def rawLamBEq : RawLamToken α → RawLamToken α → Bool
    | .bot, .bot => true
    | .atom x, .atom y => decide (x = y)
    | .funTok u v, .funTok u' v' => rawLamListBEq u u' && rawLamListBEq v v'
    | _, _ => false
  def rawLamListBEq : List (RawLamToken α) → List (RawLamToken α) → Bool
    | [], [] => true
    | x :: xs, y :: ys => rawLamBEq x y && rawLamListBEq xs ys
    | _, _ => false
end

mutual
  theorem rawLamBEq_eq : ∀ a b : RawLamToken α, rawLamBEq a b = true ↔ a = b
  | .bot, .bot => by simp [rawLamBEq]
  | .atom x, .atom y => by
      simp only [rawLamBEq, decide_eq_true_eq]
      exact ⟨congrArg RawLamToken.atom, RawLamToken.atom.inj⟩
  | .funTok u v, .funTok u' v' => by
      simp only [rawLamBEq, Bool.and_eq_true]
      constructor
      · intro ⟨hu, hv⟩
        rw [(rawLamListBEq_eq u u').1 hu, (rawLamListBEq_eq v v').1 hv]
      · intro h
        injection h with hu hv
        subst hu; subst hv
        exact ⟨(rawLamListBEq_eq u u).2 rfl, (rawLamListBEq_eq v v).2 rfl⟩
  | .bot, .atom _ | .bot, .funTok _ _ | .atom _, .bot | .atom _, .funTok _ _
  | .funTok _ _, .bot | .funTok _ _, .atom _ => by
      constructor
      · intro h; simp [rawLamBEq] at h
      · intro h; cases h
  theorem rawLamListBEq_eq : ∀ u v : List (RawLamToken α), rawLamListBEq u v = true ↔ u = v
  | [], [] => by simp [rawLamListBEq]
  | x :: xs, y :: ys => by
      simp only [rawLamListBEq, Bool.and_eq_true]
      constructor
      · intro ⟨hx, hxs⟩
        rw [(rawLamBEq_eq x y).1 hx, (rawLamListBEq_eq xs ys).1 hxs]
      · intro h
        injection h with hx hxs
        subst hx; subst hxs
        exact ⟨(rawLamBEq_eq x x).2 rfl, (rawLamListBEq_eq xs xs).2 rfl⟩
  | [], _ :: _ | _ :: _, [] => by
      constructor
      · intro h; simp [rawLamListBEq] at h
      · intro h; cases h
end

instance : DecidableEq (RawLamToken α) := fun a b =>
  if h : rawLamBEq a b = true then isTrue ((rawLamBEq_eq a b).1 h)
  else isFalse fun hab => h ((rawLamBEq_eq a b).2 hab)

/-! ## Projections -/

private def lamAtomInsert : RawLamToken α → Finset α → Finset α
  | .atom x => insert x
  | .bot | .funTok _ _ => id

private def lamFunInsert :
    RawLamToken α → Finset (List (RawLamToken α) × List (RawLamToken α)) →
      Finset (List (RawLamToken α) × List (RawLamToken α))
  | .funTok u v => insert (u, v)
  | .bot | .atom _ => id

private instance : LeftCommutative (lamAtomInsert : RawLamToken α → Finset α → Finset α) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance : LeftCommutative
    (lamFunInsert : RawLamToken α →
      Finset (List (RawLamToken α) × List (RawLamToken α)) →
        Finset (List (RawLamToken α) × List (RawLamToken α))) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def lamAtomFinset (u : Finset (RawLamToken α)) : Finset α :=
  Multiset.foldr lamAtomInsert ∅ u.1

def lamFunFinset (u : Finset (RawLamToken α)) :
    Finset (List (RawLamToken α) × List (RawLamToken α)) :=
  Multiset.foldr lamFunInsert ∅ u.1

theorem mem_lamAtomFinset {u : Finset (RawLamToken α)} {x : α} :
    x ∈ lamAtomFinset u ↔ .atom x ∈ u := by
  have aux (s : Multiset (RawLamToken α)) :
      x ∈ Multiset.foldr lamAtomInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .atom x := by
    refine Multiset.induction_on s ?_ ?_
    · constructor
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p t ih
      cases p with
      | atom a =>
        simp only [Multiset.foldr_cons, lamAtomInsert, Finset.mem_insert, ih, Multiset.mem_cons]
        constructor
        · rintro (hx | ⟨q, hq, hq'⟩)
          · exact ⟨.atom a, Or.inl rfl, congrArg RawLamToken.atom hx.symm⟩
          · exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · injection hq' with hx; exact Or.inl hx.symm
          · exact Or.inr ⟨q, hq, hq'⟩
      | bot | funTok _ _ =>
        simp only [Multiset.foldr_cons, lamAtomInsert, id_eq, ih, Multiset.mem_cons]
        constructor
        · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · exact False.elim (nomatch hq')
          · exact ⟨q, hq, hq'⟩
  constructor
  · intro hx
    rcases (aux u.1).1 hx with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro hx
    exact (aux u.1).2 ⟨.atom x, Finset.mem_def.1 hx, rfl⟩

theorem mem_lamFunFinset {u : Finset (RawLamToken α)}
    {p : List (RawLamToken α) × List (RawLamToken α)} :
    p ∈ lamFunFinset u ↔ .funTok p.1 p.2 ∈ u := by
  have aux (s : Multiset (RawLamToken α)) :
      p ∈ Multiset.foldr lamFunInsert ∅ s ↔ ∃ t ∈ s, t = .funTok p.1 p.2 := by
    refine Multiset.induction_on s ?_ ?_
    · constructor
      · intro hp; exact False.elim (Finset.notMem_empty p hp)
      · rintro ⟨_, ht, _⟩; exact False.elim (by cases ht)
    · intro t rest ih
      cases t with
      | funTok u v =>
        simp only [Multiset.foldr_cons, lamFunInsert, Finset.mem_insert, ih, Multiset.mem_cons]
        constructor
        · rintro (hp | ⟨q, hq, hq'⟩)
          · exact ⟨.funTok u v, Or.inl rfl, by cases hp; rfl⟩
          · exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · injection hq' with hu hv
            exact Or.inl (Prod.ext hu.symm hv.symm)
          · exact Or.inr ⟨q, hq, hq'⟩
      | bot | atom _ =>
        simp only [Multiset.foldr_cons, lamFunInsert, id_eq, ih, Multiset.mem_cons]
        constructor
        · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · exact False.elim (nomatch hq')
          · exact ⟨q, hq, hq'⟩
  constructor
  · intro hp
    rcases (aux u.1).1 hp with ⟨t, ht, ht'⟩
    subst ht'; exact Finset.mem_def.2 ht
  · intro hp
    exact (aux u.1).2 ⟨.funTok p.1 p.2, Finset.mem_def.1 hp, rfl⟩

theorem lamAtomFinset_empty : lamAtomFinset (∅ : Finset (RawLamToken α)) = ∅ := rfl
theorem lamFunFinset_empty : lamFunFinset (∅ : Finset (RawLamToken α)) = ∅ := rfl

theorem lamAtomFinset_mono {u v : Finset (RawLamToken α)} (h : v ⊆ u) :
    lamAtomFinset v ⊆ lamAtomFinset u :=
  fun _ hx => mem_lamAtomFinset.2 (h (mem_lamAtomFinset.1 hx))

theorem lamFunFinset_mono {u v : Finset (RawLamToken α)} (h : v ⊆ u) :
    lamFunFinset v ⊆ lamFunFinset u :=
  fun _ hp => mem_lamFunFinset.2 (h (mem_lamFunFinset.1 hp))

theorem lamAtomFinset_insert_bot (u : Finset (RawLamToken α)) :
    lamAtomFinset (insert (.bot : RawLamToken α) u) = lamAtomFinset u := by
  ext x; simp only [mem_lamAtomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamAtomFinset_insert_atom (u : Finset (RawLamToken α)) (x : α) :
    lamAtomFinset (insert (.atom x) u) = insert x (lamAtomFinset u) := by
  ext y; simp only [Finset.mem_insert, mem_lamAtomFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (RawLamToken.atom.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem lamAtomFinset_insert_funTok (u : Finset (RawLamToken α))
    (xs ys : List (RawLamToken α)) :
    lamAtomFinset (insert (.funTok xs ys) u) = lamAtomFinset u := by
  ext x; simp only [mem_lamAtomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamFunFinset_insert_bot (u : Finset (RawLamToken α)) :
    lamFunFinset (insert (.bot : RawLamToken α) u) = lamFunFinset u := by
  ext p; simp only [mem_lamFunFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamFunFinset_insert_atom (u : Finset (RawLamToken α)) (x : α) :
    lamFunFinset (insert (.atom x) u) = lamFunFinset u := by
  ext p; simp only [mem_lamFunFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem lamFunFinset_insert_funTok (u : Finset (RawLamToken α))
    (xs ys : List (RawLamToken α)) :
    lamFunFinset (insert (.funTok xs ys) u) = insert (xs, ys) (lamFunFinset u) := by
  ext p; simp only [Finset.mem_insert, mem_lamFunFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (Prod.ext (RawLamToken.funTok.inj h).1 (RawLamToken.funTok.inj h).2)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

private def lamInUnionInsert [DecidableEq (RawLamToken α)] :
    List (RawLamToken α) × List (RawLamToken α) → Finset (RawLamToken α) →
      Finset (RawLamToken α)
  | p, acc => listToFinset p.1 ∪' acc

private def lamOutUnionInsert [DecidableEq (RawLamToken α)] :
    List (RawLamToken α) × List (RawLamToken α) → Finset (RawLamToken α) →
      Finset (RawLamToken α)
  | p, acc => listToFinset p.2 ∪' acc

private instance [DecidableEq (RawLamToken α)] :
    LeftCommutative (lamInUnionInsert (α := α)) :=
  ⟨fun p q s => by
    simp only [lamInUnionInsert]
    ext x; simp only [mem_funion]
    constructor <;> · rintro (h | h | h); exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]⟩

private instance [DecidableEq (RawLamToken α)] :
    LeftCommutative (lamOutUnionInsert (α := α)) :=
  ⟨fun p q s => by
    simp only [lamOutUnionInsert]
    ext x; simp only [mem_funion]
    constructor <;> · rintro (h | h | h); exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]⟩

def lamInputUnion (s : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    Finset (RawLamToken α) :=
  Multiset.foldr (lamInUnionInsert (α := α)) ∅ s.1

def lamOutputUnion (s : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    Finset (RawLamToken α) :=
  Multiset.foldr (lamOutUnionInsert (α := α)) ∅ s.1

theorem lamInputUnion_empty :
    lamInputUnion (∅ : Finset (List (RawLamToken α) × List (RawLamToken α))) = ∅ := by
  rfl

theorem lamOutputUnion_empty :
    lamOutputUnion (∅ : Finset (List (RawLamToken α) × List (RawLamToken α))) = ∅ := by
  rfl

theorem mem_lamInputUnion {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    {t : RawLamToken α} :
    t ∈ lamInputUnion s ↔ ∃ p ∈ s, t ∈ listToFinset p.1 := by
  have aux (m : Multiset (List (RawLamToken α) × List (RawLamToken α))) :
      t ∈ Multiset.foldr (lamInUnionInsert (α := α)) ∅ m ↔
        ∃ p ∈ m, t ∈ listToFinset p.1 := by
    refine Multiset.induction_on m ?_ ?_
    · constructor
      · intro ht; exact False.elim (Finset.notMem_empty t ht)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p rest ih
      simp only [Multiset.foldr_cons, lamInUnionInsert, mem_funion, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, ht⟩)
        · exact ⟨p, Or.inl rfl, ht⟩
        · exact ⟨q, Or.inr hq, ht⟩
      · rintro ⟨q, hq, ht⟩
        rcases hq with rfl | hq
        · exact Or.inl ht
        · exact Or.inr ⟨q, hq, ht⟩
  simpa [lamInputUnion] using aux s.1

theorem mem_lamOutputUnion {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    {t : RawLamToken α} :
    t ∈ lamOutputUnion s ↔ ∃ p ∈ s, t ∈ listToFinset p.2 := by
  have aux (m : Multiset (List (RawLamToken α) × List (RawLamToken α))) :
      t ∈ Multiset.foldr (lamOutUnionInsert (α := α)) ∅ m ↔
        ∃ p ∈ m, t ∈ listToFinset p.2 := by
    refine Multiset.induction_on m ?_ ?_
    · constructor
      · intro ht; exact False.elim (Finset.notMem_empty t ht)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p rest ih
      simp only [Multiset.foldr_cons, lamOutUnionInsert, mem_funion, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, ht⟩)
        · exact ⟨p, Or.inl rfl, ht⟩
        · exact ⟨q, Or.inr hq, ht⟩
      · rintro ⟨q, hq, ht⟩
        rcases hq with rfl | hq
        · exact Or.inl ht
        · exact Or.inr ⟨q, hq, ht⟩
  simpa [lamOutputUnion] using aux s.1

/-! ## Staged consistency -/

variable (A : InfoSys α)

/-- Stage-`n` consistency (Scott (4)–(7), stratified). -/
def LamConN : ℕ → Finset (RawLamToken α) → Prop
  | 0, u => lamAtomFinset u ∈ A.Con ∧ lamFunFinset u = ∅
  | n + 1, u =>
      LamConN n u ∨
        (lamAtomFinset u = ∅ ∧
          (∀ p ∈ lamFunFinset u,
            LamConN n (listToFinset p.1) ∧ LamConN n (listToFinset p.2)) ∧
            ∀ s ⊆ lamFunFinset u,
              LamConN n (lamInputUnion s) → LamConN n (lamOutputUnion s))

def LamCon (u : Finset (RawLamToken α)) : Prop :=
  ∃ n, LamConN A n u

theorem LamConN_mono {n m : ℕ} (hmn : n ≤ m) {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) : LamConN A m u := by
  induction hmn with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem LamCon_empty : LamCon A (∅ : Finset (RawLamToken α)) :=
  ⟨0, by
    change lamAtomFinset ∅ ∈ A.Con ∧ lamFunFinset ∅ = ∅
    rw [lamAtomFinset_empty, lamFunFinset_empty]
    exact ⟨A.con_empty, rfl⟩⟩

theorem LamCon_singleton_bot : LamCon A ({.bot} : Finset (RawLamToken α)) := by
  refine ⟨0, ?_⟩
  change lamAtomFinset _ ∈ A.Con ∧ lamFunFinset _ = ∅
  constructor
  · have h : lamAtomFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
      ext x
      constructor
      · intro hx; exact False.elim (nomatch mem_lamAtomFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    rw [h]; exact A.con_empty
  · ext p
    constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)

theorem LamCon_singleton_atom (x : α) :
    LamCon A ({.atom x} : Finset (RawLamToken α)) := by
  refine ⟨0, ?_⟩
  change lamAtomFinset _ ∈ A.Con ∧ lamFunFinset _ = ∅
  constructor
  · have h : lamAtomFinset ({.atom x} : Finset (RawLamToken α)) = {x} := by
      ext y
      simp only [mem_lamAtomFinset, Finset.mem_singleton]
      exact ⟨RawLamToken.atom.inj, congrArg RawLamToken.atom⟩
    rw [h]; exact A.con_sing x
  · ext p
    constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)

theorem LamCon_subset {u : Finset (RawLamToken α)} (hu : LamCon A u) :
    ∀ {v}, v ⊆ u → LamCon A v := by
  rcases hu with ⟨n, hu⟩
  induction n generalizing u with
  | zero =>
    intro v hv
    refine ⟨0, ?_⟩
    change lamAtomFinset v ∈ A.Con ∧ lamFunFinset v = ∅
    rcases (hu : lamAtomFinset u ∈ A.Con ∧ lamFunFinset u = ∅) with ⟨hA, hF⟩
    exact ⟨A.con_subset hA (lamAtomFinset_mono hv),
      Finset.Subset.antisymm
        (fun p hp => by
          have : p ∈ lamFunFinset u := lamFunFinset_mono hv hp
          rw [hF] at this; exact False.elim (Finset.notMem_empty p this))
        (Finset.empty_subset _)⟩
  | succ n ih =>
    intro v hv
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · exact ih hu hv
    · refine ⟨n + 1, Or.inr ⟨?_, ?_, ?_⟩⟩
      · exact Finset.Subset.antisymm
          (fun x hx => by
            have : x ∈ lamAtomFinset u := lamAtomFinset_mono hv hx
            rw [hA] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      · intro p hp; exact hWF p (lamFunFinset_mono hv hp)
      · intro s hs hIn
        exact hFun s (fun p hp => lamFunFinset_mono hv (hs hp)) hIn

/-- Well-formed tokens (Scott (1)–(3)). -/
def IsLamToken : RawLamToken α → Prop
  | .bot | .atom _ => True
  | .funTok u v => LamCon A (listToFinset u) ∧ LamCon A (listToFinset v)

def LamToken : Type _ := { t : RawLamToken α // IsLamToken A t }

instance : DecidableEq (LamToken A) := Subtype.instDecidableEq

def lamBot : LamToken A := ⟨.bot, trivial⟩

def lamForget (t : LamToken A) : RawLamToken α := t.val

private def lamForgetInsert :
    LamToken A → Finset (RawLamToken α) → Finset (RawLamToken α) :=
  fun t => insert (lamForget A t)

private instance : LeftCommutative (lamForgetInsert (A := A)) :=
  ⟨fun p q s => insert_comm' (lamForget A p) (lamForget A q) s⟩

def lamForgetFinset (u : Finset (LamToken A)) : Finset (RawLamToken α) :=
  Multiset.foldr (lamForgetInsert (A := A)) ∅ u.1

private theorem mem_foldr_lamForget (s : Multiset (LamToken A)) (t : RawLamToken α) :
    t ∈ Multiset.foldr (lamForgetInsert (A := A)) ∅ s ↔ ∃ p ∈ s, p.val = t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    simp only [Multiset.foldr_cons, lamForgetInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (rfl | ⟨q, hq, hq'⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem mem_lamForgetFinset {u : Finset (LamToken A)} {t : RawLamToken α} :
    t ∈ lamForgetFinset A u ↔ ∃ p ∈ u, p.val = t := by
  simpa [lamForgetFinset] using mem_foldr_lamForget A u.1 t

theorem lamForgetFinset_empty : lamForgetFinset A (∅ : Finset (LamToken A)) = ∅ :=
  rfl

theorem lamForgetFinset_singleton (p : LamToken A) :
    lamForgetFinset A {p} = {p.val} := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, hq'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this; exact Finset.mem_singleton.mpr hq'.symm
  · intro ht
    exact (mem_lamForgetFinset A).2
      ⟨p, Finset.mem_singleton_self p, (Finset.mem_singleton.mp ht).symm⟩

theorem lamAtomFinset_singleton_funTok (u v : List (RawLamToken α)) :
    lamAtomFinset ({.funTok u v} : Finset (RawLamToken α)) = ∅ := by
  ext x
  constructor
  · intro hx; exact False.elim (nomatch mem_lamAtomFinset.1 hx)
  · intro hx; exact False.elim (Finset.notMem_empty x hx)

theorem lamFunFinset_singleton_funTok (u v : List (RawLamToken α)) :
    lamFunFinset ({.funTok u v} : Finset (RawLamToken α)) = {(u, v)} := by
  ext p
  simp only [mem_lamFunFinset, Finset.mem_singleton]
  constructor
  · intro h
    exact Prod.ext (RawLamToken.funTok.inj h).1 (RawLamToken.funTok.inj h).2
  · intro h
    cases h
    rfl

theorem lamInputUnion_singleton (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamInputUnion ({p} : Finset (List (RawLamToken α) × List (RawLamToken α))) =
      listToFinset p.1 := by
  ext t
  change t ∈ listToFinset p.1 ∪' ∅ ↔ t ∈ listToFinset p.1
  simp only [mem_funion, Finset.notMem_empty, or_false]

theorem lamOutputUnion_singleton (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamOutputUnion ({p} : Finset (List (RawLamToken α) × List (RawLamToken α))) =
      listToFinset p.2 := by
  ext t
  change t ∈ listToFinset p.2 ∪' ∅ ↔ t ∈ listToFinset p.2
  simp only [mem_funion, Finset.notMem_empty, or_false]

theorem LamConN_empty (n : ℕ) : LamConN A n (∅ : Finset (RawLamToken α)) := by
  induction n with
  | zero =>
    change lamAtomFinset ∅ ∈ A.Con ∧ lamFunFinset ∅ = ∅
    rw [lamAtomFinset_empty, lamFunFinset_empty]
    exact ⟨A.con_empty, rfl⟩
  | succ n ih => exact Or.inl ih

theorem LamCon_singleton_funTok (u v : List (RawLamToken α))
    (hu : LamCon A (listToFinset u)) (hv : LamCon A (listToFinset v)) :
    LamCon A ({.funTok u v} : Finset (RawLamToken α)) := by
  rcases hu with ⟨n, hu⟩
  rcases hv with ⟨m, hv⟩
  let k := max n m
  refine ⟨k + 1, Or.inr ⟨?_, ?_, ?_⟩⟩
  · exact lamAtomFinset_singleton_funTok u v
  · intro p hp
    have : p = (u, v) := by
      have h := Finset.mem_singleton.mp (by
        rw [← lamFunFinset_singleton_funTok u v]; exact hp)
      exact h
    subst this
    exact ⟨LamConN_mono A (Nat.le_max_left n m) hu,
      LamConN_mono A (Nat.le_max_right n m) hv⟩
  · intro s hs hIn
    have hFun : lamFunFinset ({.funTok u v} : Finset (RawLamToken α)) = {(u, v)} :=
      lamFunFinset_singleton_funTok u v
    rw [hFun] at hs
    if hmem : (u, v) ∈ s then
      have hsin : s = {(u, v)} := by
        ext p
        constructor
        · intro hp
          exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp (hs hp))
        · intro hp
          have : p = (u, v) := Finset.mem_singleton.mp hp
          subst this; exact hmem
      subst hsin
      rw [lamOutputUnion_singleton]
      exact LamConN_mono A (Nat.le_max_right n m) hv
    else
      have hempty : s = ∅ := by
        ext p
        constructor
        · intro hp
          exact False.elim (hmem (by
            have : p = (u, v) := Finset.mem_singleton.mp (hs hp)
            subst this; exact hp))
        · intro hp
          exact False.elim (Finset.notMem_empty p hp)
      subst hempty
      exact LamConN_empty A k

theorem LamCon_of_forget_singleton (p : LamToken A) :
    LamCon A (lamForgetFinset A {p}) := by
  rw [lamForgetFinset_singleton]
  match p with
  | ⟨.bot, _⟩ => exact LamCon_singleton_bot A
  | ⟨.atom x, _⟩ => exact LamCon_singleton_atom A x
  | ⟨.funTok u v, hWF⟩ => exact LamCon_singleton_funTok A u v hWF.1 hWF.2

/-- Bundled consistency on `LamToken` finsets. -/
def LamTokenCon (u : Finset (LamToken A)) : Prop :=
  LamCon A (lamForgetFinset A u)

theorem LamTokenCon_empty : LamTokenCon A (∅ : Finset (LamToken A)) := by
  simpa [LamTokenCon, lamForgetFinset_empty] using LamCon_empty A

theorem LamTokenCon_singleton (p : LamToken A) : LamTokenCon A {p} :=
  LamCon_of_forget_singleton A p

theorem LamTokenCon_subset {u v : Finset (LamToken A)}
    (hu : LamTokenCon A u) (hv : v ⊆ u) : LamTokenCon A v :=
  LamCon_subset A hu (by
    intro t ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨p, hp, rfl⟩
    exact (mem_lamForgetFinset A).2 ⟨p, hv hp, rfl⟩)

/-! ## Staged entailment (Scott (8)–(11)) — definitions only

Full `ent_refl` / `ent_con` / `ent_trans` for the `InfoSys` instance remain; the
definitions below package Scott’s clauses (8)–(11) at stages matching `LamConN`.
-/

/-- Stage-`n` entailment on raw tokens (Scott (8)–(11), stratified). -/
def LamEntN : ℕ → Finset (RawLamToken α) → RawLamToken α → Prop
  | 0, u, .bot => LamConN A 0 u
  | 0, u, .atom x =>
      LamConN A 0 u ∧ lamAtomFinset u ≠ ∅ ∧ A.Ent (lamAtomFinset u) x
  | 0, _, .funTok _ _ => False
  | n + 1, u, t =>
      LamEntN n u t ∨
        match t with
        | .bot => LamConN A (n + 1) u
        | .atom x =>
            LamConN A (n + 1) u ∧ lamFunFinset u = ∅ ∧
              lamAtomFinset u ≠ ∅ ∧ A.Ent (lamAtomFinset u) x
        | .funTok u' v' =>
            LamConN A (n + 1) u ∧ lamAtomFinset u = ∅ ∧
              LamConN A n (listToFinset u') ∧ LamConN A n (listToFinset v') ∧
              ∃ s ⊆ lamFunFinset u,
                (∀ p ∈ s, ∀ t ∈ listToFinset p.1, LamEntN n (listToFinset u') t) ∧
                  (∀ t ∈ listToFinset v', LamEntN n (lamOutputUnion s) t)

/-- Unstaged raw entailment. -/
def LamEnt (u : Finset (RawLamToken α)) (t : RawLamToken α) : Prop :=
  ∃ n, LamEntN A n u t

theorem LamEntN_mono {n m : ℕ} (hmn : n ≤ m) {u : Finset (RawLamToken α)}
    {t : RawLamToken α} (ht : LamEntN A n u t) : LamEntN A m u t := by
  induction hmn with
  | refl => exact ht
  | step _ ih => exact Or.inl ih

theorem LamEnt_bot {u : Finset (RawLamToken α)} (hu : LamCon A u) :
    LamEnt A u .bot := by
  rcases hu with ⟨n, hu⟩
  cases n with
  | zero => exact ⟨0, hu⟩
  | succ n => exact ⟨n + 1, Or.inr hu⟩

theorem LamEntN_con {n : ℕ} {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEntN A n u t) : LamConN A n u := by
  match n, t with
  | 0, .bot => exact ht
  | 0, .atom _ => exact ht.1
  | 0, .funTok _ _ => exact False.elim ht
  | n + 1, t =>
    rcases ht with ht | ht
    · exact Or.inl (LamEntN_con (n := n) ht)
    · match t with
      | .bot => exact ht
      | .atom _ => exact ht.1
      | .funTok _ _ => exact ht.1

theorem LamEnt_con {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEnt A u t) : LamCon A u := by
  rcases ht with ⟨n, ht⟩
  exact ⟨n, LamEntN_con A ht⟩

/-! ## Inversion lemmas for staged Con -/

theorem LamConN_fun_empty {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamAtomFinset u ≠ ∅) : lamFunFinset u = ∅ := by
  induction n generalizing u with
  | zero => exact hu.2
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hne
    · exact False.elim (hne hA)

theorem LamConN_atom_empty {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamFunFinset u ≠ ∅) : lamAtomFinset u = ∅ := by
  induction n generalizing u with
  | zero => exact False.elim (hne hu.2)
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hne
    · exact hA

theorem LamConN_atom_con {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamAtomFinset u ≠ ∅) : lamAtomFinset u ∈ A.Con := by
  induction n generalizing u with
  | zero => exact hu.1
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hne
    · exact False.elim (hne hA)

theorem LamConN_fun_wf {n : ℕ} {u : Finset (RawLamToken α)}
    {p : List (RawLamToken α) × List (RawLamToken α)}
    (hu : LamConN A (n + 1) u) (hp : p ∈ lamFunFinset u) :
    LamConN A n (listToFinset p.1) ∧ LamConN A n (listToFinset p.2) := by
  have aux {m : ℕ} {w : Finset (RawLamToken α)}
      (hw : LamConN A m w) (hq : p ∈ lamFunFinset w) :
      ∃ k, k + 1 ≤ m ∧
        LamConN A k (listToFinset p.1) ∧ LamConN A k (listToFinset p.2) := by
    induction m generalizing w with
    | zero =>
      exact False.elim (by
        have : p ∈ (∅ : Finset _) := by rw [← hw.2]; exact hq
        exact Finset.notMem_empty p this)
    | succ m ih =>
      rcases hw with hw | ⟨_, hWF, _⟩
      · rcases ih hw hq with ⟨k, hk, hk'⟩
        exact ⟨k, Nat.le_succ_of_le hk, hk'⟩
      · exact ⟨m, Nat.le_refl _, hWF p hq⟩
  rcases aux hu hp with ⟨k, hk, h1, h2⟩
  have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
  exact ⟨LamConN_mono A hk' h1, LamConN_mono A hk' h2⟩

/-- FunCon from an explicit right-branch witness at stage `n+1`. -/
theorem LamConN_fun_FunCon_right {n : ℕ} {u : Finset (RawLamToken α)}
    (_hA : lamAtomFinset u = ∅)
    (_hWF : ∀ p ∈ lamFunFinset u,
      LamConN A n (listToFinset p.1) ∧ LamConN A n (listToFinset p.2))
    (hFun : ∀ s ⊆ lamFunFinset u,
      LamConN A n (lamInputUnion s) → LamConN A n (lamOutputUnion s))
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hIn : LamConN A n (lamInputUnion s)) :
    LamConN A n (lamOutputUnion s) :=
  hFun s hs hIn

/-- If `u` has function tokens at stage `n`, some earlier right branch supplies FunCon. -/
theorem LamConN_exists_FunCon {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hne : lamFunFinset u ≠ ∅) :
    ∃ k, k + 1 ≤ n ∧ lamAtomFinset u = ∅ ∧
      (∀ p ∈ lamFunFinset u,
        LamConN A k (listToFinset p.1) ∧ LamConN A k (listToFinset p.2)) ∧
      (∀ s ⊆ lamFunFinset u,
        LamConN A k (lamInputUnion s) → LamConN A k (lamOutputUnion s)) := by
  induction n generalizing u with
  | zero => exact False.elim (hne hu.2)
  | succ n ih =>
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · rcases ih hu hne with ⟨k, hk, H⟩
      exact ⟨k, Nat.le_succ_of_le hk, H⟩
    · exact ⟨n, Nat.le_refl _, hA, hWF, hFun⟩

/-- Atom/bot-only sets that are consistent at stage `n` are consistent at stage `0`. -/
theorem LamConN_down_atom {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) (hF : lamFunFinset u = ∅) : LamConN A 0 u := by
  induction n generalizing u with
  | zero => exact hu
  | succ n ih =>
    rcases hu with hu | ⟨hA, _, _⟩
    · exact ih hu hF
    · exact ⟨by rw [hA]; exact A.con_empty, hF⟩

/-- Apply a stage-`k` FunCon at stage `m ≥ k` when the input union has no function tokens. -/
theorem LamConN_FunCon_mono_atom {k m : ℕ} (hkm : k ≤ m)
    {u : Finset (RawLamToken α)}
    (hFun : ∀ s ⊆ lamFunFinset u,
      LamConN A k (lamInputUnion s) → LamConN A k (lamOutputUnion s))
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u)
    (hIn : LamConN A m (lamInputUnion s))
    (hF : lamFunFinset (lamInputUnion s) = ∅) :
    LamConN A m (lamOutputUnion s) := by
  have h0 := LamConN_down_atom A hIn hF
  have hk : LamConN A k (lamInputUnion s) := LamConN_mono A (Nat.zero_le k) h0
  exact LamConN_mono A hkm (hFun s hs hk)

/-- Full FunCon at stage `n+1` (uses `exists_FunCon` + atom-input lift).
Nested function tokens in the input union remain for the general `ent_con` argument. -/
theorem LamConN_fun_FunCon_atom {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A (n + 1) u)
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hIn : LamConN A n (lamInputUnion s))
    (hF : lamFunFinset (lamInputUnion s) = ∅) :
    LamConN A n (lamOutputUnion s) := by
  if hempty : s = ∅ then
    subst hempty
    simpa [lamOutputUnion_empty] using LamConN_empty A n
  else
    have hne : lamFunFinset u ≠ ∅ := by
      obtain ⟨p, hp⟩ := Finset.nonempty_of_ne_empty hempty
      exact Finset.ne_empty_of_mem (hs hp)
    rcases LamConN_exists_FunCon A hu hne with ⟨k, hk, _, _, hFun⟩
    have hkn : k ≤ n := Nat.le_of_succ_le_succ hk
    exact LamConN_FunCon_mono_atom A hkn hFun hs hIn hF

/-- Membership entailment at a fixed stage (Scott (v) / ent_refl on raw tokens). -/
theorem LamEntN_of_mem {n : ℕ} {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamConN A n u) (ht : t ∈ u) : LamEntN A n u t := by
  induction n generalizing u t with
  | zero =>
    match t with
    | .bot => exact hu
    | .atom x =>
      exact ⟨hu, Finset.ne_empty_of_mem (mem_lamAtomFinset.2 ht),
        A.ent_refl hu.1 (mem_lamAtomFinset.2 ht)⟩
    | .funTok _ _ =>
      exact False.elim (by
        have hp : (_, _) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        rw [hu.2] at hp; exact Finset.notMem_empty _ hp)
  | succ n ih =>
    rcases hu with hu | hRight
    · exact Or.inl (ih hu ht)
    · have huFull : LamConN A (n + 1) u := Or.inr hRight
      match t with
      | .bot => exact Or.inr huFull
      | .atom x =>
        exact False.elim (by
          have : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
          rw [hRight.1] at this; exact Finset.notMem_empty x this)
      | .funTok xs ys =>
        have hmem : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        have hWF := LamConN_fun_wf A huFull hmem
        refine Or.inr ⟨huFull, hRight.1, hWF.1, hWF.2, ⟨{(xs, ys)}, ?_, ?_, ?_⟩⟩
        · intro p hp
          have : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst this
          exact hmem
        · intro p hp t ht'
          have : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst this
          exact ih hWF.1 ht'
        · intro t ht'
          rw [lamOutputUnion_singleton (xs, ys)]
          exact ih hWF.2 ht'

theorem LamEnt_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamCon A u) (ht : t ∈ u) : LamEnt A u t := by
  rcases hu with ⟨n, hu⟩
  exact ⟨n, LamEntN_of_mem A hu ht⟩

/-- Bundled entailment on `LamToken`. -/
def LamTokenEnt (u : Finset (LamToken A)) (p : LamToken A) : Prop :=
  LamEnt A (lamForgetFinset A u) p.val

theorem LamTokenEnt_bot {u : Finset (LamToken A)} (hu : LamTokenCon A u) :
    LamTokenEnt A u (lamBot A) :=
  LamEnt_bot A hu

theorem LamTokenEnt_of_mem {u : Finset (LamToken A)} {p : LamToken A}
    (hu : LamTokenCon A u) (hp : p ∈ u) : LamTokenEnt A u p :=
  LamEnt_of_mem A hu ((mem_lamForgetFinset A).2 ⟨p, hp, rfl⟩)

/-! ## ent_con: inserting an entailed token preserves consistency -/

theorem lamInputUnion_insert
    (s : Finset (List (RawLamToken α) × List (RawLamToken α)))
    (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamInputUnion (insert p s) = listToFinset p.1 ∪' lamInputUnion s := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamInputUnion).1 ht with ⟨q, hq, ht'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact mem_funion.2 (Or.inl ht')
    · exact mem_funion.2 (Or.inr ((mem_lamInputUnion).2 ⟨q, hq, ht'⟩))
  · intro ht
    rcases mem_funion.1 ht with ht | ht
    · exact (mem_lamInputUnion).2 ⟨p, Finset.mem_insert_self p s, ht⟩
    · rcases (mem_lamInputUnion).1 ht with ⟨q, hq, ht'⟩
      exact (mem_lamInputUnion).2 ⟨q, Finset.mem_insert_of_mem hq, ht'⟩

theorem lamOutputUnion_insert
    (s : Finset (List (RawLamToken α) × List (RawLamToken α)))
    (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamOutputUnion (insert p s) = listToFinset p.2 ∪' lamOutputUnion s := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamOutputUnion).1 ht with ⟨q, hq, ht'⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact mem_funion.2 (Or.inl ht')
    · exact mem_funion.2 (Or.inr ((mem_lamOutputUnion).2 ⟨q, hq, ht'⟩))
  · intro ht
    rcases mem_funion.1 ht with ht | ht
    · exact (mem_lamOutputUnion).2 ⟨p, Finset.mem_insert_self p s, ht⟩
    · rcases (mem_lamOutputUnion).1 ht with ⟨q, hq, ht'⟩
      exact (mem_lamOutputUnion).2 ⟨q, Finset.mem_insert_of_mem hq, ht'⟩

theorem lamInputUnion_funion
    (s t : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    lamInputUnion (s ∪' t) = lamInputUnion s ∪' lamInputUnion t := by
  ext x
  constructor
  · intro hx
    rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.1 hp with hp | hp
    · exact mem_funion.2 (Or.inl ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.2 (Or.inr ((mem_lamInputUnion).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.1 hx with hx | hx
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, mem_funion.2 (Or.inl hp), hx'⟩
    · rcases (mem_lamInputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamInputUnion).2 ⟨p, mem_funion.2 (Or.inr hp), hx'⟩

theorem lamOutputUnion_funion
    (s t : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    lamOutputUnion (s ∪' t) = lamOutputUnion s ∪' lamOutputUnion t := by
  ext x
  constructor
  · intro hx
    rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.1 hp with hp | hp
    · exact mem_funion.2 (Or.inl ((mem_lamOutputUnion).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.2 (Or.inr ((mem_lamOutputUnion).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.1 hx with hx | hx
    · rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamOutputUnion).2 ⟨p, mem_funion.2 (Or.inl hp), hx'⟩
    · rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamOutputUnion).2 ⟨p, mem_funion.2 (Or.inr hp), hx'⟩

theorem LamConN_insert_bot {n : ℕ} {u : Finset (RawLamToken α)}
    (hu : LamConN A n u) : LamConN A n (insert (.bot : RawLamToken α) u) := by
  induction n generalizing u with
  | zero =>
    exact ⟨by rw [lamAtomFinset_insert_bot]; exact hu.1,
      by rw [lamFunFinset_insert_bot]; exact hu.2⟩
  | succ n ih =>
    rcases hu with hu | ⟨hA, hWF, hFun⟩
    · exact Or.inl (ih hu)
    · exact Or.inr ⟨by rw [lamAtomFinset_insert_bot]; exact hA,
        fun p hp => hWF p (by rwa [lamFunFinset_insert_bot] at hp),
        fun s hs hIn =>
          hFun s (fun p hp => by rw [← lamFunFinset_insert_bot u]; exact hs hp) hIn⟩

/-- Inserting an entailed bot or atom preserves stage-`n` consistency.
Function-token `ent_con` (FunCon on `insert`) remains. -/
theorem LamConN_insert_of_ent_atom {n : ℕ} {u : Finset (RawLamToken α)} {x : α}
    (ht : LamEntN A n u (.atom x)) : LamConN A n (insert (.atom x) u) := by
  induction n generalizing u with
  | zero =>
    rcases ht with ⟨⟨_, hF⟩, _, hEnt⟩
    exact ⟨by rw [lamAtomFinset_insert_atom]; exact A.ent_con hEnt,
      by rw [lamFunFinset_insert_atom]; exact hF⟩
  | succ n ih =>
    rcases ht with ht | ⟨_, hF, _, hEnt⟩
    · exact Or.inl (ih ht)
    · exact LamConN_mono A (Nat.zero_le (n + 1))
        ⟨by rw [lamAtomFinset_insert_atom]; exact A.ent_con hEnt,
          by rw [lamFunFinset_insert_atom]; exact hF⟩

theorem LamConN_insert_of_ent_bot {n : ℕ} {u : Finset (RawLamToken α)}
    (ht : LamEntN A n u .bot) : LamConN A n (insert (.bot : RawLamToken α) u) :=
  LamConN_insert_bot A (LamEntN_con A ht)

theorem lamForgetFinset_insert (u : Finset (LamToken A)) (p : LamToken A) :
    lamForgetFinset A (insert p u) = insert p.val (lamForgetFinset A u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_lamForgetFinset A).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_lamForgetFinset A).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, rfl⟩
      exact (mem_lamForgetFinset A).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

/-- Def 2.1 progress: `con_subset`, `con_sing`, `ent_bot`, `ent_refl`;
`ent_con` for bot/atom; `ent_con`/`ent_trans` on `funTok` remain. -/
theorem lambdaSystem_con_axioms :
    (∀ {u v : Finset (LamToken A)}, LamTokenCon A u → v ⊆ u → LamTokenCon A v) ∧
      (∀ p : LamToken A, LamTokenCon A {p}) ∧
        (∀ {u : Finset (LamToken A)}, LamTokenCon A u → LamTokenEnt A u (lamBot A)) ∧
          (∀ {u : Finset (LamToken A)} {p : LamToken A},
            LamTokenCon A u → p ∈ u → LamTokenEnt A u p) :=
  ⟨fun hu hv => LamTokenCon_subset A hu hv,
    LamTokenCon_singleton A,
    fun hu => LamTokenEnt_bot A hu,
    fun hu hp => LamTokenEnt_of_mem A hu hp⟩


/-! ## Depth measure (for well-founded Con) -/

private theorem max_le_max_nat {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d :=
  max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))


def rawDepth : RawLamToken α → ℕ
  | .bot | .atom _ => 0
  | .funTok u v =>
      1 + Nat.max
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v)

theorem foldl_max_mono_init {u : List (RawLamToken α)} {i j : ℕ} (hij : i ≤ j) :
    List.foldl (fun d t => Nat.max d (rawDepth t)) i u ≤
      List.foldl (fun d t => Nat.max d (rawDepth t)) j u := by
  induction u generalizing i j with
  | nil => exact hij
  | cons a as ih => exact ih (max_le_max_nat hij le_rfl)

theorem foldl_max_ge_init (u : List (RawLamToken α)) (init : ℕ) :
    init ≤ List.foldl (fun d t => Nat.max d (rawDepth t)) init u := by
  induction u generalizing init with
  | nil => exact le_rfl
  | cons a as ih =>
    exact Nat.le_trans (Nat.le_max_left init (rawDepth a)) (ih _)

theorem foldl_list_le_of_mem {t : RawLamToken α} {u : List (RawLamToken α)}
    (ht : t ∈ u) :
    rawDepth t ≤ List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u := by
  induction u with
  | nil => cases ht
  | cons a as ih =>
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right 0 (rawDepth t))
        (foldl_max_ge_init as (Nat.max 0 (rawDepth t)))
    · exact Nat.le_trans (ih ht) (foldl_max_mono_init (Nat.zero_le _))

theorem rawDepth_funTok_gt_left {u v : List (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ u) : rawDepth t < rawDepth (.funTok u v) := by
  have h : rawDepth t ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_trans (foldl_list_le_of_mem ht) (Nat.le_max_left _ _)
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt h (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

theorem rawDepth_funTok_gt_right {u v : List (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ v) : rawDepth t < rawDepth (.funTok u v) := by
  have h : rawDepth t ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_trans (foldl_list_le_of_mem ht) (Nat.le_max_right _ _)
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt h (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

private def maxDepthInsert : RawLamToken α → ℕ → ℕ :=
  fun t d => Nat.max (rawDepth t) d

private instance : LeftCommutative (maxDepthInsert (α := α)) :=
  ⟨fun a b d => by simp only [maxDepthInsert]; exact Nat.max_left_comm _ _ _⟩

def finsetMaxDepth (u : Finset (RawLamToken α)) : ℕ :=
  Multiset.foldr (maxDepthInsert (α := α)) 0 u.1

theorem le_finsetMaxDepth_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : t ∈ u) : rawDepth t ≤ finsetMaxDepth u := by
  simp only [finsetMaxDepth]
  have ht' : t ∈ u.1 := Finset.mem_def.1 ht
  revert ht'
  refine Multiset.induction_on u.1 ?_ ?_
  · intro ht'; cases ht'
  · intro a s ih ht'
    simp only [Multiset.mem_cons] at ht'
    simp only [Multiset.foldr_cons, maxDepthInsert]
    rcases ht' with rfl | ht'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht') (Nat.le_max_right _ _)

theorem foldr_max_le_of_forall {s : Multiset (RawLamToken α)} {b : ℕ}
    (h : ∀ t ∈ s, rawDepth t ≤ b) :
    Multiset.foldr (maxDepthInsert (α := α)) 0 s ≤ b := by
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro; exact Nat.zero_le _
  · intro a s ih h
    simp only [Multiset.foldr_cons, maxDepthInsert]
    exact Nat.max_le.2 ⟨h a (Multiset.mem_cons_self _ _),
      ih fun t ht => h t (Multiset.mem_cons_of_mem ht)⟩

theorem foldr_max_lt_of_forall {s : Multiset (RawLamToken α)} {b : ℕ}
    (hb : 0 < b) (h : ∀ t ∈ s, rawDepth t < b) :
    Multiset.foldr (maxDepthInsert (α := α)) 0 s < b := by
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro; exact hb
  · intro a s ih h
    simp only [Multiset.foldr_cons, maxDepthInsert]
    exact Nat.max_lt.2 ⟨h a (Multiset.mem_cons_self _ _),
      ih fun t ht => h t (Multiset.mem_cons_of_mem ht)⟩

theorem finsetMaxDepth_listToFinset_le (u : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset u) ≤
      List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u := by
  simp only [finsetMaxDepth]
  exact foldr_max_le_of_forall fun t ht =>
    foldl_list_le_of_mem ((mem_listToFinset).1 (Finset.mem_def.2 ht))

theorem finsetMaxDepth_list_lt_funTok (u v : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset u) < rawDepth (.funTok u v) := by
  have h1 := finsetMaxDepth_listToFinset_le u
  have h2 : List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_max_left _ _
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

theorem finsetMaxDepth_list_lt_funTok_out (u v : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset v) < rawDepth (.funTok u v) := by
  have h1 := finsetMaxDepth_listToFinset_le v
  have h2 : List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_max_right _ _
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_add_of_pos_left (Nat.succ_pos 0))


theorem finsetMaxDepth_of_mem_funTok {u : Finset (RawLamToken α)}
    {xs ys : List (RawLamToken α)} (h : .funTok xs ys ∈ u) :
    finsetMaxDepth (listToFinset xs) < finsetMaxDepth u ∧
      finsetMaxDepth (listToFinset ys) < finsetMaxDepth u :=
  ⟨Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok xs ys) (le_finsetMaxDepth_of_mem h),
    Nat.lt_of_lt_of_le (finsetMaxDepth_list_lt_funTok_out xs ys) (le_finsetMaxDepth_of_mem h)⟩

theorem finsetMaxDepth_inputUnion_lt {u : Finset (RawLamToken α)}
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hfun : lamFunFinset u ≠ ∅) :
    finsetMaxDepth (lamInputUnion s) < finsetMaxDepth u := by
  obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hfun
  have htok0 : .funTok p0.1 p0.2 ∈ u := mem_lamFunFinset.1 hp0
  have hpos : 0 < finsetMaxDepth u := by
    have hraw : 0 < rawDepth (.funTok p0.1 p0.2) := by
      simp only [rawDepth]
      exact Nat.add_pos_left (Nat.succ_pos 0) _
    exact Nat.lt_of_lt_of_le hraw (le_finsetMaxDepth_of_mem htok0)
  refine foldr_max_lt_of_forall (s := (lamInputUnion s).1) hpos ?_
  intro t ht
  have ht' : t ∈ lamInputUnion s := Finset.mem_def.2 ht
  rcases (mem_lamInputUnion).1 ht' with ⟨p, hp, htp⟩
  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
  exact Nat.lt_of_lt_of_le
    (rawDepth_funTok_gt_left ((mem_listToFinset).1 htp))
    (le_finsetMaxDepth_of_mem htok)

theorem finsetMaxDepth_outputUnion_lt {u : Finset (RawLamToken α)}
    {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    (hs : s ⊆ lamFunFinset u) (hfun : lamFunFinset u ≠ ∅) :
    finsetMaxDepth (lamOutputUnion s) < finsetMaxDepth u := by
  obtain ⟨p0, hp0⟩ := Finset.nonempty_of_ne_empty hfun
  have htok0 : .funTok p0.1 p0.2 ∈ u := mem_lamFunFinset.1 hp0
  have hpos : 0 < finsetMaxDepth u := by
    have hraw : 0 < rawDepth (.funTok p0.1 p0.2) := by
      simp only [rawDepth]
      exact Nat.add_pos_left (Nat.succ_pos 0) _
    exact Nat.lt_of_lt_of_le hraw (le_finsetMaxDepth_of_mem htok0)
  refine foldr_max_lt_of_forall (s := (lamOutputUnion s).1) hpos ?_
  intro t ht
  have ht' : t ∈ lamOutputUnion s := Finset.mem_def.2 ht
  rcases (mem_lamOutputUnion).1 ht' with ⟨p, hp, htp⟩
  have htok : .funTok p.1 p.2 ∈ u := mem_lamFunFinset.1 (hs hp)
  exact Nat.lt_of_lt_of_le
    (rawDepth_funTok_gt_right ((mem_listToFinset).1 htp))
    (le_finsetMaxDepth_of_mem htok)

/-- Depth-based consistency: FunCon in the recursive clause (Scott (7)).
Uses `decidableEq_finset` so the empty-fun branch does not pull `Classical.choice`. -/
def LamConDepth (u : Finset (RawLamToken α)) : Prop :=
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  if _hF : lamFunFinset u = ∅ then
    lamAtomFinset u ∈ A.Con
  else
    lamAtomFinset u = ∅ ∧
      (∀ p ∈ lamFunFinset u,
        LamConDepth (listToFinset p.1) ∧ LamConDepth (listToFinset p.2)) ∧
      (∀ s ⊆ lamFunFinset u,
        LamConDepth (lamInputUnion s) → LamConDepth (lamOutputUnion s))
termination_by finsetMaxDepth u
decreasing_by
  · exact (finsetMaxDepth_of_mem_funTok (mem_lamFunFinset.1 ‹_›)).1
  · exact (finsetMaxDepth_of_mem_funTok (mem_lamFunFinset.1 ‹_›)).2
  · exact finsetMaxDepth_inputUnion_lt ‹_› ‹_›
  · exact finsetMaxDepth_outputUnion_lt ‹_› ‹_›

theorem LamConDepth_empty : LamConDepth A (∅ : Finset (RawLamToken α)) := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  rw [LamConDepth.eq_1, dif_pos lamFunFinset_empty, lamAtomFinset_empty]
  exact A.con_empty

theorem LamConDepth_of_fun_empty {u : Finset (RawLamToken α)}
    (hF : lamFunFinset u = ∅) :
    LamConDepth A u ↔ lamAtomFinset u ∈ A.Con := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  rw [LamConDepth.eq_1, dif_pos hF]

theorem LamConDepth_of_fun_nonempty {u : Finset (RawLamToken α)}
    (hF : lamFunFinset u ≠ ∅) :
    LamConDepth A u ↔
      lamAtomFinset u = ∅ ∧
        (∀ p ∈ lamFunFinset u,
          LamConDepth A (listToFinset p.1) ∧ LamConDepth A (listToFinset p.2)) ∧
        (∀ s ⊆ lamFunFinset u,
          LamConDepth A (lamInputUnion s) → LamConDepth A (lamOutputUnion s)) := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  rw [LamConDepth.eq_1, dif_neg hF]

theorem LamConDepth_mono {u v : Finset (RawLamToken α)}
    (huv : u ⊆ v) (hv : LamConDepth A v) : LamConDepth A u := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hFunMono := lamFunFinset_mono huv
  have hAtomMono := lamAtomFinset_mono huv
  by_cases hFv : lamFunFinset v = ∅
  · have hFu : lamFunFinset u = ∅ :=
      Finset.Subset.antisymm
        (fun p hp => by
          have := hFunMono hp
          rw [hFv] at this; exact False.elim (Finset.notMem_empty p this))
        (Finset.empty_subset _)
    exact (LamConDepth_of_fun_empty A hFu).2
      (A.con_subset ((LamConDepth_of_fun_empty A hFv).1 hv) hAtomMono)
  · have hv' := (LamConDepth_of_fun_nonempty A hFv).1 hv
    rcases hv' with ⟨hAv, hWF, hFun⟩
    by_cases hFu : lamFunFinset u = ∅
    · have hAu : lamAtomFinset u = ∅ :=
        Finset.Subset.antisymm
          (fun x hx => by
            have := hAtomMono hx
            rw [hAv] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      exact (LamConDepth_of_fun_empty A hFu).2 (by rw [hAu]; exact A.con_empty)
    · refine (LamConDepth_of_fun_nonempty A hFu).2 ⟨?_, ?_, ?_⟩
      · exact Finset.Subset.antisymm
          (fun x hx => by
            have := hAtomMono hx
            rw [hAv] at this; exact False.elim (Finset.notMem_empty x this))
          (Finset.empty_subset _)
      · intro p hp; exact hWF p (hFunMono hp)
      · intro s hs hIn
        exact hFun s (fun p hp => hFunMono (hs hp)) hIn

theorem LamConDepth_singleton_bot :
    LamConDepth A ({.bot} : Finset (RawLamToken α)) := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hF : lamFunFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
    ext p; constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)
  exact (LamConDepth_of_fun_empty A hF).2 (by
    have h : lamAtomFinset ({.bot} : Finset (RawLamToken α)) = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch mem_lamAtomFinset.1 hx)
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    rw [h]; exact A.con_empty)

theorem LamConDepth_singleton_atom (x : α) :
    LamConDepth A ({.atom x} : Finset (RawLamToken α)) := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  have hF : lamFunFinset ({.atom x} : Finset (RawLamToken α)) = ∅ := by
    ext p; constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)
  exact (LamConDepth_of_fun_empty A hF).2 (by
    have h : lamAtomFinset ({.atom x} : Finset (RawLamToken α)) = {x} := by
      ext y; simp only [mem_lamAtomFinset, Finset.mem_singleton]
      exact ⟨RawLamToken.atom.inj, congrArg RawLamToken.atom⟩
    rw [h]; exact A.con_sing x)

/-! ## Depth-based entailment (Scott (8)–(11), inductive FunEnt-style) -/

/-- Depth-based entailment as an inductive Prop (Scott (8)–(11)).
Premises are positive, so FunEnt-style recursion is allowed — unlike FunCon
inside an inductive `LamCon`. -/
inductive LamEntDepth : Finset (RawLamToken α) → RawLamToken α → Prop where
  | bot {u : Finset (RawLamToken α)}
      (hu : LamConDepth A u) : LamEntDepth u .bot
  | atom {u : Finset (RawLamToken α)} {x : α}
      (hu : LamConDepth A u)
      (hF : lamFunFinset u = ∅)
      (hne : lamAtomFinset u ≠ ∅)
      (hEnt : A.Ent (lamAtomFinset u) x) : LamEntDepth u (.atom x)
  | funTok {u : Finset (RawLamToken α)} {xs ys : List (RawLamToken α)}
      {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
      (hu : LamConDepth A u)
      (hA : lamAtomFinset u = ∅)
      (hConIn : LamConDepth A (listToFinset xs))
      (hConOut : LamConDepth A (listToFinset ys))
      (hs : s ⊆ lamFunFinset u)
      (hEntIn : ∀ p ∈ s, ∀ z ∈ listToFinset p.1, LamEntDepth (listToFinset xs) z)
      (hEntOut : ∀ z ∈ listToFinset ys, LamEntDepth (lamOutputUnion s) z) :
      LamEntDepth u (.funTok xs ys)

theorem LamEntDepth_con {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (ht : LamEntDepth A u t) : LamConDepth A u := by
  cases ht with
  | bot hu => exact hu
  | atom hu _ _ _ => exact hu
  | funTok hu _ _ _ _ _ _ => exact hu

theorem LamEntDepth_bot {u : Finset (RawLamToken α)} (hu : LamConDepth A u) :
    LamEntDepth A u .bot :=
  LamEntDepth.bot hu

theorem LamEntDepth_of_mem {u : Finset (RawLamToken α)} {t : RawLamToken α}
    (hu : LamConDepth A u) (ht : t ∈ u) : LamEntDepth A u t := by
  suffices ∀ M u t, Nat.max (finsetMaxDepth u) (rawDepth t) = M →
      LamConDepth A u → t ∈ u → LamEntDepth A u t from
    this _ _ _ rfl hu ht
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro u t hM hu ht
    match t with
    | .bot => exact LamEntDepth_bot A hu
    | .atom x =>
      cases decidableEq_finset (lamFunFinset u) ∅ with
      | isTrue hF =>
        have hx : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
        exact LamEntDepth.atom hu hF (Finset.ne_empty_of_mem hx)
          (A.ent_refl ((LamConDepth_of_fun_empty A hF).1 hu) hx)
      | isFalse hF =>
        have hA := ((LamConDepth_of_fun_nonempty A hF).1 hu).1
        have hx : x ∈ lamAtomFinset u := mem_lamAtomFinset.2 ht
        rw [hA] at hx; exact False.elim (Finset.notMem_empty x hx)
    | .funTok xs ys =>
      cases decidableEq_finset (lamFunFinset u) ∅ with
      | isTrue hF =>
        have : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        rw [hF] at this; exact False.elim (Finset.notMem_empty _ this)
      | isFalse hF =>
        have hu' := (LamConDepth_of_fun_nonempty A hF).1 hu
        rcases hu' with ⟨hA, hWF, _hFun⟩
        have hmem : (xs, ys) ∈ lamFunFinset u := mem_lamFunFinset.2 ht
        have ⟨hConIn, hConOut⟩ := hWF (xs, ys) hmem
        refine LamEntDepth.funTok (s := {(xs, ys)}) hu hA hConIn hConOut
          (fun p hp => by
            have hp' : p = (xs, ys) := Finset.mem_singleton.mp hp
            exact hp' ▸ hmem) ?_ ?_
        · intro p hp z hz
          have hp' : p = (xs, ys) := Finset.mem_singleton.mp hp
          subst hp'
          refine ih (Nat.max (finsetMaxDepth (listToFinset xs)) (rawDepth z))
            ?_ (listToFinset xs) z rfl hConIn hz
          have htok : .funTok xs ys ∈ u := mem_lamFunFinset.1 hmem
          have ht_lt : rawDepth z < finsetMaxDepth u :=
            Nat.lt_of_lt_of_le (rawDepth_funTok_gt_left ((mem_listToFinset).1 hz))
              (le_finsetMaxDepth_of_mem htok)
          have hxs_lt : finsetMaxDepth (listToFinset xs) < rawDepth (.funTok xs ys) :=
            finsetMaxDepth_list_lt_funTok xs ys
          rw [← hM]
          refine Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le hxs_lt (Nat.le_max_right _ _),
            Nat.lt_of_lt_of_le ht_lt (Nat.le_max_left _ _)⟩
        · intro z hz
          rw [lamOutputUnion_singleton]
          refine ih (Nat.max (finsetMaxDepth (listToFinset ys)) (rawDepth z))
            ?_ (listToFinset ys) z rfl hConOut hz
          have ht_lt : rawDepth z < rawDepth (.funTok xs ys) :=
            rawDepth_funTok_gt_right ((mem_listToFinset).1 hz)
          have hys_lt : finsetMaxDepth (listToFinset ys) < rawDepth (.funTok xs ys) :=
            finsetMaxDepth_list_lt_funTok_out xs ys
          rw [← hM]
          refine Nat.max_lt.2 ⟨
            Nat.lt_of_lt_of_le hys_lt (Nat.le_max_right _ _),
            Nat.lt_of_lt_of_le ht_lt (Nat.le_max_right _ _)⟩

/-- Inserting bot preserves depth-Con. -/
theorem LamConDepth_insert_bot {u : Finset (RawLamToken α)}
    (hu : LamConDepth A u) :
    LamConDepth A (insert (.bot : RawLamToken α) u) := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  by_cases hF : lamFunFinset u = ∅
  · have hF' : lamFunFinset (insert (.bot : RawLamToken α) u) = ∅ := by
      rw [lamFunFinset_insert_bot]; exact hF
    exact (LamConDepth_of_fun_empty A hF').2 (by
      rw [lamAtomFinset_insert_bot]
      exact (LamConDepth_of_fun_empty A hF).1 hu)
  · have hu' := (LamConDepth_of_fun_nonempty A hF).1 hu
    rcases hu' with ⟨hA, hWF, hFun⟩
    have hF' : lamFunFinset (insert (.bot : RawLamToken α) u) ≠ ∅ := by
      rw [lamFunFinset_insert_bot]; exact hF
    refine (LamConDepth_of_fun_nonempty A hF').2 ⟨?_, ?_, ?_⟩
    · rw [lamAtomFinset_insert_bot]; exact hA
    · intro p hp
      rw [lamFunFinset_insert_bot] at hp
      exact hWF p hp
    · intro s hs hIn
      refine hFun s (by rw [← lamFunFinset_insert_bot u]; exact hs) hIn

/-- Inserting an entailed atom preserves depth-Con. -/
theorem LamConDepth_insert_atom {u : Finset (RawLamToken α)} {x : α}
    (ht : LamEntDepth A u (.atom x)) :
    LamConDepth A (insert (.atom x) u) := by
  haveI : DecidableEq (Finset (List (RawLamToken α) × List (RawLamToken α))) :=
    decidableEq_finset
  cases ht with
  | atom hu hF _hne hEnt =>
    have hF' : lamFunFinset (insert (.atom x) u) = ∅ := by
      rw [lamFunFinset_insert_atom]; exact hF
    exact (LamConDepth_of_fun_empty A hF').2 (by
      rw [lamAtomFinset_insert_atom]
      exact A.ent_con hEnt)

/-- Weaken entailment when the larger set stays in the function world (`atom = ∅`). -/
theorem LamEntDepth_weaken_fun {u v : Finset (RawLamToken α)} {t : RawLamToken α}
    (huv : u ⊆ v) (hv : LamConDepth A v) (hAv : lamAtomFinset v = ∅)
    (ht : LamEntDepth A u t) : LamEntDepth A v t := by
  cases ht with
  | bot _ => exact LamEntDepth.bot hv
  | atom _ _ hne _ =>
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
    exact False.elim (Finset.notMem_empty x (by
      have := lamAtomFinset_mono huv hx; rwa [hAv] at this))
  | funTok _ _ hConIn hConOut hs hEntIn hEntOut =>
    exact LamEntDepth.funTok hv hAv hConIn hConOut
      (fun p hp => lamFunFinset_mono huv (hs hp)) hEntIn hEntOut

/-- Weaken atom-entailment when the larger set stays in the atom world (`fun = ∅`). -/
theorem LamEntDepth_weaken_atom {u v : Finset (RawLamToken α)} {x : α}
    (huv : u ⊆ v) (hv : LamConDepth A v) (hFv : lamFunFinset v = ∅)
    (ht : LamEntDepth A u (.atom x)) : LamEntDepth A v (.atom x) := by
  cases ht with
  | atom hu hF hne hEnt =>
    have hsubA := lamAtomFinset_mono huv
    have hne' : lamAtomFinset v ≠ ∅ := by
      intro hAv
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
      exact Finset.notMem_empty y (by have := hsubA hy; rwa [hAv] at this)
    exact LamEntDepth.atom hv hFv hne'
      (A.ent_trans ((LamConDepth_of_fun_empty A hFv).1 hv)
        ((LamConDepth_of_fun_empty A hF).1 hu)
        (fun y hy => A.ent_refl ((LamConDepth_of_fun_empty A hFv).1 hv) (hsubA hy))
        hEnt)

end InfoSys

end Scott1982
