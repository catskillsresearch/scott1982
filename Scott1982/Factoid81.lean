/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Product
import Scott1982.Sum

/-!
# Factoid 8.1 — tree / S-expression domain `T ≅ A + (T × T)`

**Scott 1982, §8.** Given `A`, the domain `T` of unlabelled binary trees with atoms
from `A` is defined so tokens, consistency, and entailment match the separated sum
of `A` with the product `T × T` (Scott clauses (1)–(12)). The domain equation then
holds by this matching: we package it as an `InfoSys` on an inductive token type
together with the unfolding map into `A + (T × T)`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

/-! ## Tokens (Scott §8 (1)–(3)) -/

/-- Tokens of the tree system: sum tagging of atoms and product left/right copies. -/
inductive TreeToken (α : Type*) where
  | bot : TreeToken α
  | atom : α → TreeToken α
  | pairL : TreeToken α → TreeToken α
  | pairR : TreeToken α → TreeToken α
  deriving DecidableEq

/-- Tree bottom `Δ_T`. -/
def treeBot : TreeToken α := .bot

/-! ## Projections -/

private def atomInsert : TreeToken α → Finset α → Finset α
  | .atom x => insert x
  | .bot | .pairL _ | .pairR _ => id

private def pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairL t => insert t
  | .bot | .atom _ | .pairR _ => id

private def pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairR t => insert t
  | .bot | .atom _ | .pairL _ => id

private instance : LeftCommutative (atomInsert : TreeToken α → Finset α → Finset α) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance :
    LeftCommutative (pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

private instance :
    LeftCommutative (pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def atomFinset (u : Finset (TreeToken α)) : Finset α :=
  Multiset.foldr atomInsert (∅ : Finset α) u.1

def pairLFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr pairLInsert (∅ : Finset (TreeToken α)) u.1

def pairRFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr pairRInsert (∅ : Finset (TreeToken α)) u.1

private theorem mem_foldr_atom (s : Multiset (TreeToken α)) (x : α) :
    x ∈ Multiset.foldr atomInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .atom x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx; exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | atom a =>
      simp only [Multiset.foldr_cons, atomInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hx | ⟨q, hq, hq'⟩)
        · exact ⟨.atom a, Or.inl rfl, congrArg TreeToken.atom hx.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hx; exact Or.inl hx.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | pairL _ | pairR _ =>
      simp only [Multiset.foldr_cons, atomInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

private theorem mem_foldr_pairL (s : Multiset (TreeToken α)) (t : TreeToken α) :
    t ∈ Multiset.foldr pairLInsert (∅ : Finset (TreeToken α)) s ↔
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
        · exact ⟨.pairL a, Or.inl rfl, congrArg TreeToken.pairL ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | atom _ | pairR _ =>
      simp only [Multiset.foldr_cons, pairLInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

private theorem mem_foldr_pairR (s : Multiset (TreeToken α)) (t : TreeToken α) :
    t ∈ Multiset.foldr pairRInsert (∅ : Finset (TreeToken α)) s ↔
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
        · exact ⟨.pairR a, Or.inl rfl, congrArg TreeToken.pairR ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | atom _ | pairL _ =>
      simp only [Multiset.foldr_cons, pairRInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_atomFinset {u : Finset (TreeToken α)} {x : α} :
    x ∈ atomFinset u ↔ .atom x ∈ u := by
  constructor
  · intro hx
    rcases (mem_foldr_atom u.1 x).1 hx with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro hx
    exact (mem_foldr_atom u.1 x).2 ⟨.atom x, Finset.mem_def.1 hx, rfl⟩

theorem mem_pairLFinset {u : Finset (TreeToken α)} {t : TreeToken α} :
    t ∈ pairLFinset u ↔ .pairL t ∈ u := by
  constructor
  · intro ht
    rcases (mem_foldr_pairL u.1 t).1 ht with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro ht
    exact (mem_foldr_pairL u.1 t).2 ⟨.pairL t, Finset.mem_def.1 ht, rfl⟩

theorem mem_pairRFinset {u : Finset (TreeToken α)} {t : TreeToken α} :
    t ∈ pairRFinset u ↔ .pairR t ∈ u := by
  constructor
  · intro ht
    rcases (mem_foldr_pairR u.1 t).1 ht with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro ht
    exact (mem_foldr_pairR u.1 t).2 ⟨.pairR t, Finset.mem_def.1 ht, rfl⟩

theorem atomFinset_empty : atomFinset (∅ : Finset (TreeToken α)) = ∅ := rfl
theorem pairLFinset_empty : pairLFinset (∅ : Finset (TreeToken α)) = ∅ := rfl
theorem pairRFinset_empty : pairRFinset (∅ : Finset (TreeToken α)) = ∅ := rfl

theorem atomFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    atomFinset v ⊆ atomFinset u := fun _ hx => mem_atomFinset.2 (h (mem_atomFinset.1 hx))

theorem pairLFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    pairLFinset v ⊆ pairLFinset u := fun _ ht => mem_pairLFinset.2 (h (mem_pairLFinset.1 ht))

theorem pairRFinset_mono {u v : Finset (TreeToken α)} (h : v ⊆ u) :
    pairRFinset v ⊆ pairRFinset u := fun _ ht => mem_pairRFinset.2 (h (mem_pairRFinset.1 ht))

theorem atomFinset_insert_atom (u : Finset (TreeToken α)) (x : α) :
    atomFinset (insert (.atom x) u) = insert x (atomFinset u) := by
  ext y; simp only [Finset.mem_insert, mem_atomFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (TreeToken.atom.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem atomFinset_insert_bot (u : Finset (TreeToken α)) :
    atomFinset (insert (.bot : TreeToken α) u) = atomFinset u := by
  ext x; simp only [mem_atomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem atomFinset_insert_pairL (u : Finset (TreeToken α)) (t : TreeToken α) :
    atomFinset (insert (.pairL t) u) = atomFinset u := by
  ext x; simp only [mem_atomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem atomFinset_insert_pairR (u : Finset (TreeToken α)) (t : TreeToken α) :
    atomFinset (insert (.pairR t) u) = atomFinset u := by
  ext x; simp only [mem_atomFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairLFinset_insert_pairL (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairLFinset (insert (.pairL t) u) = insert t (pairLFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_pairLFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (TreeToken.pairL.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem pairLFinset_insert_bot (u : Finset (TreeToken α)) :
    pairLFinset (insert (.bot : TreeToken α) u) = pairLFinset u := by
  ext t; simp only [mem_pairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairLFinset_insert_atom (u : Finset (TreeToken α)) (x : α) :
    pairLFinset (insert (.atom x) u) = pairLFinset u := by
  ext t; simp only [mem_pairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairLFinset_insert_pairR (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairLFinset (insert (.pairR t) u) = pairLFinset u := by
  ext s; simp only [mem_pairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairRFinset_insert_pairR (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairRFinset (insert (.pairR t) u) = insert t (pairRFinset u) := by
  ext s; simp only [Finset.mem_insert, mem_pairRFinset]
  constructor
  · rintro (h | h)
    · exact Or.inl (TreeToken.pairR.inj h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

theorem pairRFinset_insert_bot (u : Finset (TreeToken α)) :
    pairRFinset (insert (.bot : TreeToken α) u) = pairRFinset u := by
  ext t; simp only [mem_pairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairRFinset_insert_atom (u : Finset (TreeToken α)) (x : α) :
    pairRFinset (insert (.atom x) u) = pairRFinset u := by
  ext t; simp only [mem_pairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem pairRFinset_insert_pairL (u : Finset (TreeToken α)) (t : TreeToken α) :
    pairRFinset (insert (.pairL t) u) = pairRFinset u := by
  ext s; simp only [mem_pairRFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

theorem atomFinset_singleton_atom (x : α) :
    atomFinset ({.atom x} : Finset (TreeToken α)) = {x} := by
  ext y; simp only [mem_atomFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.atom.inj h, fun h => congrArg TreeToken.atom h⟩

theorem pairLFinset_singleton_pairL (t : TreeToken α) :
    pairLFinset ({.pairL t} : Finset (TreeToken α)) = {t} := by
  ext s; simp only [mem_pairLFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.pairL.inj h, fun h => congrArg TreeToken.pairL h⟩

theorem pairRFinset_singleton_pairR (t : TreeToken α) :
    pairRFinset ({.pairR t} : Finset (TreeToken α)) = {t} := by
  ext s; simp only [mem_pairRFinset, Finset.mem_singleton]
  exact ⟨fun h => TreeToken.pairR.inj h, fun h => congrArg TreeToken.pairR h⟩

theorem atomFinset_singleton_bot :
    atomFinset ({.bot} : Finset (TreeToken α)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (nomatch mem_atomFinset.1 hx)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem pairLFinset_singleton_bot :
    pairLFinset ({.bot} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairLFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem pairRFinset_singleton_bot :
    pairRFinset ({.bot} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairRFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem pairLFinset_singleton_atom (x : α) :
    pairLFinset ({.atom x} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairLFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem pairRFinset_singleton_atom (x : α) :
    pairRFinset ({.atom x} : Finset (TreeToken α)) = ∅ := by
  ext t
  constructor
  · intro ht
    exact False.elim (nomatch mem_pairRFinset.1 ht)
  · intro ht
    exact False.elim (Finset.notMem_empty t ht)

theorem atomFinset_singleton_pairL (t : TreeToken α) :
    atomFinset ({.pairL t} : Finset (TreeToken α)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (nomatch mem_atomFinset.1 hx)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem atomFinset_singleton_pairR (t : TreeToken α) :
    atomFinset ({.pairR t} : Finset (TreeToken α)) = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (nomatch mem_atomFinset.1 hx)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem pairRFinset_singleton_pairL (t : TreeToken α) :
    pairRFinset ({.pairL t} : Finset (TreeToken α)) = ∅ := by
  ext s
  constructor
  · intro hs
    exact False.elim (nomatch mem_pairRFinset.1 hs)
  · intro hs
    exact False.elim (Finset.notMem_empty s hs)

theorem pairLFinset_singleton_pairR (t : TreeToken α) :
    pairLFinset ({.pairR t} : Finset (TreeToken α)) = ∅ := by
  ext s
  constructor
  · intro hs
    exact False.elim (nomatch mem_pairLFinset.1 hs)
  · intro hs
    exact False.elim (Finset.notMem_empty s hs)

/-! ## Consistency and entailment -/

variable (A : InfoSys α)

/-- Consistency for trees (Scott §8 (4)–(7)). -/
inductive TreeCon : Finset (TreeToken α) → Prop where
  | left (u : Finset (TreeToken α))
      (hA : atomFinset u ∈ A.Con)
      (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅) : TreeCon u
  | right (u : Finset (TreeToken α))
      (hA : atomFinset u = ∅)
      (hL : TreeCon (pairLFinset u)) (hR : TreeCon (pairRFinset u)) : TreeCon u

theorem TreeCon_empty : TreeCon A (∅ : Finset (TreeToken α)) :=
  TreeCon.left _ (by rw [atomFinset_empty]; exact A.con_empty)
    pairLFinset_empty pairRFinset_empty

/-- Payload of tree entailment (Scott §8 (8)–(12)), recursive on the token. -/
def TreeEntPayload (u : Finset (TreeToken α)) : TreeToken α → Prop
  | .bot => True
  | .atom x => atomFinset u ≠ ∅ ∧ A.Ent (atomFinset u) x
  | .pairL t =>
      atomFinset u = ∅ ∧ pairLFinset u ≠ ∅ ∧
        (TreeCon A (pairLFinset u) ∧ TreeEntPayload (pairLFinset u) t) ∧
          TreeCon A (pairRFinset u)
  | .pairR t =>
      atomFinset u = ∅ ∧ pairRFinset u ≠ ∅ ∧
        (TreeCon A (pairRFinset u) ∧ TreeEntPayload (pairRFinset u) t) ∧
          TreeCon A (pairLFinset u)

/-- Entailment for trees. -/
def TreeEnt (u : Finset (TreeToken α)) (p : TreeToken α) : Prop :=
  TreeCon A u ∧ TreeEntPayload A u p

theorem TreeCon_pairs_empty_of_left {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hA : atomFinset u ≠ ∅) :
    pairLFinset u = ∅ ∧ pairRFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR => exact ⟨hL, hR⟩
  | right _ hAt _ _ => exact False.elim (hA hAt)

theorem TreeCon_atoms_empty_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hP : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    atomFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR =>
    rcases hP with h | h
    · exact False.elim (h hL)
    · exact False.elim (h hR)
  | right _ hA _ _ => exact hA

theorem TreeCon_atom_con_of_atoms {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hne : atomFinset u ≠ ∅) : atomFinset u ∈ A.Con := by
  cases hu with
  | left _ hA _ _ => exact hA
  | right _ hA _ _ => exact False.elim (hne hA)

theorem TreeCon_pairL_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (_hA : atomFinset u = ∅) : TreeCon A (pairLFinset u) := by
  cases hu with
  | left _ _ hL _ => rw [hL]; exact TreeCon_empty A
  | right _ _ hL _ => exact hL

theorem TreeCon_pairR_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (_hA : atomFinset u = ∅) : TreeCon A (pairRFinset u) := by
  cases hu with
  | left _ _ _ hR => rw [hR]; exact TreeCon_empty A
  | right _ _ _ hR => exact hR

theorem TreeCon_singleton (p : TreeToken α) : TreeCon A {p} := by
  induction p with
  | bot =>
    exact TreeCon.left _
      (by rw [atomFinset_singleton_bot]; exact A.con_empty)
      pairLFinset_singleton_bot pairRFinset_singleton_bot
  | atom x =>
    exact TreeCon.left _
      (by rw [atomFinset_singleton_atom]; exact A.con_sing x)
      (pairLFinset_singleton_atom x) (pairRFinset_singleton_atom x)
  | pairL t ih =>
    exact TreeCon.right _
      (atomFinset_singleton_pairL t)
      (by rw [pairLFinset_singleton_pairL]; exact ih)
      (by rw [pairRFinset_singleton_pairL]; exact TreeCon_empty A)
  | pairR t ih =>
    exact TreeCon.right _
      (atomFinset_singleton_pairR t)
      (by rw [pairLFinset_singleton_pairR]; exact TreeCon_empty A)
      (by rw [pairRFinset_singleton_pairR]; exact ih)

theorem TreeEntPayload_of_mem {u : Finset (TreeToken α)} {p : TreeToken α}
    (hu : TreeCon A u) (hp : p ∈ u) : TreeEntPayload A u p := by
  induction p generalizing u with
  | bot => exact trivial
  | atom x =>
    have hx : x ∈ atomFinset u := mem_atomFinset.2 hp
    exact ⟨Finset.ne_empty_of_mem hx,
      A.ent_refl (TreeCon_atom_con_of_atoms A hu (Finset.ne_empty_of_mem hx)) hx⟩
  | pairL t ih =>
    have ht : t ∈ pairLFinset u := mem_pairLFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon_atoms_empty_of_right A hu (Or.inl hne)
    exact ⟨hAt, hne, ⟨TreeCon_pairL_of_right A hu hAt,
      ih (TreeCon_pairL_of_right A hu hAt) ht⟩, TreeCon_pairR_of_right A hu hAt⟩
  | pairR t ih =>
    have ht : t ∈ pairRFinset u := mem_pairRFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon_atoms_empty_of_right A hu (Or.inr hne)
    exact ⟨hAt, hne, ⟨TreeCon_pairR_of_right A hu hAt,
      ih (TreeCon_pairR_of_right A hu hAt) ht⟩, TreeCon_pairL_of_right A hu hAt⟩

theorem TreeEnt_of_mem {u : Finset (TreeToken α)} {p : TreeToken α}
    (hu : TreeCon A u) (hp : p ∈ u) : TreeEnt A u p :=
  ⟨hu, TreeEntPayload_of_mem A hu hp⟩

theorem TreeCon_insert_of_ent {u : Finset (TreeToken α)} {p : TreeToken α}
    (h : TreeEnt A u p) : TreeCon A (insert p u) := by
  induction p generalizing u with
  | bot =>
    rcases h with ⟨hu, _⟩
    cases hu with
    | left _ hA hL hR =>
      exact TreeCon.left _
        (by rw [atomFinset_insert_bot]; exact hA)
        (by rw [pairLFinset_insert_bot]; exact hL)
        (by rw [pairRFinset_insert_bot]; exact hR)
    | right _ hA hL hR =>
      exact TreeCon.right _
        (by rw [atomFinset_insert_bot]; exact hA)
        (by rw [pairLFinset_insert_bot]; exact hL)
        (by rw [pairRFinset_insert_bot]; exact hR)
  | atom x =>
    rcases h with ⟨hu, hne, hA⟩
    have hLR := TreeCon_pairs_empty_of_left A hu hne
    exact TreeCon.left _
      (by rw [atomFinset_insert_atom]; exact A.ent_con hA)
      (by rw [pairLFinset_insert_atom]; exact hLR.1)
      (by rw [pairRFinset_insert_atom]; exact hLR.2)
  | pairL t ih =>
    rcases h with ⟨_, hAt, _, hEntL, hConR⟩
    exact TreeCon.right _
      (by rw [atomFinset_insert_pairL]; exact hAt)
      (by rw [pairLFinset_insert_pairL]; exact ih hEntL)
      (by rw [pairRFinset_insert_pairL]; exact hConR)
  | pairR t ih =>
    rcases h with ⟨_, hAt, _, hEntR, hConL⟩
    exact TreeCon.right _
      (by rw [atomFinset_insert_pairR]; exact hAt)
      (by rw [pairLFinset_insert_pairR]; exact hConL)
      (by rw [pairRFinset_insert_pairR]; exact ih hEntR)

theorem TreeEntPayload_trans {u v : Finset (TreeToken α)} {c : TreeToken α}
    (hv : TreeCon A v) (hu : TreeCon A u)
    (hEnts : ∀ y ∈ u, TreeEnt A v y) (hPay : TreeEntPayload A u c) :
    TreeEntPayload A v c := by
  induction c generalizing u v with
  | bot => exact trivial
  | atom x =>
    rcases hPay with ⟨hne, hA⟩
    have hlft : ∀ y ∈ atomFinset u, A.Ent (atomFinset v) y := by
      intro y hy
      exact (hEnts _ (mem_atomFinset.1 hy)).2.2
    have hne' : atomFinset v ≠ ∅ := by
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_atomFinset.1 hy)).2.1
    exact ⟨hne', A.ent_trans (TreeCon_atom_con_of_atoms A hv hne')
      (TreeCon_atom_con_of_atoms A hu hne) hlft hA⟩
  | pairL t ih =>
    rcases hPay with ⟨hAt, hne, ⟨hConL, hPayL⟩, _⟩
    have hAtv : atomFinset v = ∅ := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_pairLFinset.1 hs)).2.1
    have hne' : pairLFinset v ≠ ∅ := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_pairLFinset.1 hs)).2.2.1
    have hEntsL : ∀ y ∈ pairLFinset u, TreeEnt A (pairLFinset v) y := by
      intro y hy
      have hEy := hEnts _ (mem_pairLFinset.1 hy)
      exact ⟨hEy.2.2.2.1.1, hEy.2.2.2.1.2⟩
    have hConRv : TreeCon A (pairRFinset v) := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_pairLFinset.1 hs)).2.2.2.2
    refine ⟨hAtv, hne', ⟨TreeCon_pairL_of_right A hv hAtv, ?_⟩, hConRv⟩
    exact ih (TreeCon_pairL_of_right A hv hAtv) hConL hEntsL hPayL
  | pairR t ih =>
    rcases hPay with ⟨hAt, hne, ⟨hConR, hPayR⟩, _⟩
    have hAtv : atomFinset v = ∅ := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_pairRFinset.1 hs)).2.1
    have hne' : pairRFinset v ≠ ∅ := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_pairRFinset.1 hs)).2.2.1
    have hEntsR : ∀ y ∈ pairRFinset u, TreeEnt A (pairRFinset v) y := by
      intro y hy
      have hEy := hEnts _ (mem_pairRFinset.1 hy)
      exact ⟨hEy.2.2.2.1.1, hEy.2.2.2.1.2⟩
    have hConLv : TreeCon A (pairLFinset v) := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_pairRFinset.1 hs)).2.2.2.2
    refine ⟨hAtv, hne', ⟨TreeCon_pairR_of_right A hv hAtv, ?_⟩, hConLv⟩
    exact ih (TreeCon_pairR_of_right A hv hAtv) hConR hEntsR hPayR

theorem TreeEnt_trans {u v : Finset (TreeToken α)} {c : TreeToken α}
    (hv : TreeCon A v) (hu : TreeCon A u)
    (hEnts : ∀ y ∈ u, TreeEnt A v y) (hEntc : TreeEnt A u c) :
    TreeEnt A v c :=
  ⟨hv, TreeEntPayload_trans A hv hu hEnts hEntc.2⟩

theorem TreeCon_subset {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    ∀ {v}, v ⊆ u → TreeCon A v := by
  induction hu with
  | left u hA hL hR =>
    intro v hv
    refine TreeCon.left v (A.con_subset hA (atomFinset_mono hv)) ?_ ?_
    · exact Finset.Subset.antisymm
        (fun t ht => by
          have : t ∈ pairLFinset u := pairLFinset_mono hv ht
          rw [hL] at this; exact False.elim (Finset.notMem_empty t this))
        (Finset.empty_subset _)
    · exact Finset.Subset.antisymm
        (fun t ht => by
          have : t ∈ pairRFinset u := pairRFinset_mono hv ht
          rw [hR] at this; exact False.elim (Finset.notMem_empty t this))
        (Finset.empty_subset _)
  | right u hA hL hR ihL ihR =>
    intro v hv
    refine TreeCon.right v
      (Finset.Subset.antisymm
        (fun x hx => by
          have : x ∈ atomFinset u := atomFinset_mono hv hx
          rw [hA] at this; exact False.elim (Finset.notMem_empty x this))
        (Finset.empty_subset _))
      (ihL (pairLFinset_mono hv)) (ihR (pairRFinset_mono hv))

/-- **Factoid 8.1.** Tree information system solving `T ≅ A + (T × T)` by construction. -/
def treeSystem : InfoSys (TreeToken α) where
  bot := treeBot
  Con := {u | TreeCon A u}
  Ent := TreeEnt A
  con_subset := fun hu hv => TreeCon_subset A hu hv
  con_sing := TreeCon_singleton A
  ent_con := fun h => TreeCon_insert_of_ent A h
  ent_bot := fun hu => ⟨hu, trivial⟩
  ent_refl := fun hu hp => TreeEnt_of_mem A hu hp
  ent_trans := fun hv hu hEnts hEntc => TreeEnt_trans A hv hu hEnts hEntc

/-! ## Domain equation

Scott secures `T ≅ A + (T × T)` by choosing tokens so that `T` is literally the
sum-of-product system. Here `TreeToken` is the inductive presentation of that
tagging (clauses (1)–(3)), and `TreeCon`/`TreeEnt` are the sum×product clauses
((4)–(12)). Unfolding compares with the official `sumSystem` / `productSystem`
carriers; `pairL bot` and `pairR bot` both land on the unique product bottom,
matching Scott’s single `(Δ,(Δ,Δ))`.
-/

/-- Unfold a tree token into the sum-of-product carrier. -/
def treeUnfold (t : TreeToken α) :
    SumToken α (ProdToken (treeSystem A) (treeSystem A)) :=
  match t with
  | .bot => .bot
  | .atom x => .left x
  | .pairL t => .right ⟨(t, treeBot), Or.inr rfl⟩
  | .pairR t => .right ⟨(treeBot, t), Or.inl rfl⟩

theorem treeUnfold_bot : treeUnfold A treeBot = SumToken.bot := rfl

theorem treeUnfold_atom (x : α) : treeUnfold A (.atom x) = SumToken.left x := rfl

/-- The right-hand side of the domain equation is the official sum of products. -/
def treeRhs : InfoSys (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  sumSystem A (productSystem (treeSystem A) (treeSystem A))

theorem treeRhs_eq_sum_product :
    treeRhs A = sumSystem A (productSystem (treeSystem A) (treeSystem A)) :=
  rfl

end InfoSys

end Scott1982
