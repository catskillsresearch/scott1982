/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic

/-!
# Scott 1982, Theorem 7.2 (Palomar statement of record)

Ground truth for the wording is Scott 1982, Theorem 7.2
(`sources/Domains_for_Denotational_Semantics.pdf`). That theorem begins:

> If \(\mathbf{A}\), \(\mathbf{B}\), and \(\mathbf{C}\) are information systems,
> then so is \(\mathbf{A} \to \mathbf{B}\), and the approximable mappings
> \(f : \mathbf{A} \to \mathbf{B}\) are exactly the elements
> \(f \in |\mathbf{A} \to \mathbf{B}|\).

The compared declaration is that first sentence. Definition 7.1 supplies the
function-space information system: tokens are consistent pairs \((u,v)\),
consistency is Scott's 7.1(iii), and entailment is the constructive witness
form of 7.1(iv). The remaining `apply` / `curry` clauses of the same numbered
theorem are proved in `Scott1982/Theorem72.lean` and are not Comparator
targets.

This file imports Mathlib only. The choice-free `Finset` union `∪'` and
`decidableEq_finset` are restated here so the Challenge import closure
contains no project-local source. The proofs live in `Scott1982/*` and are
compared against this file by Comparator via `Solution.lean`.

The compared theorem is restricted to information systems whose token types
have `DecidableEq`, which is required to form the `Finset` operations used
in Definitions 2.1, 5.1, and 7.1.
-/

namespace Scott1982.Constructive

variable {α : Type*} [DecidableEq α]

/-- Choice-free commutativity of `insert` (mathlib's `Finset.insert_comm` is choice-tainted).
Needed to fold `insert` over a `Multiset`. -/
theorem insert_comm' (a b : α) (s : Finset α) :
    insert a (insert b s) = insert b (insert a s) := by
  sorry

instance instLeftCommutativeInsert :
    LeftCommutative (insert : α → Finset α → Finset α) := ⟨insert_comm'⟩

/-- Choice-free binary union of finite sets, obtained by folding `insert` over the second
argument's underlying multiset. Definitionally equal in content to `u ∪ v`, but — unlike
mathlib's `(· ∪ ·)` — free of any `Classical.choice` dependency. -/
def funion (u v : Finset α) : Finset α := Multiset.foldr insert u v.1

@[inherit_doc] infixl:65 " ∪' " => funion

omit [DecidableEq α] in
/-- If mutual subset holds, the finsets are equal. -/
theorem decidableEq_finset_eq_of_subset (s t : Finset α) (h : s ⊆ t ∧ t ⊆ s) : s = t := by
  sorry

omit [DecidableEq α] in
/-- Mutual subset is required for finset equality in this decidable instance. -/
theorem decidableEq_finset_false_of_ne (s t : Finset α) (h : ¬(s ⊆ t ∧ t ⊆ s)) (heq : s = t) :
    False := by
  sorry

/-- Choice-free decidable equality for `Finset`.
mathlib's `Finset.decidableEq` goes through `Multiset` quotients and pulls
`Classical.choice`; this version uses only decidable membership and subset. -/
def decidableEq_finset {α : Type*} [DecidableEq α] : DecidableEq (Finset α) :=
  fun s t =>
    if h : s ⊆ t ∧ t ⊆ s then
      isTrue (decidableEq_finset_eq_of_subset s t h)
    else
      isFalse (decidableEq_finset_false_of_ne s t h)

end Scott1982.Constructive

namespace Scott1982

open Scott1982.Constructive

universe u v

/-- **Definition 2.1 (Scott 1982).** An information system on tokens `α`. -/
structure InfoSys (α : Type u) [DecidableEq α] where
  bot : α
  Con : Set (Finset α)
  Ent : Finset α → α → Prop
  con_subset : ∀ {u v : Finset α}, u ∈ Con → v ⊆ u → v ∈ Con
  con_sing : ∀ a : α, {a} ∈ Con
  ent_con : ∀ {u : Finset α} {a : α}, Ent u a → insert a u ∈ Con
  ent_bot : ∀ {u : Finset α}, u ∈ Con → Ent u bot
  ent_refl : ∀ {u : Finset α} {a : α}, u ∈ Con → a ∈ u → Ent u a
  ent_trans : ∀ {u v : Finset α} {c : α},
    v ∈ Con → u ∈ Con → (∀ y ∈ u, Ent v y) → Ent u c → Ent v c

namespace InfoSys

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

/-- **Definition 3.1.** An element of `|A|`. -/
structure Element where
  carrier : Set α
  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con
  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier

/-- Extensional equality of elements. -/
theorem Element.ext {x y : sys.Element} (h : x.carrier = y.carrier) : x = y := by
  sorry

/-- Reflexivity of the carrier-inclusion order. -/
theorem element_le_refl (x : sys.Element) : x.carrier ⊆ x.carrier := by
  sorry

/-- Transitivity of the carrier-inclusion order. -/
theorem element_le_trans (x y z : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyz : y.carrier ⊆ z.carrier) :
    x.carrier ⊆ z.carrier := by
  sorry

/-- Antisymmetry of the carrier-inclusion order. -/
theorem element_le_antisymm (x y : sys.Element)
    (hxy : x.carrier ⊆ y.carrier) (hyx : y.carrier ⊆ x.carrier) :
    x = y := by
  sorry

instance : PartialOrder sys.Element where
  le x y := x.carrier ⊆ y.carrier
  le_refl := element_le_refl sys
  le_trans := element_le_trans sys
  le_antisymm := element_le_antisymm sys

/-- Empty set is consistent (subset of any singleton). -/
theorem con_empty : (∅ : Finset α) ∈ sys.Con := by
  sorry

/-- **Definition 2.2.** Set-level entailment. -/
def EntSet (u v : Finset α) : Prop := ∀ X ∈ v, sys.Ent u X

end InfoSys

namespace InfoSys

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- **Definition 5.1.** Approximable mapping. -/
structure ApproximableMap (A : InfoSys α) (B : InfoSys β) where
  rel : Finset α → Finset β → Prop
  rel_dom : ∀ {u v}, rel u v → u ∈ A.Con
  rel_cod : ∀ {u v}, rel u v → v ∈ B.Con
  empty_rel : rel ∅ ∅
  union_right : ∀ {u v v'}, rel u v → rel u v' → rel u (v ∪' v')
  mono : ∀ {u u' v v'},
    rel u v → A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con → rel u' v'

/-- Token type of the function space `A → B` (Scott 7.1(i)). -/
def FunToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : Finset α × Finset β // p.1 ∈ A.Con ∧ p.2 ∈ B.Con}

instance (A : InfoSys α) (B : InfoSys β) : DecidableEq (FunToken A B) :=
  fun p q =>
    match decidableEq_finset p.val.1 q.val.1, decidableEq_finset p.val.2 q.val.2 with
    | isTrue h1, isTrue h2 => isTrue (Subtype.ext (Prod.ext h1 h2))
    | isFalse n1, _ =>
        isFalse fun h => n1 (congrArg (fun r : FunToken A B => r.val.1) h)
    | isTrue _, isFalse n2 =>
        isFalse fun h => n2 (congrArg (fun r : FunToken A B => r.val.2) h)

variable (A : InfoSys α) (B : InfoSys β)

/-- The empty pair is a function-space token. -/
theorem funBot_property : (∅ : Finset α) ∈ A.Con ∧ (∅ : Finset β) ∈ B.Con := by
  sorry

/-- Left-commutativity of input-component union (needed to fold `funion`). -/
theorem funion_left_comm (a b c : Finset α) :
    a ∪' (b ∪' c) = b ∪' (a ∪' c) := by
  sorry

/-- Left-commutativity of output-component union (needed to fold `funion`). -/
theorem funion_left_comm' (a b c : Finset β) :
    a ∪' (b ∪' c) = b ∪' (a ∪' c) := by
  sorry

instance instLeftCommutativeFunInput :
    LeftCommutative fun p : FunToken A B => (funion p.val.1 : Finset α → Finset α) :=
  ⟨fun p q s => funion_left_comm p.val.1 q.val.1 s⟩

instance instLeftCommutativeFunOutput :
    LeftCommutative fun p : FunToken A B => (funion p.val.2 : Finset β → Finset β) :=
  ⟨fun p q s => funion_left_comm' p.val.2 q.val.2 s⟩

/-- Function-space bottom `Δ_{A→B} = (∅, ∅)` (Scott 7.1(ii)). -/
def funBot : FunToken A B :=
  ⟨(∅, ∅), funBot_property A B⟩

/-- Union of input components of a finite set of function-space tokens. -/
def funInputUnion (s : Finset (FunToken A B)) : Finset α :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.1) (∅ : Finset α) s.1

/-- Union of output components of a finite set of function-space tokens. -/
def funOutputUnion (s : Finset (FunToken A B)) : Finset β :=
  Multiset.foldr (fun p : FunToken A B => funion p.val.2) (∅ : Finset β) s.1

/-- Consistency for the function space (Scott 7.1(iii)). -/
def FunCon (w : Finset (FunToken A B)) : Prop :=
  ∀ s ⊆ w, funInputUnion A B s ∈ A.Con → funOutputUnion A B s ∈ B.Con

/-- Entailment for the function space (Scott 7.1(iv), constructive witness form). -/
def FunEnt (w : Finset (FunToken A B)) (p : FunToken A B) : Prop :=
  FunCon A B w ∧
    ∃ s ⊆ w, (∀ q ∈ s, A.EntSet p.val.1 q.val.1) ∧
      B.EntSet (funOutputUnion A B s) p.val.2

/-- Downward closure of function-space consistency. -/
theorem functionSystem_con_subset {w w' : Finset (FunToken A B)}
    (hw : FunCon A B w) (hw' : w' ⊆ w) : FunCon A B w' := by
  sorry

/-- Singletons are consistent in the function space. -/
theorem functionSystem_con_sing (p : FunToken A B) : FunCon A B {p} := by
  sorry

/-- Adding an entailed function-space token preserves consistency. -/
theorem functionSystem_ent_con {w : Finset (FunToken A B)} {p : FunToken A B}
    (hEnt : FunEnt A B w p) : FunCon A B (insert p w) := by
  sorry

/-- The function-space bottom is entailed by every consistent set. -/
theorem functionSystem_ent_bot {w : Finset (FunToken A B)} (hw : FunCon A B w) :
    FunEnt A B w (funBot A B) := by
  sorry

/-- Function-space entailment is reflexive on members. -/
theorem functionSystem_ent_refl {w : Finset (FunToken A B)} {p : FunToken A B}
    (hw : FunCon A B w) (hp : p ∈ w) : FunEnt A B w p := by
  sorry

/-- Function-space entailment is transitive. -/
theorem functionSystem_ent_trans {u v : Finset (FunToken A B)} {c : FunToken A B}
    (hv : FunCon A B v) (hu : FunCon A B u)
    (hEnts : ∀ y ∈ u, FunEnt A B v y) (hEnt : FunEnt A B u c) :
    FunEnt A B v c := by
  sorry

/-- **Definition 7.1.** The function-space information system `A → B`. -/
def functionSystem : InfoSys (FunToken A B) where
  bot := funBot A B
  Con := {w | FunCon A B w}
  Ent := FunEnt A B
  con_subset := functionSystem_con_subset A B
  con_sing := functionSystem_con_sing A B
  ent_con := functionSystem_ent_con A B
  ent_bot := functionSystem_ent_bot A B
  ent_refl := functionSystem_ent_refl A B
  ent_trans := functionSystem_ent_trans A B

/-- Consistency of a packaged function-space token. -/
theorem mkFunToken_property (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    u ∈ A.Con ∧ v ∈ B.Con := by
  sorry

/-- Package a consistent pair as a function-space token. -/
def mkFunToken (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    FunToken A B :=
  ⟨(u, v), mkFunToken_property A B u v hu hv⟩

/-- Consistency of the token-set of an approximable map. -/
theorem approxMap_toElement_consistent (f : ApproximableMap A B)
    (Y : Finset (FunToken A B))
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2}) :
    Y ∈ (functionSystem A B).Con := by
  sorry

/-- Deductive closure of the token-set of an approximable map. -/
theorem approxMap_toElement_closed (f : ApproximableMap A B)
    (Y : Finset (FunToken A B)) (p : FunToken A B)
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2})
    (hEnt : (functionSystem A B).Ent Y p) :
    p ∈ {q : FunToken A B | f.rel q.val.1 q.val.2} := by
  sorry

/-- Approximable map as an element of `|A → B|`. -/
def approxMap_toElement (f : ApproximableMap A B) : (functionSystem A B).Element where
  carrier := {p : FunToken A B | f.rel p.val.1 p.val.2}
  consistent := approxMap_toElement_consistent A B f
  closed := approxMap_toElement_closed A B f

/-- Domain of the relation recovered from a function-space element. -/
theorem element_toApproxMap_rel_dom (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      u ∈ A.Con :=
  fun ⟨hu, _, _⟩ => hu

/-- Codomain of the relation recovered from a function-space element. -/
theorem element_toApproxMap_rel_cod (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      v ∈ B.Con :=
  fun ⟨_, hv, _⟩ => hv

/-- The empty pair is related. -/
theorem element_toApproxMap_empty_rel (x : (functionSystem A B).Element) :
    ∃ (hu : (∅ : Finset α) ∈ A.Con) (hv : (∅ : Finset β) ∈ B.Con),
      mkFunToken A B ∅ ∅ hu hv ∈ x.carrier := by
  sorry

/-- Output-union of two related pairs remains related. -/
theorem element_toApproxMap_union_right (x : (functionSystem A B).Element) :
    ∀ {u : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      (∃ (hu : u ∈ A.Con) (hv : v' ∈ B.Con), mkFunToken A B u v' hu hv ∈ x.carrier) →
      ∃ (hu : u ∈ A.Con) (hv : v ∪' v' ∈ B.Con),
        mkFunToken A B u (v ∪' v') hu hv ∈ x.carrier := by
  sorry

/-- The recovered relation is monotone for entailment. -/
theorem element_toApproxMap_mono (x : (functionSystem A B).Element) :
    ∀ {u u' : Finset α} {v v' : Finset β},
      (∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier) →
      A.EntSet u' u → B.EntSet v v' → u' ∈ A.Con → v' ∈ B.Con →
      ∃ (hu : u' ∈ A.Con) (hv : v' ∈ B.Con),
        mkFunToken A B u' v' hu hv ∈ x.carrier := by
  sorry

/-- Element of `|A → B|` as an approximable map. -/
def element_toApproxMap (x : (functionSystem A B).Element) : ApproximableMap A B where
  rel u v := ∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier
  rel_dom := element_toApproxMap_rel_dom A B x
  rel_cod := element_toApproxMap_rel_cod A B x
  empty_rel := element_toApproxMap_empty_rel A B x
  union_right := element_toApproxMap_union_right A B x
  mono := element_toApproxMap_mono A B x

/-- Round-trip: every approximable map is recovered from its element. -/
theorem element_toApproxMap_approxMap_toElement (f : ApproximableMap A B) :
    element_toApproxMap A B (approxMap_toElement A B f) = f := by
  sorry

/-- Round-trip: every function-space element is recovered from its map. -/
theorem approxMap_toElement_element_toApproxMap (x : (functionSystem A B).Element) :
    approxMap_toElement A B (element_toApproxMap A B x) = x := by
  sorry

/-- **Theorem 7.2, first sentence (Scott 1982).** Approximable maps `A → B` are
exactly the elements of the Definition 7.1 function-space system `|A → B|`. -/
theorem theorem_7_2 {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    (∀ f : ApproximableMap A B,
      element_toApproxMap A B (approxMap_toElement A B f) = f) ∧
    (∀ x : (functionSystem A B).Element,
      approxMap_toElement A B (element_toApproxMap A B x) = x) := by
  sorry

end InfoSys

end Scott1982
