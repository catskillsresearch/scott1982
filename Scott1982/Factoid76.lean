/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Scott1982.Theorem72
import Scott1982.Proposition56

/-!
# Factoid 7.6 — combinators as approximable operators

**Scott 1982 (*Higher-type functions and the combinators*).** Once function spaces
exist as domains, the familiar combinators become approximable operators:

* `const : B → (A → B)` with `const(b) = constMap b`
* `pair : (C → A) × (C → B) → (C → A × B)` with `pair(f, g) = ⟨f, g⟩`
* `comp : (B → C) × (A → B) → (A → C)` with `comp(g, f) = g ∘ f`

Each is obtained by currying a composite of `apply`, `fst`/`snd`, and `pair`
(already approximable), so approximability is immediate.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-! ## Helpers: pairing with projections -/

theorem pairMap_toElement_pairElements
    {X : InfoSys α} {Y : InfoSys β} {Z : InfoSys γ}
    (f : ApproximableMap Z X) (g : ApproximableMap Z Y) (z : Z.Element) :
    (pairMap X Y f g).toElement z =
      pairElements X Y (f.toElement z) (g.toElement z) := by
  refine element_eq_of_fst_snd X Y _ _ ?_ ?_
  · rw [← comp_toElement, comp_fstMap_pairMap, fstMap_pairElements]
  · rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]

theorem pairMap_comp_fst_snd_toElement
    {P : InfoSys α} {X : InfoSys β} {Y : InfoSys γ}
    (k : ApproximableMap P (functionSystem Y X))
    (p : P.Element) (y : Y.Element) :
    (pairMap (functionSystem Y X) Y (comp k (fstMap P Y)) (sndMap P Y)).toElement
      (pairElements P Y p y) =
      pairElements (functionSystem Y X) Y (k.toElement p) y := by
  refine element_eq_of_fst_snd (functionSystem Y X) Y _ _ ?_ ?_
  · rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
      fstMap_pairElements]
  · rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements, sndMap_pairElements]

/-! ## `const : B → (A → B)` -/

/-- **Factoid 7.6.** Operator `const : B → (A → B)`, as `curry fst`. -/
def constOp : ApproximableMap B (functionSystem A B) :=
  curryMap B A B (fstMap B A)

theorem constOp_uncurry : uncurryMap B A B (constOp A B) = fstMap B A := by
  simp only [constOp, uncurry_curryMap]

theorem constOp_toElement (b : B.Element) :
    (constOp A B).toElement b =
      approxMap_toElement A B (constMap (A := A) b) := by
  have huniq :
      element_toApproxMap A B ((constOp A B).toElement b) = constMap (A := A) b := by
    refine constMap_unique (A := A) b _ fun x => ?_
    have hpair := pairMap_comp_fst_snd_toElement (constOp A B) b x
    calc
      (element_toApproxMap A B ((constOp A B).toElement b)).toElement x
          = (uncurryMap B A B (constOp A B)).toElement (pairElements B A b x) := by
              simp only [uncurryMap, comp_toElement]
              rw [hpair, applyMap_toElement]
          _ = (fstMap B A).toElement (pairElements B A b x) := by rw [constOp_uncurry]
          _ = b := fstMap_pairElements B A b x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

/-! ## `pair : (C → A) × (C → B) → (C → A × B)` -/

/-- Uncurried pairing: `((C→A)×(C→B)) × C → A×B`. -/
def pairOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem C A) (functionSystem C B)) C)
    (productSystem A B) :=
  let P := productSystem (functionSystem C A) (functionSystem C B)
  pairMap A B
    (comp (applyMap (B := C) (C := A))
      (pairMap (functionSystem C A) C
        (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
        (sndMap P C)))
    (comp (applyMap (B := C) (C := B))
      (pairMap (functionSystem C B) C
        (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
        (sndMap P C)))

/-- **Factoid 7.6.** Operator `pair : (C → A) × (C → B) → (C → A × B)`. -/
def pairOp : ApproximableMap
    (productSystem (functionSystem C A) (functionSystem C B))
    (functionSystem C (productSystem A B)) :=
  curryMap (productSystem (functionSystem C A) (functionSystem C B)) C (productSystem A B)
    (pairOpUncurry A B C)

theorem pairOp_uncurry :
    uncurryMap (productSystem (functionSystem C A) (functionSystem C B)) C (productSystem A B)
      (pairOp A B C) =
      pairOpUncurry A B C := by
  simp only [pairOp, uncurry_curryMap]

theorem pairOpUncurry_toElement (f : ApproximableMap C A) (g : ApproximableMap C B)
    (x : C.Element) :
    (pairOpUncurry A B C).toElement
      (pairElements (productSystem (functionSystem C A) (functionSystem C B)) C
        (pairElements (functionSystem C A) (functionSystem C B)
          (approxMap_toElement C A f) (approxMap_toElement C B g))
        x) =
      (pairMap A B f g).toElement x := by
  let P := productSystem (functionSystem C A) (functionSystem C B)
  let fg := pairElements (functionSystem C A) (functionSystem C B)
      (approxMap_toElement C A f) (approxMap_toElement C B g)
  have hfst_arg :
      (pairMap (functionSystem C A) C
          (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
          (sndMap P C)).toElement
        (pairElements P C fg x) =
      pairElements (functionSystem C A) C (approxMap_toElement C A f) x := by
    refine element_eq_of_fst_snd (functionSystem C A) C _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem C A) C).toElement
            ((pairMap (functionSystem C A) C
                (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          approxMap_toElement C A f := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          fstMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem C A) C _ _).symm
    · have hL :
          (sndMap (functionSystem C A) C).toElement
            ((pairMap (functionSystem C A) C
                (comp (fstMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          x := by
        rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem C A) C _ _).symm
  have hsnd_arg :
      (pairMap (functionSystem C B) C
          (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
          (sndMap P C)).toElement
        (pairElements P C fg x) =
      pairElements (functionSystem C B) C (approxMap_toElement C B g) x := by
    refine element_eq_of_fst_snd (functionSystem C B) C _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem C B) C).toElement
            ((pairMap (functionSystem C B) C
                (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          approxMap_toElement C B g := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          sndMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem C B) C _ _).symm
    · have hL :
          (sndMap (functionSystem C B) C).toElement
            ((pairMap (functionSystem C B) C
                (comp (sndMap (functionSystem C A) (functionSystem C B)) (fstMap P C))
                (sndMap P C)).toElement
              (pairElements P C fg x)) =
          x := by
        rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem C B) C _ _).symm
  refine element_eq_of_fst_snd A B _ _ ?_ ?_
  · have L :
        (fstMap A B).toElement
          ((pairOpUncurry A B C).toElement (pairElements P C fg x)) =
        f.toElement x := by
      simp only [pairOpUncurry]
      rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, hfst_arg,
        applyMap_toElement, element_toApproxMap_approxMap_toElement]
    have R :
        (fstMap A B).toElement ((pairMap A B f g).toElement x) = f.toElement x := by
      rw [← comp_toElement, comp_fstMap_pairMap]
    exact L.trans R.symm
  · have L :
        (sndMap A B).toElement
          ((pairOpUncurry A B C).toElement (pairElements P C fg x)) =
        g.toElement x := by
      simp only [pairOpUncurry]
      rw [← comp_toElement, comp_sndMap_pairMap, comp_toElement, hsnd_arg,
        applyMap_toElement, element_toApproxMap_approxMap_toElement]
    have R :
        (sndMap A B).toElement ((pairMap A B f g).toElement x) = g.toElement x := by
      rw [← comp_toElement, comp_sndMap_pairMap]
    exact L.trans R.symm

theorem pairOp_toElement (f : ApproximableMap C A) (g : ApproximableMap C B) :
    (pairOp A B C).toElement
      (pairElements (functionSystem C A) (functionSystem C B)
        (approxMap_toElement C A f) (approxMap_toElement C B g)) =
      approxMap_toElement C (productSystem A B) (pairMap A B f g) := by
  let P := productSystem (functionSystem C A) (functionSystem C B)
  let fg := pairElements (functionSystem C A) (functionSystem C B)
      (approxMap_toElement C A f) (approxMap_toElement C B g)
  have huniq :
      element_toApproxMap C (productSystem A B) ((pairOp A B C).toElement fg) =
        pairMap A B f g := by
    refine (ext_iff_toElement _ _).2 fun x => ?_
    have hpair :=
      pairMap_comp_fst_snd_toElement (X := productSystem A B) (pairOp A B C) fg x
    calc
      (element_toApproxMap C (productSystem A B) ((pairOp A B C).toElement fg)).toElement x
          = (uncurryMap P C (productSystem A B) (pairOp A B C)).toElement
              (pairElements P C fg x) := by
              simp only [uncurryMap, comp_toElement]
              rw [hpair, applyMap_toElement]
          _ = (pairOpUncurry A B C).toElement (pairElements P C fg x) := by
              rw [pairOp_uncurry]
          _ = (pairMap A B f g).toElement x := pairOpUncurry_toElement A B C f g x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

/-! ## `comp : (B → C) × (A → B) → (A → C)` -/

/-- Uncurried composition: `((B→C)×(A→B)) × A → C`. -/
def compOpUncurry : ApproximableMap
    (productSystem (productSystem (functionSystem B C) (functionSystem A B)) A) C :=
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B
      (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
      (comp (applyMap (B := A) (C := B))
        (pairMap (functionSystem A B) A
          (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (sndMap Q A))))

/-- **Factoid 7.6.** Operator `comp : (B → C) × (A → B) → (A → C)`. -/
def compOp : ApproximableMap
    (productSystem (functionSystem B C) (functionSystem A B))
    (functionSystem A C) :=
  curryMap (productSystem (functionSystem B C) (functionSystem A B)) A C
    (compOpUncurry A B C)

theorem compOp_uncurry :
    uncurryMap (productSystem (functionSystem B C) (functionSystem A B)) A C (compOp A B C) =
      compOpUncurry A B C := by
  simp only [compOp, uncurry_curryMap]

theorem compOpUncurry_toElement (g : ApproximableMap B C) (f : ApproximableMap A B)
    (x : A.Element) :
    (compOpUncurry A B C).toElement
      (pairElements (productSystem (functionSystem B C) (functionSystem A B)) A
        (pairElements (functionSystem B C) (functionSystem A B)
          (approxMap_toElement B C g) (approxMap_toElement A B f))
        x) =
      (comp g f).toElement x := by
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  let gf := pairElements (functionSystem B C) (functionSystem A B)
      (approxMap_toElement B C g) (approxMap_toElement A B f)
  have hinner :
      (pairMap (functionSystem A B) A
          (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (sndMap Q A)).toElement
        (pairElements Q A gf x) =
      pairElements (functionSystem A B) A (approxMap_toElement A B f) x := by
    refine element_eq_of_fst_snd (functionSystem A B) A _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem A B) A).toElement
            ((pairMap (functionSystem A B) A
                (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (sndMap Q A)).toElement
              (pairElements Q A gf x)) =
          approxMap_toElement A B f := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          sndMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem A B) A _ _).symm
    · have hL :
          (sndMap (functionSystem A B) A).toElement
            ((pairMap (functionSystem A B) A
                (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (sndMap Q A)).toElement
              (pairElements Q A gf x)) =
          x := by
        rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem A B) A _ _).symm
  have hf :
      (comp (applyMap (B := A) (C := B))
        (pairMap (functionSystem A B) A
          (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (sndMap Q A))).toElement
        (pairElements Q A gf x) =
      f.toElement x := by
    rw [comp_toElement, hinner, applyMap_toElement, element_toApproxMap_approxMap_toElement]
  have houter :
      (pairMap (functionSystem B C) B
          (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (comp (applyMap (B := A) (C := B))
            (pairMap (functionSystem A B) A
              (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
              (sndMap Q A)))).toElement
        (pairElements Q A gf x) =
      pairElements (functionSystem B C) B (approxMap_toElement B C g) (f.toElement x) := by
    refine element_eq_of_fst_snd (functionSystem B C) B _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (comp (applyMap (B := A) (C := B))
                  (pairMap (functionSystem A B) A
                    (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                    (sndMap Q A)))).toElement
              (pairElements Q A gf x)) =
          approxMap_toElement B C g := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          fstMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem B C) B _ _).symm
    · have hL :
          (sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (comp (applyMap (B := A) (C := B))
                  (pairMap (functionSystem A B) A
                    (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                    (sndMap Q A)))).toElement
              (pairElements Q A gf x)) =
          f.toElement x := by
        rw [← comp_toElement, comp_sndMap_pairMap, hf]
      exact hL.trans (sndMap_pairElements (functionSystem B C) B _ _).symm
  simp only [compOpUncurry, comp_toElement]
  rw [houter, applyMap_toElement, element_toApproxMap_approxMap_toElement]

theorem compOp_toElement (g : ApproximableMap B C) (f : ApproximableMap A B) :
    (compOp A B C).toElement
      (pairElements (functionSystem B C) (functionSystem A B)
        (approxMap_toElement B C g) (approxMap_toElement A B f)) =
      approxMap_toElement A C (comp g f) := by
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  let gf := pairElements (functionSystem B C) (functionSystem A B)
      (approxMap_toElement B C g) (approxMap_toElement A B f)
  have huniq :
      element_toApproxMap A C ((compOp A B C).toElement gf) = comp g f := by
    refine (ext_iff_toElement _ _).2 fun x => ?_
    have hpair := pairMap_comp_fst_snd_toElement (X := C) (compOp A B C) gf x
    calc
      (element_toApproxMap A C ((compOp A B C).toElement gf)).toElement x
          = (uncurryMap Q A C (compOp A B C)).toElement (pairElements Q A gf x) := by
              simp only [uncurryMap, comp_toElement]
              rw [hpair, applyMap_toElement]
          _ = (compOpUncurry A B C).toElement (pairElements Q A gf x) := by
              rw [compOp_uncurry]
          _ = (comp g f).toElement x := compOpUncurry_toElement A B C g f x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

end InfoSys

end Scott1982
