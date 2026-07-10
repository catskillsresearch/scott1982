import Scott1982.Theorem72
import Scott1982.Factoid65
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Factoid 7.7 — cartesian closed structure (stretch goal)

**Scott 1982 (*Categories again*).** Props 6.2 and Theorem 7.2 (with unit `1` from
Factoid 6.5) show that information systems and approximable maps form a cartesian
closed category. This file packages the category and finite-product structure in
Mathlib, together with the exponential universal property as an `Equiv`
(`Hom(A ⊗ Y, Z) ≃ Hom(Y, A → Z)` via Scott curry after product symmetry).

A full Mathlib `MonoidalClosed` instance (via `Adjunction.adjunctionOfEquivRight`)
is the remaining packaging step; it needs left-naturality of `uncurryRight`.
-/

universe u

namespace Scott1982

open Scott1982.Constructive
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace InfoSys

/-! ## Bundled objects -/

/-- Bundled information system (object of the Scott category). -/
structure InfoSysObj : Type (u + 1) where
  Token : Type u
  [decEq : DecidableEq Token]
  sys : InfoSys Token

attribute [instance] InfoSysObj.decEq

namespace InfoSysObj

def prod (A B : InfoSysObj) : InfoSysObj where
  Token := ProdToken A.sys B.sys
  sys := productSystem A.sys B.sys

def exp (A B : InfoSysObj) : InfoSysObj where
  Token := FunToken A.sys B.sys
  sys := functionSystem A.sys B.sys

def unit : InfoSysObj where
  Token := PUnit
  sys := unitSystem

end InfoSysObj

/-! ## Diagrammatic composition (`f.acomp g` = apply `f` then `g` = `f ≫ g`) -/

namespace ApproximableMap

def acomp {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) : ApproximableMap A C :=
  ApproximableMap.comp g f

theorem acomp_toElement {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) (x : A.Element) :
    (acomp f g).toElement x = g.toElement (f.toElement x) :=
  comp_toElement g f x

theorem id_acomp {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : InfoSys α} {B : InfoSys β} (f : ApproximableMap A B) :
    acomp (idMap A) f = f :=
  (ext_iff_toElement _ _).2 fun x => by rw [acomp_toElement, idMap_toElement]

theorem acomp_id {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : InfoSys α} {B : InfoSys β} (f : ApproximableMap A B) :
    acomp f (idMap B) = f :=
  (ext_iff_toElement _ _).2 fun x => by rw [acomp_toElement, idMap_toElement]

theorem acomp_assoc {α β γ δ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ} {D : InfoSys δ}
    (f : ApproximableMap A B) (g : ApproximableMap B C) (h : ApproximableMap C D) :
    acomp (acomp f g) h = acomp f (acomp g h) :=
  (ext_iff_toElement _ _).2 fun x => by simp only [acomp_toElement]

def swapMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap (productSystem A B) (productSystem B A) :=
  pairMap B A (sndMap A B) (fstMap A B)

theorem acomp_swap_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    acomp (swapMap A B) (fstMap B A) = sndMap A B := by
  simp only [acomp, swapMap, comp_fstMap_pairMap]

theorem acomp_swap_snd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    acomp (swapMap A B) (sndMap B A) = fstMap A B := by
  simp only [acomp, swapMap, comp_sndMap_pairMap]

theorem swapMap_acomp_swapMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    acomp (swapMap A B) (swapMap B A) = idMap (productSystem A B) := by
  have hfst : acomp (acomp (swapMap A B) (swapMap B A)) (fstMap A B) = fstMap A B := by
    calc
      acomp (acomp (swapMap A B) (swapMap B A)) (fstMap A B)
          = acomp (swapMap A B) (acomp (swapMap B A) (fstMap A B)) := acomp_assoc _ _ _
      _ = acomp (swapMap A B) (sndMap B A) := by rw [acomp_swap_fst]
      _ = fstMap A B := acomp_swap_snd A B
  have hsnd : acomp (acomp (swapMap A B) (swapMap B A)) (sndMap A B) = sndMap A B := by
    calc
      acomp (acomp (swapMap A B) (swapMap B A)) (sndMap A B)
          = acomp (swapMap A B) (acomp (swapMap B A) (sndMap A B)) := acomp_assoc _ _ _
      _ = acomp (swapMap A B) (fstMap B A) := by rw [acomp_swap_snd]
      _ = sndMap A B := acomp_swap_fst A B
  exact (pairMap_unique A B (fstMap A B) (sndMap A B) _ hfst hsnd).trans
    (pairMap_unique A B (fstMap A B) (sndMap A B) (idMap _)
      (id_acomp _) (id_acomp _)).symm

theorem curry_uncurry {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)
    (k : ApproximableMap A (functionSystem B C)) :
    curryMap A B C (uncurryMap A B C k) = k :=
  Eq.symm (curryMap_unique A B C (uncurryMap A B C k) k rfl)

end ApproximableMap

open ApproximableMap

/-! ## Category -/

instance : Category.{u, u + 1} InfoSysObj.{u} where
  Hom A B := ApproximableMap A.sys B.sys
  id A := idMap A.sys
  comp f g := acomp f g
  id_comp := id_acomp
  comp_id := acomp_id
  assoc := acomp_assoc

/-! ## Finite products -/

def terminalLimitCone : LimitCone (Functor.empty.{0} InfoSysObj.{u}) where
  cone := asEmptyCone InfoSysObj.unit
  isLimit := IsTerminal.ofUniqueHom
    (fun (X : InfoSysObj.{u}) => constMap (A := X.sys) unitSystem.botElement)
    fun (_X : InfoSysObj.{u}) m => approxMap_to_unit_eq_const m

def productLimitCone (X Y : InfoSysObj.{u}) : LimitCone (pair X Y) where
  cone := BinaryFan.mk (P := InfoSysObj.prod X Y)
    (fstMap X.sys Y.sys) (sndMap X.sys Y.sys)
  isLimit := by
    refine BinaryFan.IsLimit.mk _
      (fun {T : InfoSysObj.{u}} (f : T ⟶ X) (g : T ⟶ Y) => pairMap X.sys Y.sys f g)
      ?_ ?_ ?_
    · intro T f g
      exact @comp_fstMap_pairMap X.Token Y.Token T.Token _ _ _
        X.sys Y.sys T.sys f g
    · intro T f g
      exact @comp_sndMap_pairMap X.Token Y.Token T.Token _ _ _
        X.sys Y.sys T.sys f g
    · intro T f g m hf hg
      exact @pairMap_unique X.Token Y.Token T.Token _ _ _
        X.sys Y.sys T.sys f g m hf hg

instance : CartesianMonoidalCategory.{u, u + 1} InfoSysObj.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts terminalLimitCone productLimitCone

theorem tensorObj_eq_prod (A Y : InfoSysObj.{u}) : A ⊗ Y = InfoSysObj.prod A Y := rfl

/-! ## Braided curry (Mathlib convention) -/

/-- `Hom(A ⊗ Y, Z) → Hom(Y, A → Z)` via Scott curry after swap. -/
def curryRight (A Y Z : InfoSysObj.{u}) (h : A ⊗ Y ⟶ Z) : Y ⟶ InfoSysObj.exp A Z :=
  curryMap Y.sys A.sys Z.sys (acomp (swapMap Y.sys A.sys) h)

/-- Inverse of `curryRight`. -/
def uncurryRight (A Y Z : InfoSysObj.{u}) (k : Y ⟶ InfoSysObj.exp A Z) : A ⊗ Y ⟶ Z :=
  acomp (swapMap A.sys Y.sys) (uncurryMap Y.sys A.sys Z.sys k)

theorem uncurryRight_curryRight (A Y Z : InfoSysObj.{u}) (h : A ⊗ Y ⟶ Z) :
    uncurryRight A Y Z (curryRight A Y Z h) = h := by
  simp only [uncurryRight, curryRight]
  have huc := uncurry_curryMap Y.sys A.sys Z.sys (acomp (swapMap Y.sys A.sys) h)
  calc
    acomp (swapMap A.sys Y.sys)
          (uncurryMap Y.sys A.sys Z.sys
            (curryMap Y.sys A.sys Z.sys (acomp (swapMap Y.sys A.sys) h)))
        = acomp (swapMap A.sys Y.sys) (acomp (swapMap Y.sys A.sys) h) := by rw [huc]
    _ = acomp (acomp (swapMap A.sys Y.sys) (swapMap Y.sys A.sys)) h :=
        (acomp_assoc _ _ _).symm
    _ = acomp (idMap (productSystem A.sys Y.sys)) h := by rw [swapMap_acomp_swapMap]
    _ = h := id_acomp _

theorem curryRight_uncurryRight (A Y Z : InfoSysObj.{u}) (k : Y ⟶ InfoSysObj.exp A Z) :
    curryRight A Y Z (uncurryRight A Y Z k) = k := by
  simp only [curryRight, uncurryRight]
  have hred :
      acomp (swapMap Y.sys A.sys)
        (acomp (swapMap A.sys Y.sys) (uncurryMap Y.sys A.sys Z.sys k)) =
        uncurryMap Y.sys A.sys Z.sys k := by
    calc
      acomp (swapMap Y.sys A.sys)
            (acomp (swapMap A.sys Y.sys) (uncurryMap Y.sys A.sys Z.sys k))
          = acomp (acomp (swapMap Y.sys A.sys) (swapMap A.sys Y.sys))
              (uncurryMap Y.sys A.sys Z.sys k) := (acomp_assoc _ _ _).symm
      _ = acomp (idMap (productSystem Y.sys A.sys))
              (uncurryMap Y.sys A.sys Z.sys k) := by rw [swapMap_acomp_swapMap]
      _ = uncurryMap Y.sys A.sys Z.sys k := id_acomp _
  refine Eq.trans (congrArg (curryMap Y.sys A.sys Z.sys) hred)
    (curry_uncurry Y.sys A.sys Z.sys k)

/-- Hom-set equivalence for the exponential (Scott curry after braiding). -/
def tensorExpEquiv (A : InfoSysObj.{u}) (Y Z : InfoSysObj.{u}) :
    (A ⊗ Y ⟶ Z) ≃ (Y ⟶ InfoSysObj.exp A Z) where
  toFun := curryRight A Y Z
  invFun := uncurryRight A Y Z
  left_inv := uncurryRight_curryRight A Y Z
  right_inv := curryRight_uncurryRight A Y Z

/-- `A ◁ f` is the pairing `⟨fst, snd ≫ f⟩`. -/
theorem tensorLeft_map_eq (A : InfoSysObj.{u}) {Y Y' : InfoSysObj.{u}} (f : Y ⟶ Y') :
    (tensorLeft A).map f =
      pairMap A.sys Y'.sys (fstMap A.sys Y.sys) (acomp (sndMap A.sys Y.sys) f) := by
  refine pairMap_unique A.sys Y'.sys
      (fstMap A.sys Y.sys) (acomp (sndMap A.sys Y.sys) f)
      ((tensorLeft A).map f) ?_ ?_
  · change ((tensorLeft A).map f) ≫ fstMap A.sys Y'.sys = fstMap A.sys Y.sys
    exact CartesianMonoidalCategory.whiskerLeft_fst (X := A) (Y := Y) (Z := Y') f
  · change ((tensorLeft A).map f) ≫ sndMap A.sys Y'.sys = sndMap A.sys Y.sys ≫ f
    exact CartesianMonoidalCategory.whiskerLeft_snd (X := A) (Y := Y) (Z := Y') f

end InfoSys

end Scott1982
