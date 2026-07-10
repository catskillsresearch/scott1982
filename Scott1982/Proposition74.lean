import Scott1982.Fixpoint
import Scott1982.Proposition54
import Scott1982.Proposition55
import Scott1982.Factoid33
import Scott1982.Factoid35

/-!
# Proposition 7.4 — Plotkin’s equational characterization of `fix`

**Scott 1982, Proposition 7.4.** The least fixed-point operator is uniquely
determined by:
(i) `fix_A : (A → A) → A` for every system `A`;
(ii) `fix(f) = f(fix(f))`;
(iii) `h(fix_A(f)) = fix_B(g)` whenever `h ∘ f = g ∘ h` and `h(⊥_A) = ⊥_B`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

/-- **Proposition 7.4(ii).** -/
theorem proposition_7_4_ii (f : ApproximableMap A A) :
    f.toElement (fixElement A f) = fixElement A f :=
  fixElement_fixed A f

theorem toElement_comp_fix_le (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h) :
    g.toElement (h.toElement (fixElement A f)) ≤ h.toElement (fixElement A f) := by
  have h1 : g.toElement (h.toElement (fixElement A f)) =
      h.toElement (f.toElement (fixElement A f)) := by
    rw [← comp_toElement, ← hcomm, comp_toElement]
  rw [h1, proposition_7_4_ii A f]

theorem fixElement_le_toElement_fix (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h) :
    fixElement B g ≤ h.toElement (fixElement A f) :=
  fixElement_le_of_pre_fixed B g (h.toElement (fixElement A f))
    (toElement_comp_fix_le A B f g h hcomm)

private theorem closure_empty_eq_bot :
    A.closure (∅ : Finset α) A.con_empty = A.botElement := by
  apply le_antisymm
  · intro a ha
    exact A.ent_trans (A.con_sing A.bot) A.con_empty (A.entSet_empty _) ha
  · intro a ha
    exact A.ent_trans A.con_empty (A.con_sing A.bot)
      (fun x hx => by
        have : x = A.bot := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_bot A.con_empty)
      ha

theorem fixChain_toElement_le_fix (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement)
    {w : Finset (FunToken A A)}
    (hw : ↑w ⊆ (approxMap_toElement A A f).carrier) {n : Nat} {u : Finset α}
    (hchain : FixChain A w n u) :
    h.toElement (A.closure u (fixChain_con A hchain)) ≤ fixElement B g := by
  induction n generalizing u with
  | zero =>
    have hu : u = ∅ := hchain
    subst hu
    simpa [closure_empty_eq_bot A, hstrict] using
      (botElement_le B (fixElement B g))
  | succ n ih =>
    obtain ⟨u0, hu0, hu0C, huC, hEnt⟩ := hchain
    have ih' := ih hu0
    obtain ⟨_, s, hs, hIn, hOut⟩ := hEnt
    have hps : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq => by
      simpa [mem_approxMap_toElement] using hw (Finset.mem_coe.2 (hs hq))
    have hin : funInputUnion A A s ∈ A.Con :=
      A.con_subset
        (proposition_2_3_ii A hu0C (entSet_inputUnion_of_ent A A hIn))
        (subset_funion_right _ _)
    have hrel : f.rel (funInputUnion A A s) (funOutputUnion A A s) :=
      rel_input_output_union A A f s hps hin
    have hrel' : f.rel u0 (funOutputUnion A A s) :=
      f.mono hrel (entSet_inputUnion_of_ent A A hIn)
        (proposition_2_3_iii A (f.rel_cod hrel)) hu0C (f.rel_cod hrel)
    have hrel'' : f.rel u0 u :=
      f.mono hrel' (proposition_2_3_iii A hu0C) hOut hu0C huC
    have huf : A.closure u huC ≤ f.toElement (A.closure u0 hu0C) := by
      intro a ha
      have hsub : ↑u ⊆ (f.toElement (A.closure u0 hu0C)).carrier := by
        intro b hb
        have hsing : f.rel u0 {b} :=
          f.mono hrel'' (proposition_2_3_iii A hu0C)
            (fun z hz => by
              rw [Finset.mem_singleton] at hz; subst hz
              exact A.ent_refl huC hb)
            hu0C (A.con_sing b)
        refine ⟨u0, fun z hz => A.subset_closure hu0C hz, hsing⟩
      exact (f.toElement (A.closure u0 hu0C)).closed u a hsub ha
    have hhuf : h.toElement (A.closure u huC) ≤
        h.toElement (f.toElement (A.closure u0 hu0C)) :=
      toElement_mono h huf
    have hcomm' : h.toElement (f.toElement (A.closure u0 hu0C)) =
        g.toElement (h.toElement (A.closure u0 hu0C)) := by
      rw [← comp_toElement, hcomm, comp_toElement]
    have hgle : g.toElement (h.toElement (A.closure u0 hu0C)) ≤
        g.toElement (fixElement B g) :=
      toElement_mono g ih'
    have hfixg : g.toElement (fixElement B g) = fixElement B g :=
      proposition_7_4_ii B g
    calc
      h.toElement (A.closure u huC) ≤ h.toElement (f.toElement (A.closure u0 hu0C)) := hhuf
      _ = g.toElement (h.toElement (A.closure u0 hu0C)) := hcomm'
      _ ≤ g.toElement (fixElement B g) := hgle
      _ = fixElement B g := hfixg

theorem toElement_fix_le_fixElement (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) ≤ fixElement B g := by
  intro Z ⟨u, hu, hrel⟩
  obtain ⟨w, hw, ⟨_, _, v0, hv0, hEnt⟩⟩ :=
    exists_rel_of_subset_image (fixMap A) (approxMap_toElement A A f) u hu
  obtain ⟨n, hn⟩ := hv0
  have hcl := fixChain_toElement_le_fix A B f g h hcomm hstrict hw hn
  have hv0C := fixChain_con A hn
  have hrel' : h.rel v0 {Z} :=
    h.mono hrel hEnt (proposition_2_3_iii B (h.rel_cod hrel)) hv0C (h.rel_cod hrel)
  have hZ : Z ∈ (h.toElement (A.closure v0 hv0C)).carrier :=
    ⟨v0, A.subset_closure hv0C, hrel'⟩
  exact hcl hZ

/-- **Proposition 7.4(iii).** Naturality of `fix` for strict commuting maps. -/
theorem proposition_7_4_iii (f : ApproximableMap A A) (g : ApproximableMap B B)
    (h : ApproximableMap A B)
    (hcomm : comp h f = comp g h)
    (hstrict : h.toElement A.botElement = B.botElement) :
    h.toElement (fixElement A f) = fixElement B g := by
  apply le_antisymm
  · exact toElement_fix_le_fixElement A B f g h hcomm hstrict
  · exact fixElement_le_toElement_fix A B f g h hcomm

/-- **Proposition 7.4.** Uniqueness via the Theorem 7.3 least-fixed-point property
(Plotkin’s (ii) is the fixed-point equation; leastness is 7.3(iii)). -/
theorem proposition_7_4_unique (f : ApproximableMap A A) (φ : A.Element)
    (hii : f.toElement φ = φ)
    (hleast : ∀ x : A.Element, f.toElement x ≤ x → φ ≤ x) :
    φ = fixElement A f :=
  fixElement_unique A f φ (le_of_eq hii) hleast

/-- Identity is strict, so 7.4(iii) specializes to a tautology on `fix` itself. -/
theorem idMap_botElement : (idMap A).toElement A.botElement = A.botElement :=
  idMap_toElement A A.botElement

end ApproximableMap

end InfoSys

end Scott1982
