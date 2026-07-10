import Scott1982.FunctionSpace
import Scott1982.Theorem72
import Scott1982.Factoid25
import Scott1982.Factoid33
import Scott1982.Factoid35

/-!
# Factoid 7.5 — strict mappings, `strictify`, and BOOL

**Scott 1982 (after Prop 7.4).** Strict approximable maps; Scott’s `strict` /
`strictify` operator; flat BOOL via satisfaction.
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

end InfoSys

end Scott1982
