import Scott1982.Proposition54

/-!
# Proposition 5.5 — composition of approximable mappings

**Scott 1982, Proposition 5.5.** `u (g ∘ f) w ↔ ∃ v, u f v ∧ v g w`, and
`(g ∘ f)(x) = g(f(x))`.
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}

/-- **Proposition 5.5(i).** Composition of approximable mappings. -/
def comp (g : ApproximableMap B C) (f : ApproximableMap A B) : ApproximableMap A C where
  rel u w := ∃ v, f.rel u v ∧ g.rel v w
  rel_dom := fun ⟨_, hf, _⟩ => f.rel_dom hf
  rel_cod := fun ⟨_, _, hg⟩ => g.rel_cod hg
  empty_rel := ⟨∅, f.empty_rel, g.empty_rel⟩
  union_right := by
    rintro u w w' ⟨v, hf, hg⟩ ⟨v', hf', hg'⟩
    -- Need common middle: use union_right on f to get u f (v ∪' v'), then g.
    have hfU : f.rel u (v ∪' v') := f.union_right hf hf'
    have hvU : v ∪' v' ∈ B.Con := f.rel_cod hfU
    have hEntv : B.EntSet (v ∪' v') v :=
      fun y hy => B.ent_refl hvU (subset_funion_left v v' hy)
    have hEntv' : B.EntSet (v ∪' v') v' :=
      fun y hy => B.ent_refl hvU (subset_funion_right v v' hy)
    have hg1 : g.rel (v ∪' v') w :=
      g.mono hg hEntv (proposition_2_3_iii C (g.rel_cod hg)) hvU (g.rel_cod hg)
    have hg2 : g.rel (v ∪' v') w' :=
      g.mono hg' hEntv' (proposition_2_3_iii C (g.rel_cod hg')) hvU (g.rel_cod hg')
    exact ⟨v ∪' v', hfU, g.union_right hg1 hg2⟩
  mono := by
    rintro u u' w w' ⟨v, hf, hg⟩ hEntu hEntw hu' hw'
    refine ⟨v, ?_, ?_⟩
    · exact f.mono hf hEntu (proposition_2_3_iii B (f.rel_cod hf)) hu' (f.rel_cod hf)
    · exact g.mono hg (proposition_2_3_iii B (f.rel_cod hf)) hEntw (f.rel_cod hf) hw'

/-- **Proposition 5.5(ii).** `(g ∘ f)(x) = g(f(x))`. -/
theorem comp_toElement (g : ApproximableMap B C) (f : ApproximableMap A B) (x : A.Element) :
    (comp g f).toElement x = g.toElement (f.toElement x) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨v, hf, hg⟩⟩
    -- Z ∈ g(f(x)): need ∃ v' ⊆ f(x), v' g {Z}. Have v with u f v and v g {Z}?
    -- hg : g.rel v w where w should be {Z}. Our rel is to w = {Z} from toElement def.
    -- Actually ⟨u, hu, hrel⟩ where hrel : ∃ v, f.rel u v ∧ g.rel v {Z}
    refine ⟨v, ?_, hg⟩
    intro b hb
    -- b ∈ v ⇒ need b ∈ f(x). Since u f v and u ⊆ x, use: u f {b} by mono, so b ∈ f(x).
    have hb' : b ∈ v := Finset.mem_coe.1 hb
    have hsing : f.rel u {b} :=
      f.mono hf (proposition_2_3_iii A (f.rel_dom hf))
        (fun z hz => by
          rw [Finset.mem_singleton] at hz; subst hz
          exact B.ent_refl (f.rel_cod hf) hb')
        (f.rel_dom hf) (B.con_sing b)
    exact ⟨u, hu, hsing⟩
  · intro Z ⟨v, hv, hg⟩
    -- Z ∈ g(f(x)) with v ⊆ f(x), v g {Z}.
    -- Need u ⊆ x with u (g∘f) {Z}. From v ⊆ f(x), get u with u f v (exists_rel).
    obtain ⟨u, hu, hf⟩ := exists_rel_of_subset_image f x v hv
    exact ⟨u, hu, ⟨v, hf, hg⟩⟩

end ApproximableMap

end InfoSys

end Scott1982
