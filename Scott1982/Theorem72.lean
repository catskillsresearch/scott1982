import Scott1982.FunctionSpace
import Scott1982.Proposition53
import Scott1982.Proposition55
import Scott1982.Proposition62
import Scott1982.Factoid32

/-!
# Theorem 7.2 — function space elements, apply, and curry

**Scott 1982, Theorem 7.2.** Approximable maps `A → B` are exactly the elements of
`|A → B|`. There is approximable `apply : (B → C) × B → C` with `apply(g,y) = g(y)`,
and for each `h : A × B → C` a unique `curry h : A → (B → C)` satisfying
`h = apply ∘ ⟨(curry h) ∘ fst, snd⟩`.

(`A → B` as an `InfoSys` is already Def 7.1 / `functionSystem`.)
-/

namespace Scott1982

open Scott1982.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

/-- Package a consistent pair as a function-space token. -/
def mkFunToken (u : Finset α) (v : Finset β) (hu : u ∈ A.Con) (hv : v ∈ B.Con) :
    FunToken A B :=
  ⟨(u, v), ⟨hu, hv⟩⟩

theorem mkFunToken_eq (p : FunToken A B) :
    mkFunToken A B p.val.1 p.val.2 p.property.1 p.property.2 = p :=
  Subtype.ext rfl

private theorem funion_self (u : Finset α) : u ∪' u = u := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h <;> exact h
  · intro hx
    exact mem_funion.mpr (Or.inl hx)

private theorem funion_comm_β (u v : Finset β) : u ∪' v = v ∪' u := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)

theorem rel_input_output_union (f : ApproximableMap A B)
    (s : Finset (FunToken A B))
    (hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2)
    (hin : funInputUnion A B s ∈ A.Con) :
    f.rel (funInputUnion A B s) (funOutputUnion A B s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    exact f.empty_rel
  | insert q s' _hq ih =>
    have hrel' : ∀ r ∈ s', f.rel r.val.1 r.val.2 := fun r hr =>
      hrel r (Finset.mem_insert_of_mem hr)
    have hin' : funInputUnion A B s' ∈ A.Con :=
      A.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hrel' hin'
    have hqrel : f.rel q.val.1 q.val.2 := hrel q (Finset.mem_insert_self q s')
    have hinU : q.val.1 ∪' funInputUnion A B s' ∈ A.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_q : A.EntSet (q.val.1 ∪' funInputUnion A B s') q.val.1 :=
      fun x hx => A.ent_refl hinU (subset_funion_left _ _ hx)
    have hEnt_s : A.EntSet (q.val.1 ∪' funInputUnion A B s') (funInputUnion A B s') :=
      fun x hx => A.ent_refl hinU (subset_funion_right _ _ hx)
    have h1 : f.rel (q.val.1 ∪' funInputUnion A B s') q.val.2 :=
      f.mono hqrel hEnt_q (proposition_2_3_iii B q.property.2) hinU q.property.2
    have h2 : f.rel (q.val.1 ∪' funInputUnion A B s') (funOutputUnion A B s') :=
      f.mono ih' hEnt_s (proposition_2_3_iii B (f.rel_cod ih')) hinU (f.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact f.union_right h1 h2

namespace ApproximableMap

theorem funCon_of_approxMap (f : ApproximableMap A B) (w : Finset (FunToken A B))
    (hw : ∀ p ∈ w, f.rel p.val.1 p.val.2) : FunCon A B w :=
  fun s hs hin =>
    f.rel_cod (rel_input_output_union A B f s (fun q hq => hw q (hs hq)) hin)

/-- **Theorem 7.2.** Approximable map as an element of `|A → B|`. -/
def approxMap_toElement (f : ApproximableMap A B) : (functionSystem A B).Element where
  carrier := {p : FunToken A B | f.rel p.val.1 p.val.2}
  consistent := by
    intro Y hY
    exact funCon_of_approxMap A B f Y fun p hp => hY (Finset.mem_coe.2 hp)
  closed := by
    intro Y p hY hEnt
    obtain ⟨_hCon, s, hs, hEntIn, hEntOut⟩ := hEnt
    have hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq =>
      hY (Finset.mem_coe.2 (hs hq))
    have hin_s : funInputUnion A B s ∈ A.Con :=
      A.con_subset
        (proposition_2_3_ii A p.property.1 (entSet_inputUnion_of_ent A B hEntIn))
        (subset_funion_right _ _)
    have hIO := rel_input_output_union A B f s hrel hin_s
    have hU : f.rel p.val.1 (funOutputUnion A B s) :=
      f.mono hIO (entSet_inputUnion_of_ent A B hEntIn)
        (proposition_2_3_iii B (f.rel_cod hIO)) p.property.1 (f.rel_cod hIO)
    exact f.mono hU (proposition_2_3_iii A p.property.1) hEntOut p.property.1 p.property.2

theorem mem_approxMap_toElement (f : ApproximableMap A B) {p : FunToken A B} :
    p ∈ (approxMap_toElement A B f).carrier ↔ f.rel p.val.1 p.val.2 :=
  Iff.rfl

/-- **Theorem 7.2.** Element of `|A → B|` as an approximable map. -/
def element_toApproxMap (x : (functionSystem A B).Element) : ApproximableMap A B where
  rel u v := ∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier
  rel_dom := fun ⟨hu, _, _⟩ => hu
  rel_cod := fun ⟨_, hv, _⟩ => hv
  empty_rel := by
    refine ⟨A.con_empty, B.con_empty, ?_⟩
    change funBot A B ∈ x.carrier
    exact factoid_3_2 (functionSystem A B) x
  union_right := by
    rintro u v v' ⟨hu, hv, hp⟩ ⟨hu', hv', hq⟩
    have hvU : v ∪' v' ∈ B.Con := by
      have hCon : FunCon A B
          (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) := by
        apply x.consistent
        intro r hr
        rcases Finset.mem_insert.mp (Finset.mem_coe.1 hr) with rfl | hr
        · exact hq
        · have : r = mkFunToken A B u v hu hv := Finset.mem_singleton.mp hr
          subst this
          exact hp
      have hin : funInputUnion A B
          (insert (mkFunToken A B u v' hu' hv') {mkFunToken A B u v hu hv}) ∈ A.Con := by
        rw [funInputUnion_insert, funInputUnion_singleton]
        change u ∪' u ∈ A.Con
        rw [funion_self]
        exact hu
      have hout := hCon _ (Finset.Subset.refl _) hin
      rw [funOutputUnion_insert, funOutputUnion_singleton, funion_comm_β] at hout
      exact hout
    refine ⟨hu, hvU, ?_⟩
    let p := mkFunToken A B u v hu hv
    let q := mkFunToken A B u v' hu' hv'
    let r := mkFunToken A B u (v ∪' v') hu hvU
    let w : Finset (FunToken A B) := insert q {p}
    have hwsub : (↑w : Set _) ⊆ x.carrier := by
      intro t ht
      rcases Finset.mem_insert.mp (Finset.mem_coe.1 ht) with rfl | ht
      · exact hq
      · have : t = p := Finset.mem_singleton.mp ht
        subst this
        exact hp
    have hEnt : FunEnt A B w r := by
      refine ⟨x.consistent w hwsub, w, Finset.Subset.refl _, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact proposition_2_3_iii A hu'
        · have : t = p := Finset.mem_singleton.mp ht
          subst this
          exact proposition_2_3_iii A hu
      · have houtEq : funOutputUnion A B w = v' ∪' v := by
          simp only [w, q, p, funOutputUnion_insert, funOutputUnion_singleton, mkFunToken]
        rw [houtEq, funion_comm_β]
        exact proposition_2_3_iii B hvU
    exact x.closed w r hwsub hEnt
  mono := by
    rintro u u' v v' ⟨hu, hv, hp⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    let p := mkFunToken A B u v hu hv
    let r := mkFunToken A B u' v' hu' hv'
    have hwsub : (↑({p} : Finset (FunToken A B)) : Set _) ⊆ x.carrier := by
      intro t ht
      have : t = p := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
      subst this
      exact hp
    have hEnt : FunEnt A B {p} r := by
      refine ⟨x.consistent {p} hwsub, {p}, Finset.Subset.refl _, ?_, ?_⟩
      · intro t ht
        have : t = p := Finset.mem_singleton.mp ht
        subst this
        exact hEntu
      · rw [funOutputUnion_singleton]
        exact hEntv
    exact x.closed {p} r hwsub hEnt

theorem element_toApproxMap_approxMap_toElement (f : ApproximableMap A B) :
    element_toApproxMap A B (approxMap_toElement A B f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨hu, hv, hp⟩
    simpa [mem_approxMap_toElement, mkFunToken] using hp
  · intro hrel
    exact ⟨f.rel_dom hrel, f.rel_cod hrel, by
      simpa [mem_approxMap_toElement, mkFunToken] using hrel⟩

theorem approxMap_toElement_element_toApproxMap (x : (functionSystem A B).Element) :
    approxMap_toElement A B (element_toApproxMap A B x) = x := by
  apply le_antisymm
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2 at hp
    obtain ⟨_, _, hmem⟩ := hp
    simpa [mkFunToken_eq A B p] using hmem
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2
    refine ⟨p.property.1, p.property.2, ?_⟩
    simpa [mkFunToken_eq A B p] using hp

/-- **Theorem 7.2.** Approximable `apply : (B → C) × B → C`. -/
def applyMap : ApproximableMap (productSystem (functionSystem B C) B) C where
  rel s t :=
    ∃ (hs : ProdCon (functionSystem B C) B s) (ht : t ∈ C.Con),
      FunEnt B C (fstFinset (functionSystem B C) B s)
        (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht)
  rel_dom := fun ⟨hs, _, _⟩ => hs
  rel_cod := fun ⟨_, ht, _⟩ => ht
  empty_rel := by
    have hs : ProdCon (functionSystem B C) B ∅ :=
      ⟨by rw [fstFinset_empty]; exact (functionSystem B C).con_empty,
        by rw [sndFinset_empty]; exact B.con_empty⟩
    refine ⟨hs, C.con_empty, ?_⟩
    have hfst : fstFinset (functionSystem B C) B (∅ : Finset _) = ∅ := fstFinset_empty _ _
    have hsnd : sndFinset (functionSystem B C) B (∅ : Finset _) = ∅ := sndFinset_empty _ _
    simp only [hfst, hsnd]
    exact (functionSystem B C).ent_bot (functionSystem B C).con_empty
  union_right := by
    rintro s t t' ⟨hs, ht, hEntt⟩ ⟨_, ht', hEntt'⟩
    obtain ⟨hw, s1, hs1, hIn1, hOut1⟩ := hEntt
    obtain ⟨_, s2, hs2, hIn2, hOut2⟩ := hEntt'
    have hsub : s1 ∪' s2 ⊆ fstFinset (functionSystem B C) B s :=
      funion_subset_iff.mpr ⟨hs1, hs2⟩
    have hin : funInputUnion B C (s1 ∪' s2) ∈ B.Con := by
      rw [funInputUnion_funion]
      have hEntU : B.EntSet (sndFinset (functionSystem B C) B s)
          (funInputUnion B C s1 ∪' funInputUnion B C s2) :=
        proposition_2_3_vi B
          (entSet_inputUnion_of_ent B C hIn1)
          (entSet_inputUnion_of_ent B C hIn2)
      exact B.con_subset (proposition_2_3_ii B hs.2 hEntU) (subset_funion_right _ _)
    have hout : funOutputUnion B C s1 ∪' funOutputUnion B C s2 ∈ C.Con := by
      have := hw _ hsub hin
      rwa [funOutputUnion_funion] at this
    have htt' : t ∪' t' ∈ C.Con := by
      have hEntt2 : C.EntSet (funOutputUnion B C s1 ∪' funOutputUnion B C s2) (t ∪' t') :=
        proposition_2_3_vi C
          (proposition_2_3_v C (C.con_subset hout (subset_funion_left _ _)) hout
            (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
          (proposition_2_3_v C (C.con_subset hout (subset_funion_right _ _)) hout
            (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))
      exact C.con_subset (proposition_2_3_ii C hout hEntt2) (subset_funion_right _ _)
    refine ⟨hs, htt', hw, s1 ∪' s2, hsub, ?_, ?_⟩
    · intro q hq
      rcases mem_funion.mp hq with hq | hq
      · exact hIn1 q hq
      · exact hIn2 q hq
    · rw [funOutputUnion_funion]
      exact proposition_2_3_vi C
        (proposition_2_3_v C (C.con_subset hout (subset_funion_left _ _)) hout
          (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
        (proposition_2_3_v C (C.con_subset hout (subset_funion_right _ _)) hout
          (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))
  mono := by
    rintro s s' t t' ⟨hs, ht, hEnt⟩ hEnts hEntt hs' ht'
    refine ⟨hs', ht', ?_⟩
    have hfst := entSet_fst_of_prodEntSet (functionSystem B C) B hEnts
    have hsnd := entSet_snd_of_prodEntSet (functionSystem B C) B hEnts
    have htok :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s)
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) := hEnt
    have hmid :
        (functionSystem B C).Ent (fstFinset (functionSystem B C) B s')
          (mkFunToken B C (sndFinset (functionSystem B C) B s) t hs.2 ht) :=
      (functionSystem B C).ent_trans hs'.1 hs.1 (fun y hy => hfst y hy) htok
    obtain ⟨hw', s1, hs1, hIn1, hOut1⟩ := hmid
    have hIn1' : ∀ q ∈ s1, B.EntSet (sndFinset (functionSystem B C) B s') q.val.1 :=
      fun q hq => proposition_2_3_iv B hs'.2 hs.2 hsnd (hIn1 q hq)
    have hin : funInputUnion B C s1 ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hs'.2 (entSet_inputUnion_of_ent B C hIn1'))
        (subset_funion_right _ _)
    have hout : funOutputUnion B C s1 ∈ C.Con := hw' s1 hs1 hin
    refine ⟨hw', s1, hs1, hIn1', ?_⟩
    exact proposition_2_3_iv C hout ht hOut1 hEntt

/-! ## Curry helpers -/

/-- Product token set encoding a pair of consistent sets `(u, v)`. -/
def liftPair (u : Finset α) (v : Finset β) : Finset (ProdToken A B) :=
  liftLeft A B u ∪' liftRight A B v

theorem liftLeft_funion (u u' : Finset α) :
    liftLeft A B (u ∪' u') = liftLeft A B u ∪' liftLeft A B u' := by
  ext p
  constructor
  · intro hp
    rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
    rcases mem_funion.mp hx with hx | hx
    · exact mem_funion.mpr (Or.inl ((mem_liftLeft A B).2 ⟨x, hx, rfl⟩))
    · exact mem_funion.mpr (Or.inr ((mem_liftLeft A B).2 ⟨x, hx, rfl⟩))
  · intro hp
    rcases mem_funion.mp hp with hp | hp
    · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
      exact (mem_liftLeft A B).2 ⟨x, mem_funion.mpr (Or.inl hx), rfl⟩
    · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
      exact (mem_liftLeft A B).2 ⟨x, mem_funion.mpr (Or.inr hx), rfl⟩

theorem liftRight_funion (v v' : Finset β) :
    liftRight A B (v ∪' v') = liftRight A B v ∪' liftRight A B v' := by
  ext p
  constructor
  · intro hp
    rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
    rcases mem_funion.mp hy with hy | hy
    · exact mem_funion.mpr (Or.inl ((mem_liftRight A B).2 ⟨y, hy, rfl⟩))
    · exact mem_funion.mpr (Or.inr ((mem_liftRight A B).2 ⟨y, hy, rfl⟩))
  · intro hp
    rcases mem_funion.mp hp with hp | hp
    · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
      exact (mem_liftRight A B).2 ⟨y, mem_funion.mpr (Or.inl hy), rfl⟩
    · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
      exact (mem_liftRight A B).2 ⟨y, mem_funion.mpr (Or.inr hy), rfl⟩

theorem ProdCon_liftPair {u : Finset α} {v : Finset β}
    (hu : u ∈ A.Con) (hv : v ∈ B.Con) : ProdCon A B (liftPair A B u v) := by
  constructor
  · unfold liftPair
    rw [fstFinset_funion, fstFinset_liftLeft]
    have hEnt : A.EntSet u (fstFinset A B (liftRight A B v)) := fun x hx => by
      have : x = A.bot := Finset.mem_singleton.mp (fstFinset_liftRight A B v hx)
      subst this
      exact A.ent_bot hu
    exact proposition_2_3_ii A hu hEnt
  · unfold liftPair
    rw [sndFinset_funion, sndFinset_liftRight]
    have hEnt : B.EntSet v (sndFinset A B (liftLeft A B u)) := fun y hy => by
      have : y = B.bot := Finset.mem_singleton.mp (sndFinset_liftLeft A B u hy)
      subst this
      exact B.ent_bot hv
    have h := proposition_2_3_ii B hv hEnt
    rwa [funion_comm_β] at h

theorem fstFinset_liftPair (u : Finset α) (v : Finset β) :
    fstFinset A B (liftPair A B u v) =
      u ∪' fstFinset A B (liftRight A B v) := by
  unfold liftPair
  rw [fstFinset_funion, fstFinset_liftLeft]

theorem sndFinset_liftPair (u : Finset α) (v : Finset β) :
    sndFinset A B (liftPair A B u v) =
      sndFinset A B (liftLeft A B u) ∪' v := by
  unfold liftPair
  rw [sndFinset_funion, sndFinset_liftRight]

/-- Product entailment between lifted pairs from component entailments. -/
theorem entSet_liftPair {u u' : Finset α} {v v' : Finset β}
    (hu' : u' ∈ A.Con) (hv' : v' ∈ B.Con)
    (hEntu : A.EntSet u' u) (hEntv : B.EntSet v' v) :
    (productSystem A B).EntSet (liftPair A B u' v') (liftPair A B u v) := by
  intro p hp
  have hCon : ProdCon A B (liftPair A B u' v') := ProdCon_liftPair A B hu' hv'
  unfold liftPair at hp
  rcases mem_funion.mp hp with hp | hp
  · rcases (mem_liftLeft A B).1 hp with ⟨x, hx, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      have hsub : u' ⊆ fstFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [fstFinset_liftPair]
        exact subset_funion_left _ _ hz
      exact A.ent_trans hCon.1 hu'
        (fun z hz => A.ent_refl hCon.1 (hsub hz)) (hEntu x hx)
    · intro _
      exact B.ent_bot hCon.2
  · rcases (mem_liftRight A B).1 hp with ⟨y, hy, rfl⟩
    refine ⟨hCon, ?_, ?_⟩
    · intro _
      exact A.ent_bot hCon.1
    · intro _
      have hsub : v' ⊆ sndFinset A B (liftPair A B u' v') := by
        intro z hz
        rw [sndFinset_liftPair]
        exact subset_funion_right _ _ hz
      exact B.ent_trans hCon.2 hv'
        (fun z hz => B.ent_refl hCon.2 (hsub hz)) (hEntv y hy)

/-- Combine pointwise `h`-relations along a finite set of function tokens. -/
theorem rel_of_funTokens (h : ApproximableMap (productSystem A B) C)
    (u : Finset α) (hu : u ∈ A.Con) (t : Finset (FunToken B C))
    (hps : ∀ p ∈ t, h.rel (liftPair A B u p.val.1) p.val.2)
    (hin : funInputUnion B C t ∈ B.Con) :
    h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) := by
  induction t using Finset.induction_on with
  | empty =>
    rw [funInputUnion_empty, funOutputUnion_empty]
    have hdom : liftPair A B u ∅ ∈ (productSystem A B).Con :=
      ProdCon_liftPair A B hu B.con_empty
    exact h.mono h.empty_rel
      ((productSystem A B).entSet_empty _)
      (C.entSet_empty ∅) hdom C.con_empty
  | insert p t' hpnot ih =>
    have hps' : ∀ q ∈ t', h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (Finset.mem_insert_of_mem hq)
    have hin' : funInputUnion B C t' ∈ B.Con :=
      B.con_subset hin (by
        rw [funInputUnion_insert]
        exact subset_funion_right _ _)
    have ih' := ih hps' hin'
    have hp : h.rel (liftPair A B u p.val.1) p.val.2 :=
      hps p (Finset.mem_insert_self p t')
    have hinU : p.val.1 ∪' funInputUnion B C t' ∈ B.Con := by
      rwa [funInputUnion_insert] at hin
    have hEnt_p : B.EntSet (p.val.1 ∪' funInputUnion B C t') p.val.1 :=
      fun y hy => B.ent_refl hinU (subset_funion_left _ _ hy)
    have hEnt_t : B.EntSet (p.val.1 ∪' funInputUnion B C t') (funInputUnion B C t') :=
      fun y hy => B.ent_refl hinU (subset_funion_right _ _ hy)
    have hdomU : liftPair A B u (p.val.1 ∪' funInputUnion B C t') ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hu hinU
    have h1 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t')) p.val.2 :=
      h.mono hp
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_p)
        (proposition_2_3_iii C (h.rel_cod hp)) hdomU (h.rel_cod hp)
    have h2 : h.rel (liftPair A B u (p.val.1 ∪' funInputUnion B C t'))
        (funOutputUnion B C t') :=
      h.mono ih'
        (entSet_liftPair A B hu hinU (proposition_2_3_iii A hu) hEnt_t)
        (proposition_2_3_iii C (h.rel_cod ih')) hdomU (h.rel_cod ih')
    rw [funInputUnion_insert, funOutputUnion_insert]
    exact h.union_right h1 h2

theorem funCon_of_curry_pointwise (h : ApproximableMap (productSystem A B) C)
    {u : Finset α} (hu : u ∈ A.Con) {s : Finset (FunToken B C)}
    (hps : ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2) :
    FunCon B C s :=
  fun t ht hin =>
    h.rel_cod (rel_of_funTokens A B C h u hu t (fun p hp => hps p (ht hp)) hin)

/-- **Theorem 7.2.** Approximable `curry h : A → (B → C)`. -/
def curryMap (h : ApproximableMap (productSystem A B) C) :
    ApproximableMap A (functionSystem B C) where
  rel u s :=
    u ∈ A.Con ∧ ∀ p ∈ s, h.rel (liftPair A B u p.val.1) p.val.2
  rel_dom hrel := hrel.1
  rel_cod hrel := funCon_of_curry_pointwise A B C h hrel.1 hrel.2
  empty_rel := ⟨A.con_empty, fun _ hp => False.elim (Finset.notMem_empty _ hp)⟩
  union_right := by
    rintro u s s' ⟨hu, hps⟩ ⟨_, hps'⟩
    refine ⟨hu, ?_⟩
    intro p hp
    rcases mem_funion.mp hp with hp | hp
    · exact hps p hp
    · exact hps' p hp
  mono := by
    rintro u u' s s' ⟨hu, hps⟩ hEntu hEnts hu' hs'
    refine ⟨hu', ?_⟩
    intro p hp
    -- FunEnt s p from EntSet
    have hEntp : FunEnt B C s p := hEnts p hp
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEntp
    have hps_t : ∀ q ∈ t, h.rel (liftPair A B u q.val.1) q.val.2 :=
      fun q hq => hps q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B p.property.1 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hmid : h.rel (liftPair A B u (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h u hu t hps_t hin
    have hmid' : h.rel (liftPair A B u' p.val.1) (funOutputUnion B C t) :=
      h.mono hmid
        (entSet_liftPair A B hu' p.property.1 hEntu
          (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii C (h.rel_cod hmid))
        (ProdCon_liftPair A B hu' p.property.1) (h.rel_cod hmid)
    exact h.mono hmid'
      (proposition_2_3_iii (productSystem A B) (ProdCon_liftPair A B hu' p.property.1))
      hOut (ProdCon_liftPair A B hu' p.property.1) p.property.2

/-- Product element `⟨x, y⟩` assembled from the two projections. -/
def pairElements (x : A.Element) (y : B.Element) : (productSystem A B).Element where
  carrier := {p : ProdToken A B |
    (p.val.2 = B.bot → p.val.1 ∈ x.carrier) ∧ (p.val.1 = A.bot → p.val.2 ∈ y.carrier)}
  consistent := by
    intro Y hY
    refine ⟨?_, ?_⟩
    · have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).1 hbot
      exact x.consistent _ hsub
    · have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
        exact (hY (Finset.mem_coe.2 hp)).2 hbot
      exact y.consistent _ hsub
  closed := by
    intro Y p hY hEnt
    obtain ⟨hCon, hL, hR⟩ := hEnt
    refine ⟨?_, ?_⟩
    · intro hbot
      have hEntA : A.Ent (fstFinset A B Y) p.val.1 := hL hbot
      have hsub : ↑(fstFinset A B Y) ⊆ x.carrier := by
        intro a ha
        rcases (mem_fstFinset A B).1 ha with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).1 hbot'
      exact x.closed _ _ hsub hEntA
    · intro hbot
      have hEntB : B.Ent (sndFinset A B Y) p.val.2 := hR hbot
      have hsub : ↑(sndFinset A B Y) ⊆ y.carrier := by
        intro b hb
        rcases (mem_sndFinset A B).1 hb with ⟨q, hq, hbot', rfl⟩
        exact (hY (Finset.mem_coe.2 hq)).2 hbot'
      exact y.closed _ _ hsub hEntB

theorem fstMap_pairElements (x : A.Element) (y : B.Element) :
    (fstMap A B).toElement (pairElements A B x y) = x := by
  apply le_antisymm
  · intro a ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(fstFinset A B s) ⊆ x.carrier := by
      intro b hb
      rcases (mem_fstFinset A B).1 hb with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).1 hbot
    exact x.closed _ a hsub (hEnt a (Finset.mem_singleton_self _))
  · intro a ha
    refine ⟨liftLeft A B {a}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftLeft A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
      have : b = a := Finset.mem_singleton.mp hb
      subst this
      exact ⟨fun _ => ha, fun _ => factoid_3_2 B y⟩
    · refine ⟨ProdCon_liftLeft A B (A.con_sing a), A.con_sing a, ?_⟩
      rw [fstFinset_liftLeft]
      exact proposition_2_3_iii A (A.con_sing a)

theorem sndMap_pairElements (x : A.Element) (y : B.Element) :
    (sndMap A B).toElement (pairElements A B x y) = y := by
  apply le_antisymm
  · intro b ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
    have hsub : ↑(sndFinset A B s) ⊆ y.carrier := by
      intro c hc
      rcases (mem_sndFinset A B).1 hc with ⟨p, hp, hbot, rfl⟩
      exact (hs (Finset.mem_coe.2 hp)).2 hbot
    exact y.closed _ b hsub (hEnt b (Finset.mem_singleton_self _))
  · intro b hb
    refine ⟨liftRight A B {b}, ?_, ?_⟩
    · intro p hp
      rcases (mem_liftRight A B).1 (Finset.mem_coe.1 hp) with ⟨c, hc, rfl⟩
      have : c = b := Finset.mem_singleton.mp hc
      subst this
      exact ⟨fun _ => factoid_3_2 A x, fun _ => hb⟩
    · refine ⟨ProdCon_liftRight A B (B.con_sing b), B.con_sing b, ?_⟩
      rw [sndFinset_liftRight]
      exact proposition_2_3_iii B (B.con_sing b)

/-- Tokens in `fstFinset s` for `s ⊆ ⟨x,y⟩` lie in `x`. -/
theorem mem_fst_of_subset_pairElements {x : A.Element} {y : B.Element}
    {s : Finset (ProdToken A B)}
    (hs : ↑s ⊆ (pairElements A B x y).carrier) {a : α}
    (ha : a ∈ fstFinset A B s) : a ∈ x.carrier := by
  have hCon : ProdCon A B s := (pairElements A B x y).consistent s hs
  have : a ∈ ((fstMap A B).toElement (pairElements A B x y)).carrier := by
    refine ⟨s, hs, ⟨hCon, A.con_sing a, ?_⟩⟩
    intro b hb
    have : b = a := Finset.mem_singleton.mp hb
    subst this
    exact A.ent_refl hCon.1 ha
  simpa [fstMap_pairElements] using this

/-- Tokens in `sndFinset s` for `s ⊆ ⟨x,y⟩` lie in `y`. -/
theorem mem_snd_of_subset_pairElements {x : A.Element} {y : B.Element}
    {s : Finset (ProdToken A B)}
    (hs : ↑s ⊆ (pairElements A B x y).carrier) {b : β}
    (hb : b ∈ sndFinset A B s) : b ∈ y.carrier := by
  have hCon : ProdCon A B s := (pairElements A B x y).consistent s hs
  have : b ∈ ((sndMap A B).toElement (pairElements A B x y)).carrier := by
    refine ⟨s, hs, ⟨hCon, B.con_sing b, ?_⟩⟩
    intro c hc
    have : c = b := Finset.mem_singleton.mp hc
    subst this
    exact B.ent_refl hCon.2 hb
  simpa [sndMap_pairElements] using this

theorem subset_pairElements_liftLeft {x : A.Element} {y : B.Element}
    {u : Finset α} (hu : ↑u ⊆ x.carrier) :
    ↑(liftLeft A B u) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  rcases (mem_liftLeft A B).1 (Finset.mem_coe.1 hp) with ⟨a, ha, rfl⟩
  have hax : a ∈ x.carrier := hu (Finset.mem_coe.2 ha)
  have : a ∈ ((fstMap A B).toElement (pairElements A B x y)).carrier := by
    simpa [fstMap_pairElements] using hax
  rcases this with ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
  exact (pairElements A B x y).closed s (mkLeft A B a) hs ⟨hCon,
    fun _ => hEnt a (Finset.mem_singleton_self _),
    fun _ => B.ent_bot hCon.2⟩

theorem subset_pairElements_liftRight {x : A.Element} {y : B.Element}
    {v : Finset β} (hv : ↑v ⊆ y.carrier) :
    ↑(liftRight A B v) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  rcases (mem_liftRight A B).1 (Finset.mem_coe.1 hp) with ⟨b, hb, rfl⟩
  have hby : b ∈ y.carrier := hv (Finset.mem_coe.2 hb)
  have : b ∈ ((sndMap A B).toElement (pairElements A B x y)).carrier := by
    simpa [sndMap_pairElements] using hby
  rcases this with ⟨s, hs, ⟨hCon, _, hEnt⟩⟩
  exact (pairElements A B x y).closed s (mkRight A B b) hs ⟨hCon,
    fun _ => A.ent_bot hCon.1,
    fun _ => hEnt b (Finset.mem_singleton_self _)⟩

theorem subset_pairElements_liftPair {x : A.Element} {y : B.Element}
    {u : Finset α} {v : Finset β} (hu : ↑u ⊆ x.carrier) (hv : ↑v ⊆ y.carrier) :
    ↑(liftPair A B u v) ⊆ (pairElements A B x y).carrier := by
  intro p hp
  have hp' : p ∈ liftLeft A B u ∪' liftRight A B v := Finset.mem_coe.1 hp
  rcases mem_funion.mp hp' with hp | hp
  · exact subset_pairElements_liftLeft A B hu (Finset.mem_coe.2 hp)
  · exact subset_pairElements_liftRight A B hv (Finset.mem_coe.2 hp)

/-- **Theorem 7.2.** `apply(g, y) = g(y)`. -/
theorem applyMap_toElement (g : (functionSystem B C).Element) (y : B.Element) :
    (applyMap (B := B) (C := C)).toElement
      (pairElements (functionSystem B C) B g y) =
      (element_toApproxMap B C g).toElement y := by
  apply le_antisymm
  · intro Z ⟨s, hs, ⟨hCon, hZcon, hEnt⟩⟩
    obtain ⟨hw, t, ht, hIn, hOut⟩ := hEnt
    have ht_sub : ↑t ⊆ g.carrier := by
      intro p hp
      exact mem_fst_of_subset_pairElements (functionSystem B C) B hs (ht (Finset.mem_coe.1 hp))
    have hsnd_sub : ↑(sndFinset (functionSystem B C) B s) ⊆ y.carrier := by
      intro b hb
      exact mem_snd_of_subset_pairElements (functionSystem B C) B hs hb
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hin_sub : ↑(funInputUnion B C t) ⊆ y.carrier := by
      intro b hb
      rcases (mem_funInputUnion B C).1 (Finset.mem_coe.1 hb) with ⟨q, hq, hb'⟩
      exact y.closed _ b hsnd_sub (hIn q hq b hb')
    have hEntZ : FunEnt B C t
        (mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z)) := by
      refine ⟨fun s' hs' hin' => hw s' (fun q hq => ht (hs' hq)) hin', t, Finset.Subset.refl _, ?_, hOut⟩
      intro q hq y' hy'
      exact B.ent_refl hin ((mem_funInputUnion B C).2 ⟨q, hq, hy'⟩)
    have hmem : mkFunToken B C (funInputUnion B C t) {Z} hin (C.con_sing Z) ∈ g.carrier :=
      g.closed t _ ht_sub hEntZ
    exact ⟨funInputUnion B C t, hin_sub, ⟨hin, C.con_sing Z, hmem⟩⟩
  · intro Z ⟨v, hv, ⟨hvCon, hZcon, hmem⟩⟩
    let p : FunToken B C := mkFunToken B C v {Z} hvCon hZcon
    have hp : p ∈ g.carrier := hmem
    let s := liftPair (functionSystem B C) B {p} v
    have hsCon : ProdCon (functionSystem B C) B s :=
      ProdCon_liftPair (functionSystem B C) B ((functionSystem B C).con_sing p) hvCon
    have hs_sub : ↑s ⊆ (pairElements (functionSystem B C) B g y).carrier :=
      subset_pairElements_liftPair (functionSystem B C) B
        (by
          intro q hq
          have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
          subst this
          exact hp)
        hv
    refine ⟨s, hs_sub, ⟨hsCon, C.con_sing Z, ?_⟩⟩
    refine ⟨?_, {p}, ?_, ?_, ?_⟩
    · -- FunCon of fst s from g.consistent
      intro t ht hin
      have ht_sub : ↑t ⊆ g.carrier := by
        intro q hq
        exact mem_fst_of_subset_pairElements (functionSystem B C) B hs_sub (ht hq)
      exact (funCon_of_approxMap B C (element_toApproxMap B C g) t
        (fun q hq => ⟨q.property.1, q.property.2, by
          simpa [mkFunToken_eq] using ht_sub (Finset.mem_coe.2 hq)⟩)) t (Finset.Subset.refl _) hin
    · -- {p} ⊆ fst s
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      rw [show s = liftLeft (functionSystem B C) B {p} ∪' liftRight (functionSystem B C) B v from rfl]
      rw [fstFinset_funion, fstFinset_liftLeft]
      exact subset_funion_left _ _ (Finset.mem_singleton_self _)
    · -- snd s ⊢ v = p.input
      intro q hq
      have : q = p := Finset.mem_singleton.mp hq
      subst this
      intro b hb
      have hb' : b ∈ v := hb
      -- snd s = snd(liftLeft) ∪' v entails v
      have : b ∈ sndFinset (functionSystem B C) B s := by
        rw [sndFinset_liftPair]
        exact subset_funion_right _ _ hb'
      exact B.ent_refl hsCon.2 this
    · -- output {Z} ⊢ {Z}
      rw [funOutputUnion_singleton]
      exact proposition_2_3_iii C (C.con_sing Z)

/-- The uncurrying of `k : A → (B → C)`. -/
def uncurryMap (k : ApproximableMap A (functionSystem B C)) :
    ApproximableMap (productSystem A B) C :=
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B))

/-- **Theorem 7.2.** `h = apply ∘ ⟨(curry h) ∘ fst, snd⟩`. -/
theorem uncurry_curryMap (h : ApproximableMap (productSystem A B) C) :
    uncurryMap A B C (curryMap A B C h) = h := by
  refine ApproximableMap.ext fun s w => ?_
  constructor
  · rintro ⟨m, ⟨hk, hsnd⟩, ⟨hCon, hw, hEnt⟩⟩
    -- hk : (curry h ∘ fst).rel s (fst m) i.e. ∃ v, fst.rel s v ∧ curry.rel v (fst m)
    obtain ⟨v, hfst, ⟨hv, hcurry⟩⟩ := hk
    obtain ⟨_, t, ht, hIn, hOut⟩ := hEnt
    -- Each q ∈ t is in fst m, and curry says h.rel (liftPair v q.1) q.2
    have hps : ∀ q ∈ t, h.rel (liftPair A B v q.val.1) q.val.2 :=
      fun q hq => hcurry q (ht hq)
    have hin : funInputUnion B C t ∈ B.Con :=
      B.con_subset
        (proposition_2_3_ii B hCon.2 (entSet_inputUnion_of_ent B C hIn))
        (subset_funion_right _ _)
    have hmid : h.rel (liftPair A B v (funInputUnion B C t)) (funOutputUnion B C t) :=
      rel_of_funTokens A B C h v hv t hps hin
    -- fst.rel s v means EntSet (fst s) v; snd.rel s (snd m) means EntSet (snd s) (snd m)
    -- and snd m ⊢ funInputUnion t
    have hEntIn : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      proposition_2_3_iv B (hsnd.1.2) hin
        (proposition_2_3_iv B (hsnd.1.2) hCon.2 hsnd.2.2
          (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii B hin)
    -- Actually hsnd : sndMap.rel s (snd m) = ⟨ProdCon s, snd m ∈ Con, EntSet (snd s) (snd m)⟩
    -- Simplify:
    have hs : s ∈ (productSystem A B).Con := hfst.1
    have hEntv : A.EntSet (fstFinset A B s) v := hfst.2.2
    have hEntsnd : B.EntSet (sndFinset A B s) (sndFinset (functionSystem B C) B m) := hsnd.2.2
    have hEntIn' : B.EntSet (sndFinset A B s) (funInputUnion B C t) :=
      proposition_2_3_iv B hs.2 hin
        (proposition_2_3_iv B hs.2 hCon.2 hEntsnd (entSet_inputUnion_of_ent B C hIn))
        (proposition_2_3_iii B hin)
    have hdom : liftPair A B (fstFinset A B s) (sndFinset A B s) ∈
        (productSystem A B).Con :=
      ProdCon_liftPair A B hs.1 hs.2
    -- Relate liftPair (fst s) (snd s) to liftPair v (inputUnion) via entSet_liftPair
    have hmid' : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s))
        (funOutputUnion B C t) :=
      h.mono hmid (entSet_liftPair A B hs.1 hs.2 hEntv hEntIn')
        (proposition_2_3_iii C (h.rel_cod hmid)) hdom (h.rel_cod hmid)
    -- Need: liftPair (fst s) (snd s) is "entailed by" s as product sets, or s relates via mono from a subset relation
    -- Key: s as product tokens "contains" the information of liftPair (fst s) (snd s)
    -- Use: EntSet s (liftPair (fst s) (snd s)) then mono of h from... wait h relates liftPair to output, need s h w.
    -- Show (productSystem).EntSet s (liftPair (fst s) (snd s))
    have hEntLift : (productSystem A B).EntSet s (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
      intro p hp
      unfold liftPair at hp
      rcases mem_funion.mp hp with hp | hp
      · rcases (mem_liftLeft A B).1 hp with ⟨a, ha, rfl⟩
        refine ⟨hs, ?_, ?_⟩
        · intro _
          exact A.ent_refl hs.1 ha
        · intro _
          exact B.ent_bot hs.2
      · rcases (mem_liftRight A B).1 hp with ⟨b, hb, rfl⟩
        refine ⟨hs, ?_, ?_⟩
        · intro _
          exact A.ent_bot hs.1
        · intro _
          exact B.ent_refl hs.2 hb
    exact h.mono hmid' hEntLift hOut hs hw
  · intro hh
    have hs : s ∈ (productSystem A B).Con := h.rel_dom hh
    have hw : w ∈ C.Con := h.rel_cod hh
    let tok : FunToken B C := mkFunToken B C (sndFinset A B s) w hs.2 hw
    have hLiftCon : ProdCon A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) :=
      ProdCon_liftPair A B hs.1 hs.2
    have hEntLift : (productSystem A B).EntSet
        (liftPair A B (fstFinset A B s) (sndFinset A B s)) s := by
      intro p hp
      rcases p.property with hR | hL
      · refine ⟨hLiftCon, fun _ => ?_, fun _ => ?_⟩
        · rw [hR]; exact A.ent_bot hLiftCon.1
        · have hb : p.val.2 ∈ sndFinset A B s :=
            (mem_sndFinset A B).2 ⟨p, hp, hR, rfl⟩
          have hb' : p.val.2 ∈
              sndFinset A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
            rw [sndFinset_liftPair]
            exact subset_funion_right _ _ hb
          exact B.ent_refl hLiftCon.2 hb'
      · refine ⟨hLiftCon, fun _ => ?_, fun _ => ?_⟩
        · have ha : p.val.1 ∈ fstFinset A B s :=
            (mem_fstFinset A B).2 ⟨p, hp, hL, rfl⟩
          have ha' : p.val.1 ∈
              fstFinset A B (liftPair A B (fstFinset A B s) (sndFinset A B s)) := by
            rw [fstFinset_liftPair]
            exact subset_funion_left _ _ ha
          exact A.ent_refl hLiftCon.1 ha'
        · rw [hL]; exact B.ent_bot hLiftCon.2
    have hrel : h.rel (liftPair A B (fstFinset A B s) (sndFinset A B s)) w :=
      h.mono hh hEntLift (proposition_2_3_iii C hw) hLiftCon hw
    have hcurry_tok : (curryMap A B C h).rel (fstFinset A B s) {tok} := by
      refine ⟨hs.1, ?_⟩
      intro p hp
      have : p = tok := Finset.mem_singleton.mp hp
      subst this
      exact hrel
    let m := liftPair (functionSystem B C) B {tok} (sndFinset A B s)
    have hmCon : ProdCon (functionSystem B C) B m :=
      ProdCon_liftPair (functionSystem B C) B ((functionSystem B C).con_sing tok) hs.2
    have hfst_m : fstFinset (functionSystem B C) B m =
        {tok} ∪' fstFinset (functionSystem B C) B
          (liftRight (functionSystem B C) B (sndFinset A B s)) := by
      change fstFinset _ _ (liftLeft _ _ {tok} ∪' liftRight _ _ _) = _
      rw [fstFinset_funion, fstFinset_liftLeft]
    have hsnd_m : sndFinset (functionSystem B C) B m =
        sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
          sndFinset A B s := by
      change sndFinset _ _ (liftLeft _ _ {tok} ∪' liftRight _ _ _) = _
      rw [sndFinset_funion, sndFinset_liftRight]
    have hcurry_fst : (curryMap A B C h).rel (fstFinset A B s)
        (fstFinset (functionSystem B C) B m) := by
      refine ⟨hs.1, ?_⟩
      intro p hp
      have hp' : p ∈ {tok} ∪' fstFinset (functionSystem B C) B
          (liftRight (functionSystem B C) B (sndFinset A B s)) := by
        rw [hfst_m] at hp
        exact hp
      rcases mem_funion.mp hp' with hp' | hp'
      · have : p = tok := Finset.mem_singleton.mp hp'
        subst this
        exact hrel
      · have hpbot : p = (functionSystem B C).bot :=
          Finset.mem_singleton.mp
            (fstFinset_liftRight (functionSystem B C) B (sndFinset A B s) hp')
        subst hpbot
        change h.rel (liftPair A B (fstFinset A B s) (funBot B C).val.1) (funBot B C).val.2
        simp only [funBot]
        exact h.mono h.empty_rel ((productSystem A B).entSet_empty _)
          (C.entSet_empty ∅) (ProdCon_liftPair A B hs.1 B.con_empty) C.con_empty
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · -- (curry ∘ fst).rel s (fst m)
      exact ⟨fstFinset A B s, ⟨hs, hs.1, proposition_2_3_iii A hs.1⟩, hcurry_fst⟩
    · -- snd.rel s (snd m)
      refine ⟨hs, hmCon.2, ?_⟩
      intro b hb
      have hb' : b ∈
          sndFinset (functionSystem B C) B (liftLeft (functionSystem B C) B {tok}) ∪'
            sndFinset A B s := by
        rwa [hsnd_m] at hb
      rcases mem_funion.mp hb' with hb' | hb'
      · have : b = B.bot := Finset.mem_singleton.mp
          (sndFinset_liftLeft (functionSystem B C) B {tok} hb')
        subst this
        exact B.ent_bot hs.2
      · exact B.ent_refl hs.2 hb'
    · -- apply.rel m w
      refine ⟨hmCon, hw, ?_⟩
      refine ⟨(curryMap A B C h).rel_cod hcurry_fst, {tok}, ?_, ?_, ?_⟩
      · intro q hq
        have : q = tok := Finset.mem_singleton.mp hq
        subst this
        have : tok ∈ fstFinset (functionSystem B C) B m := by
          rw [hfst_m]
          exact subset_funion_left _ _ (Finset.mem_singleton_self _)
        exact this
      · intro q hq
        have : q = tok := Finset.mem_singleton.mp hq
        subst this
        intro b hb
        have : b ∈ sndFinset (functionSystem B C) B m := by
          rw [hsnd_m]
          exact subset_funion_right _ _ hb
        exact B.ent_refl hmCon.2 this
      · rw [funOutputUnion_singleton]
        exact proposition_2_3_iii C hw

/-- **Theorem 7.2.** `curry` is the unique map satisfying the universal equation. -/
theorem curryMap_unique (h : ApproximableMap (productSystem A B) C)
    (k : ApproximableMap A (functionSystem B C))
    (huniv : uncurryMap A B C k = h) :
    k = curryMap A B C h := by
  have hk : uncurryMap A B C k = uncurryMap A B C (curryMap A B C h) := by
    rw [huniv, uncurry_curryMap]
  refine (ext_iff_toElement k (curryMap A B C h)).2 fun x => ?_
  have happly : ∀ y : B.Element,
      (element_toApproxMap B C (k.toElement x)).toElement y =
        (element_toApproxMap B C ((curryMap A B C h).toElement x)).toElement y := by
    intro y
    have hpair_k :
        (pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B (k.toElement x) y := by
      apply element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = k.toElement x := by
          rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements]
        exact h1.trans (fstMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
      · have h1 : (sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B (comp k (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
        exact h1.trans (sndMap_pairElements (functionSystem B C) B (k.toElement x) y).symm
    have hpair_c :
        (pairMap (functionSystem B C) B
            (comp (curryMap A B C h) (fstMap A B)) (sndMap A B)).toElement
          (pairElements A B x y) =
        pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y := by
      apply element_eq_of_fst_snd (functionSystem B C) B
      · have h1 : (fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = (curryMap A B C h).toElement x := by
          rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements]
        exact h1.trans
          (fstMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
      · have h1 : (sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (curryMap A B C h) (fstMap A B)) (sndMap A B)).toElement
              (pairElements A B x y)) = y := by
          rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
        exact h1.trans
          (sndMap_pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y).symm
    have hu1 : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B (k.toElement x) y) := by
      simp only [uncurryMap, comp_toElement, hpair_k]
    have hu2 : (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) =
        (applyMap (B := B) (C := C)).toElement
          (pairElements (functionSystem B C) B ((curryMap A B C h).toElement x) y) := by
      simp only [uncurryMap, comp_toElement, hpair_c]
    have heq : (uncurryMap A B C k).toElement (pairElements A B x y) =
        (uncurryMap A B C (curryMap A B C h)).toElement (pairElements A B x y) := by
      rw [hk]
    rw [← applyMap_toElement, ← applyMap_toElement, ← hu1, ← hu2, heq]
  have hx : element_toApproxMap B C (k.toElement x) =
      element_toApproxMap B C ((curryMap A B C h).toElement x) :=
    (ext_iff_toElement _ _).2 happly
  have : k.toElement x = (curryMap A B C h).toElement x := by
    rw [← approxMap_toElement_element_toApproxMap B C (k.toElement x),
      ← approxMap_toElement_element_toApproxMap B C ((curryMap A B C h).toElement x), hx]
  rw [this]
