/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1982
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Scott1982.InfoSys

/-!
# Factoid 2.5 — second example: open intervals plus `(0, ∞)`

**Scott 1982, §2 (“A second example”).** Data objects are pairs `(n, m)` of integers
with `n < m`, read as `n < x < m`, together with an artificial least-informative
object `(0, ∞)` (our `bot`). Consistency: some point satisfies every token in the
finite set. Entailment: every point satisfying the left-hand set satisfies the
right-hand token.

We take the point space to be `ℚ` so every strict integer-endpoint interval is
inhabited (Def 2.1(ii)). The always-true reading of `bot` matches Scott’s
“artificial” Δ.
-/

namespace Scott1982

namespace Factoid25

/-- Tokens: `bot` ≃ `(0, ∞)`, or a strict integer interval `(lo, hi)`. -/
inductive Token : Type where
  | bot
  | interval (lo hi : ℕ) (hlt : lo < hi)

namespace Token

/-- Decidable equality ignores the `<` proof (proof-irrelevant). -/
instance instDecidableEq : DecidableEq Token
  | bot, bot => isTrue rfl
  | bot, interval _ _ _ => isFalse Token.noConfusion
  | interval _ _ _, bot => isFalse Token.noConfusion
  | interval n m _, interval n' m' _ =>
    if h : n = n' ∧ m = m' then
      isTrue (by
        rcases h with ⟨rfl, rfl⟩
        rfl)
    else
      isFalse (by
        intro hEq
        injection hEq with hn hm
        exact h ⟨hn, hm⟩)

end Token

/-- Satisfaction of a token at a rational point. -/
def Sat (x : ℚ) : Token → Prop
  | .bot => True
  | .interval lo hi _ => (lo : ℚ) < x ∧ x < (hi : ℚ)

/-- Midpoint witness: `lo < hi` (on `ℕ`) implies `(lo+hi)/2` lies in `(lo, hi)` on `ℚ`. -/
theorem sat_midpoint {lo hi : ℕ} (hlt : lo < hi) :
    Sat (((lo : ℚ) + (hi : ℚ)) / 2) (.interval lo hi hlt) := by
  have h2 : (0 : ℚ) < 2 := by norm_num
  have _hlo : (lo : ℚ) < (hi : ℚ) := Nat.cast_lt.mpr hlt
  constructor
  · -- lo < (lo+hi)/2 ↔ 2*lo < lo+hi ↔ lo < hi
    rw [lt_div_iff₀ h2]
    linarith
  · rw [div_lt_iff₀ h2]
    linarith

/-- Every token is satisfiable. -/
theorem sat_sing (t : Token) : ∃ x : ℚ, Sat x t := by
  cases t with
  | bot => exact ⟨0, trivial⟩
  | interval lo hi hlt => exact ⟨_, sat_midpoint hlt⟩

/-- Generic information system from a satisfaction relation with a true `bot`
and inhabited singletons (Scott’s “obvious interpretation”).

`Ent` packages consistency of the left-hand set together with semantic entailment,
matching Scott’s typing of `⊢` as a relation on `Con × D` and making `ent_con`
hold (a purely vacuous `∀`-entailment from an inconsistent set would not). -/
def ofSatisfaction {τ : Type*} [DecidableEq τ] {Point : Type*}
    (Sat : Point → τ → Prop) (bot : τ)
    (sat_bot : ∀ p, Sat p bot)
    (sat_sing : ∀ t, ∃ p, Sat p t) : InfoSys τ where
  bot := bot
  Con := {u | ∃ p, ∀ t ∈ u, Sat p t}
  Ent u X := (∃ p, ∀ t ∈ u, Sat p t) ∧ ∀ p, (∀ t ∈ u, Sat p t) → Sat p X
  con_subset := by
    rintro u v ⟨p, hp⟩ hsub
    exact ⟨p, fun t ht => hp t (hsub ht)⟩
  con_sing := by
    intro a
    obtain ⟨p, hp⟩ := sat_sing a
    exact ⟨p, fun t ht => by
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hp⟩
  ent_con := by
    rintro u a ⟨⟨p, hp⟩, hEnt⟩
    exact ⟨p, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact hEnt p hp
      · exact hp t ht'⟩
  ent_bot := by
    intro u hu
    exact ⟨hu, fun p _ => sat_bot p⟩
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, fun p hp => hp a ha⟩
  ent_trans := by
    intro u v c hv _hu hvu ⟨_, huEnt⟩
    refine ⟨hv, fun p hp => huEnt p ?_⟩
    intro y hy
    exact (hvu y hy).2 p hp

/-- **Factoid 2.5.** Interval information system of Scott 1982, §2. -/
example : InfoSys Token :=
  ofSatisfaction Sat Token.bot (fun _ => trivial) sat_sing

end Factoid25

end Scott1982
