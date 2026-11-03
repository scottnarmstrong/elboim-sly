/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Discharge
public import ElboimSly.Foundations.Cyclic.CycFarRc
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegen
public import Mathlib

/-!
# The fresh walk `W'_i` is right-continuous

One excursion succeeds with probability at least frac12 (events of `W'_i` by countable reduction, right-continuity).
The glued walk `W' = contGlue (planFirst …) (contSeq N'')` of w_2 after zeta_i, given ℱ^+_zeta_i is right-continuous
for every sample point: the first piece is `envWalk` (the constant start if the environment is not
good, an environment path otherwise), the further pieces are `walkMap`s of slices.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem rc_envWalk (ν : Measure (CycS Unit d β)) (δ : CycData Unit d) (s : ℝ≥0) :
    ∀ᶠ u in 𝓝[≥] s, envWalk ν δ u = envWalk ν δ s := by
  by_cases hν : CycGood ν
  · have e : envWalk ν δ = (envPath ν δ).1.fn := by
      unfold envWalk
      rw [ite_eq_left hν, (envPath_len (hν δ.copy)).2]
    rw [e]
    exact (envPath ν δ).1.rc s
  · have e : envWalk ν δ = fun _ => δ.start := by
      unfold envWalk
      rw [ite_eq_right hν]
    rw [e]
    exact Eventually.of_forall fun _ => rfl

theorem rc_walkMap (ν : Measure (RingSpace d β)) (s : ℝ≥0) :
    ∀ᶠ u in 𝓝[≥] s, walkMap ν u = walkMap ν s := by
  classical
  set ν' : Measure (RingSpace d β) := if Good ν then ν else 0 with hν'
  have hg : Good ν' := by
    rw [hν']; split_ifs with h
    · exact h
    · exact good_zero
  have h := (step78_isRegPath_cycWalk (ν := ν'.map (Prod.mk ())) (cycGood_map_unit hg) 0 0
    0).rc s
  simp only [cycSlice_map_unit] at h
  exact h

theorem rc_contGlue {b : ℝ≥0} (hb : 0 < b) {p : ℝ≥0 → Fin d → ℤ} {q : ℕ → ℝ≥0 → Fin d → ℤ}
    (hp : ∀ s, ∀ᶠ u in 𝓝[≥] s, p u = p s) (hq : ∀ k s, ∀ᶠ u in 𝓝[≥] s, q k u = q k s)
    (s : ℝ≥0) : ∀ᶠ u in 𝓝[≥] s, contGlue b p q u = contGlue b p q s := by
  set σ := partialSums fun k => pathTreg b (contPieces p q k) with hσ
  have hm : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ, partialSums_succ]; exact le_self_add
  have h0 : σ 0 = 0 := by simp [hσ, partialSums]
  have hbdd := bdd_partialSums hb (τ := fun k => pathTreg b (contPieces p q k))
    (fun k => le_pathTreg b _)
  have hw : ∀ (k : ℕ) (s : ℝ≥0), ∀ᶠ u in 𝓝[≥] s, contPieces p q k u = contPieces p q k s := by
    intro k s
    cases k with
    | zero => exact hp s
    | succ k => exact hq k s
  exact gluedWalk_rc hm h0 hbdd hw s

/-- The fresh walk `W'` of w_2 after zeta_i, given ℱ^+_zeta_i is right-continuous, at every sample point. -/
theorem rc_freshWalk {Ω : Type*} (P : CycPlan Unit d β) (N N' : Ω → Measure (CycS Unit d β))
    (N'' : Ω → Measure (ℕ × RingSpace d β)) (T : Ω → WithTop ℝ≥0) (δ : Ω → CycData Unit d)
    (ω : Ω) (s : ℝ≥0) :
    ∀ᶠ u in 𝓝[≥] s, contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω) u =
      contGlue β.toNNReal (planFirst P N N' T δ ω) (contSeq N'' ω) s := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  refine rc_contGlue hb (fun s => ?_) (fun k s => rc_walkMap _ s) s
  have := rc_envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) (δ ω) s
  filter_upwards [this] with u hu
  simp only [planFirst, hu]

end ElboimSly.Paper.Step

end
