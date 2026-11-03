/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Transfer
public import ElboimSly.Foundations.SRW.PoissonTail
public import ElboimSly.Foundations.SRW.FixedCounts
public import ElboimSly.Foundations.SRW.Increments
public import Mathlib

/-!
# Window counts of the canonical walk

Good event and path properties (P2) and the Poisson law of `M(U) = ν(D × U)` (PPP1), used by
Crude count bound; Lemma 2.2 for the SRW and fluctuations over short windows.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- The `ℓ¹` norm of an integer vector, as a real number. -/
noncomputable def l1 {d : ℕ} (x : Fin d → ℤ) : ℝ := ∑ i, |(x i : ℝ)|

theorem l1_eq_natAbs {d : ℕ} (x : Fin d → ℤ) : l1 x = ((∑ i, (x i).natAbs : ℕ) : ℝ) := by
  simp [l1, Nat.cast_natAbs, Int.cast_abs]

theorem norm_le_l1 {d : ℕ} (x : Fin d → ℤ) : ‖x‖ ≤ l1 x := by
  unfold l1
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  intro i
  rw [Int.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |(x i : ℝ)|) (fun i _ => abs_nonneg _)
    (Finset.mem_univ i)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

/-- The number of points in a time window, `M(a,b]`. -/
noncomputable def winCount (N : Ω → Measure (Dir d × ℝ)) (a b : ℝ) (ω : Ω) : ℕ :=
  natOf (tot (N ω) (Ioc a b))

theorem measurable_winCount (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (a b : ℝ) :
    Measurable (winCount N a b) :=
  measurable_natOf.comp (hN.measurable_count (MeasurableSet.univ.prod measurableSet_Ioc))

theorem hasLaw_winCount (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {a b : ℝ}
    (ha : 0 ≤ a) (_hab : a ≤ b) :
    HasLaw (winCount N a b) (poissonMeasure (((2 * d : ℝ) * (b - a)).toNNReal)) P := by
  have hm : MeasurableSet (univ ×ˢ Ioc a b : Set (Dir d × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioc
  refine ⟨(measurable_winCount hN a b).aemeasurable, ?_⟩
  have h1 : winCount N a b = natOf ∘ fun ω => N ω (univ ×ˢ Ioc a b) := rfl
  have hcard : (Fintype.card (Dir d) : ℝ) = 2 * d := by simp [Dir]; ring
  have hx : clockIntensity (Dir d) (univ ×ˢ Ioc a b) =
      ((((2 * d : ℝ) * (b - a)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [clock_univ_Ioc ha]
    show _ = ENNReal.ofReal _
    rw [ENNReal.ofReal_mul (by positivity), ← hcard, ENNReal.ofReal_natCast]
  rw [h1, ← Measure.map_map measurable_natOf (hN.measurable_count hm), hN.map_count hm, hx]
  show Measure.map natOf (extPoissonMeasure _) = _
  rw [extPoissonMeasure_coe, Measure.map_map measurable_natOf measurable_natCast_ennreal]
  have : natOf ∘ (Nat.cast : ℕ → ℝ≥0∞) = id := by
    funext n; simp [natOf]
  rw [this, Measure.map_id]

/-- Chernoff bound for the window count: `P(M(a,b] ≥ c) ≤ exp (2d(e-1)(b-a) - c)`. -/
theorem winCount_tail (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (c : ℝ) :
    P.real {ω | c ≤ (winCount N a b ω : ℝ)} ≤
      Real.exp (2 * d * (Real.exp 1 - 1) * (b - a) - c) := by
  have := hN.isProbabilityMeasure
  have := poisson_chernoff_one (hasLaw_winCount hN ha hab) c
  rw [Real.coe_toNNReal _ (by have : (0 : ℝ) ≤ 2 * d := by positivity
                              nlinarith)] at this
  convert this using 2
  ring

/-- Good event and path properties (P2), canonical walk: the `ℓ¹` size of an increment over `(s,s']` is
at most `M(a,b]` for any `(s,s'] ⊆ (a,b]`. -/
theorem l1_walk_sub_le (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) :
    ∀ᵐ ω ∂P, ∀ s s' a b : ℝ, 0 ≤ a → a ≤ s → s ≤ s' → s' ≤ b →
      l1 (walk d (N ω) s' - walk d (N ω) s) ≤ (winCount N a b ω : ℝ) := by
  filter_upwards [ae_good hN] with ω hω s s' a b ha has hss' hs'b
  have h1 := walk_sub_l1_le hω (le_trans ha has) hss'
  have h2 : tot (N ω) (Ioc s s') ≤ tot (N ω) (Ioc a b) :=
    measure_mono (prod_mono subset_rfl (Ioc_subset_Ioc has hs'b))
  have h3 : ((winCount N a b ω : ℕ) : ℝ≥0∞) = tot (N ω) (Ioc a b) :=
    (good_tot_Ioc hω ha).natCast_natOf
  have h4 : ((∑ i, (walk d (N ω) s' i - walk d (N ω) s i).natAbs : ℕ) : ℝ≥0∞) ≤
      (winCount N a b ω : ℕ) := by
    rw [h3]; exact h1.trans h2
  have h5 : (∑ i, (walk d (N ω) s' i - walk d (N ω) s i).natAbs) ≤ winCount N a b ω := by
    exact_mod_cast h4
  rw [l1_eq_natAbs]
  exact_mod_cast h5

end SRW
end ElboimSly
