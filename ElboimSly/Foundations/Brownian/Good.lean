/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Schauder
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib

/-!
# The good event of the Lévy–Ciesielski construction

The good event (with one-dimensional Gaussian bounds (a), the Gaussian tail bound).

For real random variables `ξ_α`, `α = (i, m, h) ∈ Idx d`, each with law `N(0,1)`, the event `G` on
which `∑_n 2^{-n/2-1} max_k |ξ_{(i,m,(n,k))}|` converges for all `i, m` is measurable and
almost sure. (The written proof writes the weight `2^{-n/2}`; the weight here is `schauderAmp n =
2^{-n/2-1}`, which differs by the constant factor `1/2` and so defines the same event.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ElboimSly.Brownian

/-- The index set `[d] × ℕ × ℋ` of the Gaussian family (Schauder functions and index sets). -/
abbrev Idx (d : ℕ) : Type := Fin d × ℕ × HaarIdx

variable {Ω : Type*} {d : ℕ}

/-- The maximum `max_{k < 2^n} |ξ_{(i,m,(n,k))}|` of level `n`. -/
noncomputable def levelMax (ξ : Idx d → Ω → ℝ) (i : Fin d) (m n : ℕ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun k : Fin (2 ^ n) => |ξ (i, m, some ⟨n, k⟩) ω|)

/-- The good event. The good event `G`. -/
def goodSet (ξ : Idx d → Ω → ℝ) : Set Ω :=
  {ω | ∀ (i : Fin d) (m : ℕ), ∑' n : ℕ, ENNReal.ofReal (schauderAmp n * levelMax ξ i m n ω) ≠ ∞}

lemma abs_le_levelMax (ξ : Idx d → Ω → ℝ) (i : Fin d) (m n : ℕ) (ω : Ω) (k : Fin (2 ^ n)) :
    |ξ (i, m, some ⟨n, k⟩) ω| ≤ levelMax ξ i m n ω :=
  Finset.le_sup' (fun k : Fin (2 ^ n) => |ξ (i, m, some ⟨n, k⟩) ω|) (Finset.mem_univ k)

lemma levelMax_nonneg (ξ : Idx d → Ω → ℝ) (i : Fin d) (m n : ℕ) (ω : Ω) :
    0 ≤ levelMax ξ i m n ω :=
  (abs_nonneg _).trans (abs_le_levelMax ξ i m n ω ⟨0, by positivity⟩)

variable [MeasurableSpace Ω]

lemma measurable_levelMax {ξ : Idx d → Ω → ℝ} (hξ : ∀ α, Measurable (ξ α)) (i : Fin d)
    (m n : ℕ) : Measurable (levelMax ξ i m n) := by
  unfold levelMax
  have := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (2 ^ n)))) Finset.univ_nonempty
    (f := fun k ω => |ξ (i, m, some ⟨n, k⟩) ω|) fun k _ => (hξ _).abs
  convert this using 1
  ext ω
  simp [Finset.sup'_apply]

lemma measurableSet_goodSet {ξ : Idx d → Ω → ℝ} (hξ : ∀ α, Measurable (ξ α)) :
    MeasurableSet (goodSet ξ) := by
  have : goodSet ξ = ⋂ (i : Fin d) (m : ℕ),
      {ω | ∑' n : ℕ, ENNReal.ofReal (schauderAmp n * levelMax ξ i m n ω) ≠ ∞} := by
    ext ω; simp [goodSet]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun m => ?_
  have : Measurable fun ω => ∑' n : ℕ, ENNReal.ofReal (schauderAmp n * levelMax ξ i m n ω) :=
    Measurable.tsum fun n =>
      ENNReal.measurable_ofReal.comp ((measurable_levelMax hξ i m n).const_mul _)
  exact this (measurableSet_singleton ∞).compl

omit [MeasurableSpace Ω] in
lemma summable_of_mem_goodSet {ξ : Idx d → Ω → ℝ} {ω : Ω} (hω : ω ∈ goodSet ξ) (i : Fin d)
    (m : ℕ) : Summable fun n => schauderAmp n * levelMax ξ i m n ω := by
  have := ENNReal.summable_toReal (hω i m)
  refine this.congr fun n => ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (schauderAmp_pos n).le (levelMax_nonneg _ _ _ _ _))]

omit [MeasurableSpace Ω] in
lemma mem_goodSet_of_summable {ξ : Idx d → Ω → ℝ} {ω : Ω}
    (h : ∀ (i : Fin d) (m : ℕ), Summable fun n => schauderAmp n * levelMax ξ i m n ω) :
    ω ∈ goodSet ξ := by
  intro i m
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (schauderAmp_pos n).le (levelMax_nonneg _ _ _ _ _)) (h i m)]
  exact ENNReal.ofReal_ne_top

/-! ### Gaussian tail -/

section Tail

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- One-dimensional Gaussian bounds (a): `P(|X| > a) ≤ 2 e^{-a²/2}` for `X ~ N(0,1)`. -/
lemma gaussian_tail {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | a < |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / 2))) := by
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := by
    intro t
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t
    rw [← hX.map_eq, integrable_map_measure h.aestronglyMeasurable hX.aemeasurable] at h
    exact h
  have hup := measure_ge_le_exp_mul_mgf (μ := P) (X := X) a ha (hint a)
  have hlow := measure_le_le_exp_mul_mgf (μ := P) (X := X) (-a) (neg_nonpos.2 ha) (hint (-a))
  rw [mgf_gaussianReal hX] at hup hlow
  have e1 : Real.exp (-a * a) * Real.exp (0 * a + ((1 : ℝ≥0) : ℝ) * a ^ 2 / 2) =
      Real.exp (-(a ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; simp; ring
  have e2 : Real.exp (-(-a) * -a) * Real.exp (0 * -a + ((1 : ℝ≥0) : ℝ) * (-a) ^ 2 / 2) =
      Real.exp (-(a ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; simp; ring
  rw [e1] at hup
  rw [e2] at hlow
  have hsub : {ω | a < |X ω|} ⊆ {ω | a ≤ X ω} ∪ {ω | X ω ≤ -a} := by
    intro ω hω
    have hω' : a < |X ω| := hω
    rcases lt_abs.mp hω' with h | h
    · exact Or.inl h.le
    · exact Or.inr (show X ω ≤ -a by linarith)
  calc P {ω | a < |X ω|} ≤ P ({ω | a ≤ X ω} ∪ {ω | X ω ≤ -a}) := measure_mono hsub
    _ ≤ P {ω | a ≤ X ω} + P {ω | X ω ≤ -a} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(a ^ 2 / 2))) + ENNReal.ofReal (Real.exp (-(a ^ 2 / 2))) := by
        gcongr
        · rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
          exact ENNReal.ofReal_le_ofReal hup
        · rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
          exact ENNReal.ofReal_le_ofReal hlow
    _ = _ := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1; ring

/-- The geometric bound for the level maxima. -/
lemma measure_levelMax_gt {ξ : Idx d → Ω → ℝ}
    (hξ : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P) (i : Fin d) (m n : ℕ) :
    P {ω | 2 * ((n : ℝ) + 1) < levelMax ξ i m n ω} ≤
      ENNReal.ofReal (2 * Real.exp (-2) * (2 * Real.exp (-2)) ^ n) := by
  set a : ℝ := 2 * ((n : ℝ) + 1) with ha
  have ha0 : 0 ≤ a := by positivity
  have hsub : {ω | a < levelMax ξ i m n ω} ⊆
      ⋃ k : Fin (2 ^ n), {ω | a < |ξ (i, m, some ⟨n, k⟩) ω|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, levelMax, Finset.lt_sup'_iff] at hω
    obtain ⟨k, _, hk⟩ := hω
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  have hexp : Real.exp (-(a ^ 2 / 2)) ≤ Real.exp (-2) * Real.exp (-2) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [ha]; nlinarith
  calc P {ω | a < levelMax ξ i m n ω}
      ≤ P (⋃ k : Fin (2 ^ n), {ω | a < |ξ (i, m, some ⟨n, k⟩) ω|}) := measure_mono hsub
    _ ≤ ∑ k : Fin (2 ^ n), P {ω | a < |ξ (i, m, some ⟨n, k⟩) ω|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (2 ^ n), ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / 2))) :=
        Finset.sum_le_sum fun k _ => gaussian_tail (hξ _) ha0
    _ = ENNReal.ofReal ((2 : ℝ) ^ n * (2 * Real.exp (-(a ^ 2 / 2)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        simp
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        calc (2 : ℝ) ^ n * (2 * Real.exp (-(a ^ 2 / 2)))
            ≤ 2 ^ n * (2 * (Real.exp (-2) * Real.exp (-2) ^ n)) := by gcongr
          _ = _ := by rw [mul_pow]; ring

lemma summable_amp_mul :
    Summable fun n : ℕ => schauderAmp n * (2 * ((n : ℝ) + 1)) := by
  have hr : ‖(Real.sqrt 2)⁻¹‖ < 1 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply inv_lt_one_of_one_lt₀
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_norm_lt_one hr
  refine (h1.add h0).congr fun n => ?_
  simp only [schauderAmp, pow_one]
  ring

lemma ae_summable_levelMax {ξ : Idx d → Ω → ℝ}
    (hξ : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P) (i : Fin d) (m : ℕ) :
    ∀ᵐ ω ∂P, Summable fun n => schauderAmp n * levelMax ξ i m n ω := by
  set ρ : ℝ := 2 * Real.exp (-2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    rw [hρ, Real.exp_neg]
    rw [mul_inv_lt_iff₀ (Real.exp_pos 2)]
    linarith
  have hsum : Summable fun n : ℕ => 2 * Real.exp (-2) * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hfin : ∑' n : ℕ, P {ω | 2 * ((n : ℝ) + 1) < levelMax ξ i m n ω} ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => measure_levelMax_gt hξ i m n)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  refine Summable.of_norm_bounded_eventually summable_amp_mul ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hω] with n hn
  have hn' : levelMax ξ i m n ω ≤ 2 * ((n : ℝ) + 1) := not_lt.mp hn
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (schauderAmp_pos n).le
    (levelMax_nonneg _ _ _ _ _))]
  exact mul_le_mul_of_nonneg_left hn' (schauderAmp_pos n).le

/-- The good event. The good event has probability one (independence is not needed). -/
theorem ae_mem_goodSet {ξ : Idx d → Ω → ℝ} (hξ : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P) :
    ∀ᵐ ω ∂P, ω ∈ goodSet ξ := by
  have : ∀ᵐ ω ∂P, ∀ (i : Fin d) (m : ℕ), Summable fun n => schauderAmp n * levelMax ξ i m n ω :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun m => ae_summable_levelMax hξ i m
  filter_upwards [this] with ω hω using mem_goodSet_of_summable hω

end Tail

end ElboimSly.Brownian
