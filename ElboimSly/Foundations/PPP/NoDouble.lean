/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Dissecting
public import ElboimSly.Foundations.PPP.PoissonMoments
public import Mathlib

/-!
# No double cells

No double cells.

The cells `C_m(i) = A ∩ idx_m⁻¹{i}` of the partitions of `A` are the fibres of the measurable maps
`idx m : S → ℕ` intersected with `A`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- `P(N(C) ≥ 2) ≤ μ(C)² / 2` for a set of finite mass. -/
theorem measure_two_le_count (h : IsPoissonPointProcess N μ P) {C : Set S} (hC : MeasurableSet C)
    (hμ : μ C < ∞) : P {ω | 2 ≤ N ω C} ≤ 2⁻¹ * μ C ^ 2 := by
  have hm := h.measurable_count hC
  have e : {ω | 2 ≤ N ω C} = (fun ω => N ω C) ⁻¹' Set.Ici 2 := rfl
  rw [e, ← Measure.map_apply hm measurableSet_Ici, h.map_count hC]
  lift μ C to ℝ≥0 using hμ.ne with r hr
  refine (extPoissonMeasure_Ici_two_le r).trans ?_
  refine le_of_eq ?_
  rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_pow r.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm]

end IsPoissonPointProcess

/-- The function `x ↦ μ(A ∩ C_m(x))`. -/
noncomputable def cellMass (μ : Measure S) (A : Set S) (idx : S → ℕ) (x : S) : ℝ≥0∞ :=
  μ (A ∩ idx ⁻¹' {idx x})

theorem measurable_cellMass (μ : Measure S) (A : Set S) {idx : S → ℕ} (hidx : Measurable idx) :
    Measurable (cellMass μ A idx) := by
  have : cellMass μ A idx = (fun i : ℕ => μ (A ∩ idx ⁻¹' {i})) ∘ idx := rfl
  rw [this]
  exact measurable_from_top.comp hidx

theorem lintegral_cellMass (μ : Measure S) (A : Set S) {idx : S → ℕ} (hidx : Measurable idx)
    (_hA : MeasurableSet A) :
    ∫⁻ x in A, cellMass μ A idx x ∂μ = ∑' i : ℕ, μ (A ∩ idx ⁻¹' {i}) ^ 2 := by
  have e : ∀ x, cellMass μ A idx x =
      ∑' i : ℕ, (idx ⁻¹' {i}).indicator (fun _ => μ (A ∩ idx ⁻¹' {i})) x := by
    intro x
    rw [tsum_eq_single (idx x)]
    · simp [cellMass]
    · intro i hi
      have : x ∉ idx ⁻¹' {i} := fun h => hi (by simpa using h.symm)
      simp [this]
  simp_rw [e]
  rw [lintegral_tsum fun i => ((measurable_const.indicator
    (hidx (measurableSet_singleton i))).aemeasurable)]
  refine tsum_congr fun i => ?_
  rw [lintegral_indicator_const (hidx (measurableSet_singleton i)),
    Measure.restrict_apply (hidx (measurableSet_singleton i)), sq, Set.inter_comm]

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- No double cells (quantitative part): the probability that some cell of level `m`
contains two atoms is at most `½ ∫_A μ(C_m(x)) μ(dx)`. -/
theorem measure_exists_two_le_count (h : IsPoissonPointProcess N μ P) {A : Set S}
    (hA : MeasurableSet A) (hμA : μ A < ∞) {idx : S → ℕ} (hidx : Measurable idx) :
    P {ω | ∃ i : ℕ, 2 ≤ N ω (A ∩ idx ⁻¹' {i})} ≤ 2⁻¹ * ∫⁻ x in A, cellMass μ A idx x ∂μ := by
  have e : {ω | ∃ i : ℕ, 2 ≤ N ω (A ∩ idx ⁻¹' {i})} =
      ⋃ i : ℕ, {ω | 2 ≤ N ω (A ∩ idx ⁻¹' {i})} := by ext; simp
  rw [e, lintegral_cellMass μ A hidx hA, ← ENNReal.tsum_mul_left]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun i => ?_)
  exact h.measure_two_le_count (hA.inter (hidx (measurableSet_singleton i)))
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hμA)

/-- No double cells: almost surely some level has at most one atom per cell. -/
theorem ae_exists_level_le_one (h : IsPoissonPointProcess N μ P) {A : Set S}
    (hA : MeasurableSet A) (hμA : μ A < ∞) {idx : ℕ → S → ℕ} (hidx : ∀ m, Measurable (idx m))
    (href : ∀ m x y, idx (m + 1) x = idx (m + 1) y → idx m x = idx m y)
    (hnull : ∀ x ∈ A, μ (A ∩ ⋂ m, idx m ⁻¹' {idx m x}) = 0) :
    ∀ᵐ ω ∂P, ∃ m, ∀ i : ℕ, N ω (A ∩ idx m ⁻¹' {i}) ≤ 1 := by
  have hcm : ∀ m i, MeasurableSet (A ∩ idx m ⁻¹' {i}) := fun m i =>
    hA.inter (hidx m (measurableSet_singleton i))
  have hnat : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, ∃ n : ℕ, N ω (A ∩ idx p.1 ⁻¹' {p.2}) = n :=
    h.ae_forall_natCast_count (A := fun p : ℕ × ℕ => A ∩ idx p.1 ⁻¹' {p.2})
      (fun p => hcm p.1 p.2) fun p =>
        lt_of_le_of_lt (measure_mono Set.inter_subset_left) hμA
  -- the limit of the bounds is zero
  set f : ℕ → S → ℝ≥0∞ := fun m => cellMass μ A (idx m) with hf
  have hfm : ∀ m, Measurable (f m) := fun m => measurable_cellMass μ A (hidx m)
  have hle : ∀ {m m' : ℕ}, m ≤ m' → ∀ x y, idx m' x = idx m' y → idx m x = idx m y := by
    intro m m' hmm' x y hxy
    induction hmm' with
    | refl => exact hxy
    | step _ ih => exact ih (href _ _ _ hxy)
  have hset : ∀ x, Antitone fun m => A ∩ idx m ⁻¹' {idx m x} := by
    intro x m m' hmm'
    refine Set.inter_subset_inter_right _ ?_
    intro y hy
    exact hle hmm' _ _ (by simpa using hy)
  have hanti : Antitone f := fun m m' hmm' x => measure_mono (hset x hmm')
  have hfin : ∫⁻ x in A, f 0 x ∂μ ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => μ A) fun x =>
      measure_mono Set.inter_subset_left) ?_)
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.mul_lt_top hμA hμA
  have hinf : ⨅ m, ∫⁻ x in A, f m x ∂μ = 0 := by
    rw [← lintegral_iInf (μ := μ.restrict A) hfm hanti hfin]
    have : ∀ x ∈ A, ⨅ m, f m x = 0 := by
      intro x hx
      have := (hset x).measure_iInter (μ := μ) (fun m => (hcm m _).nullMeasurableSet)
        ⟨0, (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hμA).ne⟩
      have e : (⋂ m, A ∩ idx m ⁻¹' {idx m x}) = A ∩ ⋂ m, idx m ⁻¹' {idx m x} := by
        rw [Set.inter_iInter]
      rw [e, hnull x hx] at this
      exact this.symm
    rw [setLIntegral_congr_fun hA this]
    simp
  have hP : P (⋂ m, {ω | ∃ i : ℕ, 2 ≤ N ω (A ∩ idx m ⁻¹' {i})}) = 0 := by
    refine le_antisymm ?_ bot_le
    calc P (⋂ m, {ω | ∃ i : ℕ, 2 ≤ N ω (A ∩ idx m ⁻¹' {i})})
        ≤ ⨅ m, 2⁻¹ * ∫⁻ x in A, f m x ∂μ :=
          le_iInf fun m => (measure_mono (Set.iInter_subset _ m)).trans
            (h.measure_exists_two_le_count hA hμA (hidx m))
      _ = 2⁻¹ * ⨅ m, ∫⁻ x in A, f m x ∂μ := by
          rw [ENNReal.mul_iInf_of_ne (by simp) (by simp)]
      _ = 0 := by rw [hinf, mul_zero]
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ m, {ω | ∃ i : ℕ, 2 ≤ N ω (A ∩ idx m ⁻¹' {i})} := by
    exact measure_eq_zero_iff_ae_notMem.1 hP
  filter_upwards [hnat, hae] with ω hω1 hω2
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, not_forall, not_exists, not_le] at hω2
  obtain ⟨m, hm⟩ := hω2
  refine ⟨m, fun i => ?_⟩
  obtain ⟨n, hn⟩ := hω1 (m, i)
  have := hm i
  rw [hn] at this ⊢
  have : n < 2 := by exact_mod_cast this
  exact_mod_cast Nat.lt_succ_iff.1 this

end IsPoissonPointProcess

end ElboimSly
