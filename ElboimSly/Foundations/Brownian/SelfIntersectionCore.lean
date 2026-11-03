/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionDet
public import ElboimSly.Foundations.Brownian.SelfIntersectionGlobal
public import ElboimSly.Foundations.Brownian.SelfIntersectionNum
public import ElboimSly.Foundations.Brownian.Bernoulli

import Mathlib

/-!
# The core estimate of the self-intersection claim

ES22 Claim 9.4, Steps 2 and 3, and the combination of Step 1.

Fix `ζ ∈ (0, 1/100]` and `t ≥ 1` with the thresholds `SiGood ζ t`. The block events `E_j` and the
good events `G_j = G(s_j)` satisfy the hypothesis of the adapted Bernoulli bound (adapted Bernoulli trials: upper tail)
with `p = r^{-1/2}`. Together with the deterministic bound of Step 1 this gives

`P (|T| ≥ t^{1-ζ³}) ≤ e^{-m_*/2} + P (G(t+1))ᶜ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → R5}

/-- ES22 Claim 9.4, Step 2: `P (E_j ∩ G_j ∩ F) ≤ p P (G_j ∩ F)`
for `F ∈ ℱ_{s_j}`, with `p = r^{-1/2}`. -/
theorem block_step [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P) {ζ t : ℝ}
    (hζ : 0 < ζ) (ht : 1 ≤ t) (hg : SiGood ζ t) (j : ℕ) {F : Set Ω}
    (hF : MeasurableSet[bmFiltration B (blkT (siR ζ t ^ 2) j)] F) :
    P (blkE B (siR ζ t ^ 2) (siK ζ t) (siRho ζ t) j ∩
        good B t (siRho ζ t) (3 * siBig ζ t) (siM ζ t) (blkT (siR ζ t ^ 2) j) ∩ F) ≤
      ENNReal.ofReal (siR ζ t ^ (-(1 : ℝ) / 2)) *
        P (good B t (siRho ζ t) (3 * siBig ζ t) (siM ζ t) (blkT (siR ζ t ^ 2) j) ∩ F) := by
  have hr1 := siR_one_le hζ ht
  have hr0 : 0 ≤ siR ζ t ^ 2 := by positivity
  have hb := blkT_succ hr0 j
  have hI : ∀ i ∈ blkI (siR ζ t ^ 2) (siK ζ t) j,
      (blkT (siR ζ t ^ 2) j : ℝ) + siK ζ t - 1 ≤ i ∧ (i : ℝ) ≤ blkT (siR ζ t ^ 2) (j + 1) := by
    intro i hi
    unfold blkI at hi
    rw [Finset.mem_Icc] at hi
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hi.1),
      (by exact_mod_cast hi.2 : (i : ℝ) ≤ (⌊(blkT (siR ζ t ^ 2) (j + 1) : ℝ)⌋₊ : ℝ)).trans
        (Nat.floor_le (NNReal.coe_nonneg _))⟩
  have hcard : ((blkI (siR ζ t ^ 2) (siK ζ t) j).card : ℝ) ≤ siR ζ t ^ 2 := by
    unfold blkI
    rw [Nat.card_Icc]
    set c := ⌈(blkT (siR ζ t ^ 2) j : ℝ) + siK ζ t - 1⌉₊ with hc
    set f := ⌊(blkT (siR ζ t ^ 2) (j + 1) : ℝ)⌋₊ with hf
    have hc1 : (blkT (siR ζ t ^ 2) j : ℝ) + siK ζ t - 1 ≤ c := Nat.le_ceil _
    have hf1 : (f : ℝ) ≤ blkT (siR ζ t ^ 2) (j + 1) := Nat.floor_le (NNReal.coe_nonneg _)
    by_cases h : c ≤ f + 1
    · rw [Nat.cast_sub h]
      push_cast
      have := hg.L1
      linarith
    · rw [Nat.sub_eq_zero_of_le (by omega)]
      simpa using hr0
  have hbb := block_bound hB (a := blkT (siR ζ t ^ 2) j) (b := blkT (siR ζ t ^ 2) (j + 1))
    (t := t) (ρ := siRho ζ t) (R := siBig ζ t) (M := siM ζ t) (r := siR ζ t) (K := siK ζ t)
    (N := siR ζ t ^ 2) (blkI (siR ζ t ^ 2) (siK ζ t) j) ht (siRho_one_le hζ ht) hg.L2
    (siM_nonneg hζ ht) hg.L1 hr1 hb hI hcard hF
  rw [Set.inter_assoc]
  refine hbb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  exact hg.L3

open scoped Classical in
omit mΩ in
/-- The count of `j < J` with `ω ∈ E_j` is the Bernoulli count when `ω ∈ G_j` for `j < J`. -/
lemma card_filter_eq_bernCount {E G : ℕ → Set Ω} {ω : Ω} {J : ℕ} (hG : ∀ j < J, ω ∈ G j) :
    ((Finset.range J).filter fun j => ω ∈ E j).card = bernCount E G J ω := by
  classical
  unfold bernCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := hG j (Finset.mem_range.1 hj)
  by_cases h : ω ∈ E j
  · simp [h, Set.indicator_of_mem (show ω ∈ E j ∩ G j from ⟨h, hj'⟩)]
  · simp [h]

/-- ES22 Claim 9.4, Steps 1 and 3. For `t ≥ 1` with `SiGood ζ t`,
`P (|T| ≥ t^{1-ζ³}) ≤ e^{-m_*/2} + P (G(t+1))ᶜ`. -/
theorem core_bound [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P) {ζ t : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) (ht : 1 ≤ t) (hg : SiGood ζ t) :
    P {ω | ENNReal.ofReal (t ^ (1 - ζ ^ 3)) ≤
        nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ ζ)) (Real.toNNReal t) ω)} ≤
      ENNReal.ofReal (Real.exp (-siMstar ζ t / 2)) +
        P (good B t (siRho ζ t) (3 * siBig ζ t) (siM ζ t) (Real.toNNReal (t + 1)))ᶜ := by
  classical
  have hr1 := siR_one_le hζ ht
  have hr0 : 0 ≤ siR ζ t ^ 2 := by positivity
  have hrsq := siR_sq (ζ := ζ) ht
  set r2 : ℝ := siR ζ t ^ 2 with hr2def
  set G : ℕ → Set Ω := fun j =>
    good B t (siRho ζ t) (3 * siBig ζ t) (siM ζ t) (blkT r2 j) with hGdef
  set E : ℕ → Set Ω := fun j => blkE B r2 (siK ζ t) (siRho ζ t) j with hEdef
  set J : ℕ := siJ ζ t with hJdef
  have h𝒢 : Monotone fun j => bmFiltration B (blkT r2 j) :=
    fun i j hij => bmFiltration_mono B (blkT_mono hr0 hij)
  have hle : ∀ j, bmFiltration B (blkT r2 j) ≤ mΩ := fun j => bmFiltration_le hB.measurable _
  have hGm : ∀ j, MeasurableSet[bmFiltration B (blkT r2 j)] (G j) := fun j =>
    measurableSet_good hB _ _ _ _ _
  have hEm : ∀ j, MeasurableSet[bmFiltration B (blkT r2 (j + 1))] (E j) := fun j => by
    refine measurableSet_blockEvent hB (blkT_mono hr0 (Nat.le_succ j)) _ ?_ _
    intro i hi
    unfold blkI at hi
    rw [Finset.mem_Icc] at hi
    rw [← NNReal.coe_le_coe]
    push_cast
    exact (by exact_mod_cast hi.2 : (i : ℝ) ≤ (⌊(blkT r2 (j + 1) : ℝ)⌋₊ : ℝ)).trans
      (Nat.floor_le (NNReal.coe_nonneg _))
  have hp0 : 0 ≤ siR ζ t ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (siR_pos hζ ht).le _
  have hbern := bernoulli_upper_tail (P := P) h𝒢 hle hGm hEm hp0
    (fun j F hF => by
      exact block_step hB hζ ht hg j hF) J (siMstar ζ t)
  have hbern' : P {ω | siMstar ζ t ≤ (bernCount E G J ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-siMstar ζ t / 2)) := by
    refine hbern.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have := pJ_le hζ ht hζ1 hg.L4
    linarith
  -- the deterministic part
  have hsub : {ω | ENNReal.ofReal (t ^ (1 - ζ ^ 3)) ≤
        nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ ζ)) (Real.toNNReal t) ω)} ⊆
      {ω | siMstar ζ t ≤ (bernCount E G J ω : ℝ)} ∪
        (good B t (siRho ζ t) (3 * siBig ζ t) (siM ζ t) (Real.toNNReal (t + 1)))ᶜ := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Set.notMem_compl_iff] at hno
    obtain ⟨hbc, hgood⟩ := hno
    -- the endpoints of the blocks lie below `t`
    have hJt : (J : ℝ) * r2 ≤ t := by
      calc (J : ℝ) * r2 ≤ t ^ (1 - ζ) * t ^ ζ :=
            mul_le_mul (siJ_le ht) hrsq.le hr0 (Real.rpow_nonneg (by linarith) _)
        _ = t := by rw [← Real.rpow_add (by linarith)]; simp
    have hGall : ∀ j < J, ω ∈ G j := by
      intro j hj
      refine good_anti B _ _ _ _ ?_ hgood
      rw [← NNReal.coe_le_coe, blkT_coe hr0, Real.coe_toNNReal _ (by linarith)]
      have : (j : ℝ) ≤ J := by exact_mod_cast hj.le
      nlinarith
    have hcard := card_filter_eq_bernCount (E := E) (G := G) hGall
    have hL : ((Real.toNNReal (t ^ ζ) : ℝ≥0) : ℝ) = r2 := by
      rw [Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _)]
      exact hrsq.symm
    have hdet := sepVol_le (B := B) (ω := ω) (ρ := siRho ζ t) (t := Real.toNNReal t) hr0 hg.L1 hL J
      (by have := siR_pos hζ ht; positivity)
    -- bound the pieces
    have hcard_le : ((((Finset.range J).filter fun j => ω ∈ blkE B r2 (siK ζ t) (siRho ζ t) j).card
        : ℕ) : ℝ) ≤ siMstar ζ t := by
      rw [show ((Finset.range J).filter fun j => ω ∈ blkE B r2 (siK ζ t) (siRho ζ t) j) =
        (Finset.range J).filter fun j => ω ∈ E j from rfl, hcard]
      exact hbc.le
    have hJK := siJ_mul_siK_le (ζ := ζ) ht
    have hJlt := lt_siJ_add_one ζ t
    have htJ : t - blkT r2 J ≤ r2 := by
      rw [blkT_coe hr0]
      have h1 : t = t ^ (1 - ζ) * r2 := by
        rw [hrsq, ← Real.rpow_add (by linarith)]; simp
      nlinarith
    have herr := err_le hζ hζ1 ht hg.L5
    have hms : siMstar ζ t * r2 = t ^ (1 - 11 / 10 * ζ + ζ) := by
      unfold siMstar
      rw [hrsq, ← Real.rpow_add (by linarith)]
    have hpos : 0 < t ^ (1 - ζ ^ 3) := Real.rpow_pos_of_pos (by linarith) _
    -- assemble
    have hTle : nnLebesgue (sepSet B 1 (Real.toNNReal (t ^ ζ)) (Real.toNNReal t) ω) ≤
        ENNReal.ofReal (t ^ (1 - ζ ^ 2) + t ^ (1 - 11 / 10 * ζ + ζ) + t ^ ζ) := by
      refine hdet.trans ?_
      have e1 : (J : ℝ≥0∞) * ENNReal.ofReal (siK ζ t) = ENNReal.ofReal (J * siK ζ t) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      have e2 : (((Finset.range J).filter fun j => ω ∈ blkE B r2 (siK ζ t) (siRho ζ t) j).card
          : ℝ≥0∞) * ENNReal.ofReal r2 = ENNReal.ofReal
          ((((Finset.range J).filter fun j => ω ∈ blkE B r2 (siK ζ t) (siRho ζ t) j).card : ℕ)
            * r2) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      have e3 : (((Real.toNNReal t - blkT r2 J : ℝ≥0)) : ℝ≥0∞) ≤ ENNReal.ofReal (t ^ ζ) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [NNReal.coe_sub_def, Real.coe_toNNReal _ (by linarith)]
        refine max_le ?_ (Real.rpow_nonneg (by linarith) _)
        rw [← hrsq]; exact htJ
      rw [e1, e2]
      refine (add_le_add (add_le_add le_rfl le_rfl) e3).trans ?_
      have hK0 := siK_nonneg hζ ht
      have hq0 : 0 ≤ t ^ ζ := Real.rpow_nonneg (by linarith) _
      rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hK0)
          (mul_nonneg (Nat.cast_nonneg _) hr0),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hK0)
          (mul_nonneg (Nat.cast_nonneg _) hr0)) hq0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hc0 : (0 : ℝ) ≤ r2 := hr0
      have : (((Finset.range J).filter fun j => ω ∈ blkE B r2 (siK ζ t) (siRho ζ t) j).card : ℝ)
          * r2 ≤ siMstar ζ t * r2 := mul_le_mul_of_nonneg_right hcard_le hc0
      have hJK' := siJ_mul_siK_le (ζ := ζ) ht
      linarith
    have hlt : ENNReal.ofReal (t ^ (1 - ζ ^ 2) + t ^ (1 - 11 / 10 * ζ + ζ) + t ^ ζ) <
        ENNReal.ofReal (t ^ (1 - ζ ^ 3)) :=
      (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
    exact absurd (hω.trans hTle) (not_le.2 hlt)
  calc _ ≤ P ({ω | siMstar ζ t ≤ (bernCount E G J ω : ℝ)} ∪
        (good B t (siRho ζ t) (3 * siBig ζ t) (siM ζ t) (Real.toNNReal (t + 1)))ᶜ) :=
        measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add hbern' le_rfl)

end ElboimSly.Brownian
