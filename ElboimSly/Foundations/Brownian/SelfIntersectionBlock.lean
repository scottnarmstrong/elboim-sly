/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionHit
public import ElboimSly.Foundations.Brownian.Oscillation
public import ElboimSly.Foundations.Brownian.Invariance

import Mathlib

/-!
# One block of the self-intersection claim

ES22 Claim 9.4, Step 2 (iii).

For a block `[a, b]` with `b = a + r²`, the bad event `E` is: some integer time `i ∈ I` of the block
is within `1 + ρ` of the past path `B [0,a]`, or the path oscillates by more than `ρ` over a unit
time inside `[a, b]`. For every `F ∈ ℱ_a`, `P (E ∩ G(a) ∩ F)` is at most `p · P (G(a) ∩ F)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → R5}

/-- Some integer time of `I` is within `c` of the past path `B [0,a]`. -/
def hitEvent (B : ℝ≥0 → Ω → R5) (a : ℝ≥0) (I : Finset ℕ) (c : ℝ) : Set Ω :=
  {ω | ∃ i ∈ I, ∃ s' ≤ a, ‖B (i : ℝ≥0) ω - B s' ω‖ ≤ c}

/-- The path oscillates by more than `ρ` over a unit time inside `[a, b]`. -/
def oscBad (B : ℝ≥0 → Ω → R5) (a b : ℝ≥0) (ρ : ℝ) : Set Ω :=
  {ω | ∃ u v : ℝ≥0, a ≤ u ∧ u ≤ b ∧ a ≤ v ∧ v ≤ b ∧ dist u v ≤ 1 ∧ ρ < ‖B u ω - B v ω‖}

/-- The block event `E_j`. -/
def blockEvent (B : ℝ≥0 → Ω → R5) (a b : ℝ≥0) (I : Finset ℕ) (ρ : ℝ) : Set Ω :=
  hitEvent B a I (1 + ρ) ∪ oscBad B a b ρ

omit mΩ in
lemma hitEvent_eq {ω : Ω} (hc : Continuous fun u => B u ω) (a : ℝ≥0) (I : Finset ℕ) (c : ℝ) :
    ω ∈ hitEvent B a I c ↔ ∃ i ∈ I, ∀ n : ℕ, ∃ q : RatLe a,
      ‖B (i : ℝ≥0) ω - B q.1 ω‖ < c + 1 / ((n : ℝ) + 1) := by
  simp only [hitEvent, Set.mem_ofPred_eq]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rw [exists_le_iff_rat hc (B (i : ℝ≥0) ω) a c]
  refine forall_congr' fun n => ?_
  constructor
  · rintro ⟨q, hq, hqa, h⟩
    exact ⟨⟨q, hq, hqa⟩, h⟩
  · rintro ⟨⟨q, hq, hqa⟩, h⟩
    exact ⟨q, hq, hqa, h⟩

omit mΩ in
lemma measurableSet_hitEvent {m : MeasurableSpace Ω} {a b : ℝ≥0} (hab : a ≤ b) (I : Finset ℕ)
    (hI : ∀ i ∈ I, (i : ℝ≥0) ≤ b) (hc : ∀ ω, Continuous fun u => B u ω)
    (hm : ∀ u ≤ b, Measurable[m] (B u)) (c : ℝ) :
    MeasurableSet[m] (hitEvent B a I c) := by
  have e : hitEvent B a I c = ⋃ i ∈ I, ⋂ n : ℕ, ⋃ q : RatLe a,
      {ω | ‖B (i : ℝ≥0) ω - B q.1 ω‖ < c + 1 / ((n : ℝ) + 1)} := by
    ext ω
    rw [hitEvent_eq (hc ω)]
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq, exists_prop]
  rw [e]
  refine Finset.measurableSet_biUnion _ fun i hi => ?_
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_
  exact measurableSet_lt ((hm _ (hI i hi)).sub (hm _ (q.2.2.trans hab))).norm measurable_const

omit mΩ in
lemma measurableSet_oscBad {m : MeasurableSpace Ω} {a b : ℝ≥0}
    (hc : ∀ ω, Continuous fun u => B u ω) (hm : ∀ u ≤ b, Measurable[m] (B u)) (ρ : ℝ) :
    MeasurableSet[m] (oscBad B a b ρ) := by
  have e : oscBad B a b ρ = (⋂ p ∈ closePairs (denseSub (Set.Icc a b)) 1,
      {ω | ‖B p.1 ω - B p.2 ω‖ ≤ ρ})ᶜ := by
    ext ω
    have hiff := forall_closePairs_iff (w := fun u => B u ω) (hc ω)
      (Set.ordConnected_Icc (a := a) (b := b)) 1 ρ
    have h1 : ω ∈ oscBad B a b ρ ↔
        ¬ ∀ p ∈ closePairs (Set.Icc a b) 1, ‖B p.1 ω - B p.2 ω‖ ≤ ρ := by
      constructor
      · rintro ⟨u, v, hau, hub, hav, hvb, hd, hlt⟩ H
        exact absurd (H (u, v) ⟨⟨hau, hub⟩, ⟨hav, hvb⟩, hd⟩) (not_le.2 hlt)
      · intro H
        by_contra hno
        apply H
        rintro ⟨u, v⟩ ⟨⟨hau, hub⟩, ⟨hav, hvb⟩, hd⟩
        by_contra hlt
        exact hno ⟨u, v, hau, hub, hav, hvb, hd, not_le.1 hlt⟩
    rw [h1, hiff]
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine MeasurableSet.compl (MeasurableSet.biInter ?_ fun p hp => ?_)
  · exact ((denseSub_countable (Set.Icc a b)).prod (denseSub_countable (Set.Icc a b))).mono
      fun p hp => Set.mem_prod.2 ⟨hp.1, hp.2.1⟩
  · exact measurableSet_le ((hm p.1 (denseSub_subset _ hp.1).2).sub
      (hm p.2 (denseSub_subset _ hp.2.1).2)).norm measurable_const

lemma measurableSet_blockEvent [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P)
    {a b : ℝ≥0} (hab : a ≤ b) (I : Finset ℕ) (hI : ∀ i ∈ I, (i : ℝ≥0) ≤ b) (ρ : ℝ) :
    MeasurableSet[bmFiltration B b] (blockEvent B a b I ρ) :=
  (measurableSet_hitEvent hab I hI (fun ω => (hB.continuous_zero ω).1)
    (fun _ hu => measurable_bmFiltration hu) _).union
    (measurableSet_oscBad (fun ω => (hB.continuous_zero ω).1)
      (fun _ hu => measurable_bmFiltration hu) ρ)

/-- ES22 Claim 9.4, Step 2 (iii), the oscillation part: the oscillation
inside `[a, b]` is independent of `ℱ_a`. -/
theorem oscBad_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P) {a b : ℝ≥0}
    (hab : a < b) {ρ : ℝ} (hρ : 0 < ρ) {F : Set Ω} (hF : MeasurableSet[bmFiltration B a] F) :
    P (oscBad B a b ρ ∩ F) ≤
      ((20 * (⌈b - a⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-ρ ^ 2 / 16))) * P F := by
  set T : ℝ≥0 := b - a with hT
  have hT0 : T ≠ 0 := (tsub_pos_of_lt hab).ne'
  set W : Set (PathSpace 5) := {w | ∃ p ∈ closePairs (denseSub (Set.Icc 0 T)) 1,
    ρ < ‖w p.1 - w p.2‖} with hW
  have hWm : MeasurableSet W := by
    have e : W = ⋃ p ∈ closePairs (denseSub (Set.Icc 0 T)) 1, {w | ρ < ‖w p.1 - w p.2‖} := by
      ext w; simp [hW]
    rw [e]
    refine MeasurableSet.biUnion ?_ fun p _ => ?_
    · exact ((denseSub_countable (Set.Icc 0 T)).prod (denseSub_countable (Set.Icc 0 T))).mono
        fun p hp => Set.mem_prod.2 ⟨hp.1, hp.2.1⟩
    · exact measurableSet_lt measurable_const
        (((measurable_pi_apply p.1).sub (measurable_pi_apply p.2)).norm)
  have hsub : oscBad B a b ρ ⊆ shiftPath B a ⁻¹' W := by
    rintro ω ⟨u, v, hau, hub, hav, hvb, hd, hlt⟩
    have hcw : Continuous (shiftPath B a ω) := by
      have := ((hB.shift a).continuous_zero ω).1
      exact this
    by_contra hno
    have hall : ∀ p ∈ closePairs (denseSub (Set.Icc 0 T)) 1,
        ‖shiftPath B a ω p.1 - shiftPath B a ω p.2‖ ≤ ρ := fun p hp =>
      not_lt.1 fun h => hno ⟨p, hp, h⟩
    have h2 := (forall_closePairs_iff (w := shiftPath B a ω) hcw
      (Set.ordConnected_Icc (a := 0) (b := T)) 1 ρ).2 hall (u - a, v - a)
      ⟨⟨zero_le, tsub_le_tsub_right hub a⟩, ⟨zero_le, tsub_le_tsub_right hvb a⟩, ?_⟩
    · have e1 : a + (u - a) = u := add_tsub_cancel_of_le hau
      have e2 : a + (v - a) = v := add_tsub_cancel_of_le hav
      simp only [shiftPath, e1, e2] at h2
      have : B u ω - B a ω - (B v ω - B a ω) = B u ω - B v ω := by abel
      rw [this] at h2
      exact absurd hlt (not_lt.2 h2)
    · rw [NNReal.dist_eq] at hd ⊢
      have e1 : ((u - a : ℝ≥0) : ℝ) = u - a := NNReal.coe_sub hau
      have e2 : ((v - a : ℝ≥0) : ℝ) = v - a := NNReal.coe_sub hav
      have e3 : (u : ℝ) - a - ((v : ℝ) - a) = u - v := by ring
      rw [e1, e2, e3]
      simpa using hd
  have hindep := (hB.indep_shift a).symm
  rw [Indep_iff] at hindep
  have hWm' : MeasurableSet[MeasurableSpace.comap (shiftPath B a) inferInstance]
      (shiftPath B a ⁻¹' W) := ⟨W, hWm, rfl⟩
  calc P (oscBad B a b ρ ∩ F) ≤ P (F ∩ shiftPath B a ⁻¹' W) :=
        measure_mono (fun ω hω => ⟨hω.2, hsub hω.1⟩)
    _ = P F * P (shiftPath B a ⁻¹' W) := hindep F _ hF hWm'
    _ ≤ P F * ((20 * (⌈b - a⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-ρ ^ 2 / 16))) := by
        gcongr
        have hB' := hB.shift a
        have := hB'.oscillation_le (T := T) (h := 1) hT0 one_ne_zero hρ one_pos
        refine le_trans (measure_mono ?_) (this.trans (le_of_eq ?_))
        · rintro ω ⟨p, hp, hlt⟩
          refine ⟨p.1, p.2, (denseSub_subset _ hp.1).2, (denseSub_subset _ hp.2.1).2, hp.2.2, ?_⟩
          simpa [shiftPath] using hlt.le
        · simp only [div_one]; norm_num [hT]
    _ = _ := mul_comm _ _

/-- ES22 Claim 9.4, Step 2 (iii): for `F ∈ ℱ_a`,
`P (E ∩ G(a) ∩ F) ≤ p · P (G(a) ∩ F)` with
`p = N ((πK)^{-5/2} M (6ρ)^5 + 10 e^{-R²/(8r²)}) + 20 ⌈r²⌉ e^{-ρ²/16}`. Here `N` bounds the number
of integer times of the block, `K ≤ 2(i - a)` for each of them and `b = a + r²`. -/
theorem block_bound [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P) {a b : ℝ≥0}
    {t ρ R M r K N : ℝ} (I : Finset ℕ) (ht : 1 ≤ t) (hρ : 1 ≤ ρ) (hR : 2 + 4 * ρ ≤ R)
    (hM : 0 ≤ M) (hK : 2 ≤ K) (hr : 1 ≤ r) (hb : (b : ℝ) = a + r ^ 2)
    (hI : ∀ i ∈ I, (a : ℝ) + K - 1 ≤ i ∧ (i : ℝ) ≤ b) (hIc : (I.card : ℝ) ≤ N)
    {F : Set Ω} (hF : MeasurableSet[bmFiltration B a] F) :
    P (blockEvent B a b I ρ ∩ (good B t ρ (3 * R) M a ∩ F)) ≤
      ENNReal.ofReal (N * ((Real.pi * K) ^ (-(5 : ℝ) / 2) * (M * (6 * ρ) ^ 5) +
        10 * Real.exp (-R ^ 2 / (8 * r ^ 2))) +
        20 * (⌈r ^ 2⌉₊ : ℝ) * Real.exp (-ρ ^ 2 / 16)) * P (good B t ρ (3 * R) M a ∩ F) := by
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < r := by linarith
  set A : Set Ω := good B t ρ (3 * R) M a ∩ F with hAdef
  have hAF : MeasurableSet[bmFiltration B a] A :=
    @MeasurableSet.inter Ω (bmFiltration B a) _ _ (measurableSet_good hB t ρ (3 * R) M a) hF
  have hab : a < b := by
    have : (a : ℝ) < b := by rw [hb]; nlinarith
    exact_mod_cast this
  have hN : 0 ≤ N := le_trans (Nat.cast_nonneg _) hIc
  set C : ℝ := (Real.pi * K) ^ (-(5 : ℝ) / 2) * (M * (6 * ρ) ^ 5) +
        10 * Real.exp (-R ^ 2 / (8 * r ^ 2)) with hC
  have hC0 : 0 ≤ C := by positivity
  clear_value C
  -- each integer time
  have hhit : ∀ i ∈ I, P ({ω | ∃ s' ≤ a, ‖B (i : ℝ≥0) ω - B s' ω‖ ≤ 1 + ρ} ∩ A) ≤
      ENNReal.ofReal C * P A := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hI i hi
    have hai : a ≤ (i : ℝ≥0) := by
      have : (a : ℝ) ≤ i := by linarith
      exact_mod_cast this
    set v : ℝ≥0 := (i : ℝ≥0) - a with hv
    have hvR : (v : ℝ) = i - a := by rw [hv, NNReal.coe_sub hai]; simp
    have hav : a + v = (i : ℝ≥0) := add_tsub_cancel_of_le hai
    have hv1 : K - 1 ≤ (v : ℝ) := by rw [hvR]; linarith
    have hv2 : (v : ℝ) ≤ r ^ 2 := by rw [hvR]; linarith
    have hv0 : v ≠ 0 := by
      intro h; rw [h] at hv1; simp at hv1; linarith
    have hvpos : (0 : ℝ) < v := by positivity
    have h := hit_le hB hv0 ht hρ hR hM hF
    rw [hav] at h
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have e1 : (Real.pi * K) ^ (-(5 : ℝ) / 2) ≥ (2 * Real.pi * v) ^ (-(5 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Real.pi_pos]) (by norm_num)
    have e2 : Real.exp (-(R / 2) ^ 2 / (2 * v)) ≤ Real.exp (-R ^ 2 / (8 * r ^ 2)) := by
      refine Real.exp_le_exp.2 ?_
      have : R ^ 2 / (8 * r ^ 2) ≤ (R / 2) ^ 2 / (2 * v) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg R]
      rw [neg_div, neg_div]
      linarith
    have e3 : 0 ≤ M * (6 * ρ) ^ 5 := by positivity
    rw [hC]
    gcongr
  -- decomposition
  have hsub : blockEvent B a b I ρ ∩ A ⊆
      (⋃ i ∈ I, {ω | ∃ s' ≤ a, ‖B (i : ℝ≥0) ω - B s' ω‖ ≤ 1 + ρ} ∩ A) ∪ (oscBad B a b ρ ∩ A) := by
    rintro ω ⟨hω | hω, hA⟩
    · left
      obtain ⟨i, hi, hs⟩ := hω
      exact Set.mem_iUnion₂.2 ⟨i, hi, hs, hA⟩
    · right; exact ⟨hω, hA⟩
  have hosc := oscBad_le hB hab (ρ := ρ) (by linarith) hAF
  have hceil : ⌈b - a⌉₊ = ⌈r ^ 2⌉₊ := by
    have : ((b - a : ℝ≥0) : ℝ) = r ^ 2 := by
      rw [NNReal.coe_sub hab.le, hb]; ring
    rw [← this]
    exact Nonneg.nat_ceil_coe (b - a)
  rw [hceil] at hosc
  calc P (blockEvent B a b I ρ ∩ A) ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ (∑ i ∈ I, P ({ω | ∃ s' ≤ a, ‖B (i : ℝ≥0) ω - B s' ω‖ ≤ 1 + ρ} ∩ A)) +
        (20 * (⌈r ^ 2⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-ρ ^ 2 / 16)) * P A :=
        add_le_add (measure_biUnion_finset_le _ _) hosc
    _ ≤ (∑ _i ∈ I, ENNReal.ofReal C * P A) +
        (20 * (⌈r ^ 2⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-ρ ^ 2 / 16)) * P A :=
        add_le_add (Finset.sum_le_sum hhit) le_rfl
    _ = ENNReal.ofReal (I.card * C + 20 * (⌈r ^ 2⌉₊ : ℝ) * Real.exp (-ρ ^ 2 / 16)) * P A := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← add_mul, ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp
    _ ≤ _ := by
        rw [hC]
        gcongr

end ElboimSly.Brownian
