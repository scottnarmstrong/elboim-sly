/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelLaw
public import ElboimSly.Paper.Step.Cor72
public import ElboimSly.Paper.Step.RegenPath
public import ElboimSly.Foundations.Concentration.FreedmanIndep
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# The engine of Lemmas 7.3 and 7.4 (conditional on Corollary 7.2)

ES22 Lemma 7.3; ES22 Lemma 7.4. Both proofs share the same four steps: the natural coupling
with `k` blocks of length `h` (Corollary 7.2, here the hypothesis `StepCor72`), truncation of the
block endpoints, Freedman's inequality for the independent centred truncated endpoints
(`concFreedman_indep`), and a union bound. `step_travel_engine` is that argument with the
parameters (`k`, `h`, truncation level `K`, Freedman level `x`, tail bound `p`, second-moment bound
`v`) left free.

**Conditional**: `step_travel_engine` assumes `StepCor72` (the conclusion of ES22 Corollary 7.2), isolated
in `Cor72.lean`; it is not the source Corollary 7.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem stepPartial_const (T : ℝ≥0) (j : ℕ) : stepPartial (fun _ => T) j = (j : ℝ≥0) * T := by
  simp [stepPartial, Finset.sum_const, nsmul_eq_mul]

theorem isRegPath_stepWj {Y : ℝ≥0 → Fin d → ℤ} (hY : Y ∈ StepPath d) (a : ℝ≥0) (s : ℕ → ℝ≥0)
    (j : ℕ) : IsRegPath (stepWj β a s Y j) := by
  have h1 : IsRegPath (stepReg β (stepShift (a + stepPartial s j) Y)) :=
    isRegPath_stepReg (stepShift_mem hY _).toIsRegPath
  exact stopPath_isRegPath h1 (s j)

/-- A path in the complement of `farSet K T`, regular, is `< K` on all of `[0, T]`. -/
theorem lt_of_not_mem_farSet {w : ℝ≥0 → Fin d → ℤ} (hw : IsRegPath w) {K : ℝ} {T v : ℝ≥0}
    (hv : v ≤ T) (hn : w ∉ farSet K T) : ‖w v‖ < K := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨q, hq, hKq⟩ := exists_check_of_rc hw.rc hv (P := fun z => K ≤ ‖z‖) hcon
  exact hn (mem_iUnion₂.2 ⟨q, hq, hKq⟩)

/-- **Pathwise bound.** If the natural coupling is `ε`-close to `W`, no block leaves
`(-K, K)`, and the partial sums of the truncated endpoints are below `x`, then
`‖W(u)‖ < ε + K + x` for every `u ≤ kT`. -/
theorem travel_pathwise {Y : ℝ≥0 → Fin d → ℤ} (hY : Y ∈ StepPath d) (T : ℝ≥0) (k : ℕ)
    (hk : 1 ≤ k) {K x ε : ℝ}
    (hE1 : ∀ u ≤ (k : ℝ≥0) * T, ‖stepReg β (stepShift 0 Y) u -
      stepNatTilde β 0 (fun _ => T) k Y u‖ < ε)
    (hE2 : ∀ i < k, stepWj β 0 (fun _ => T) Y i ∉ farSet K T)
    (hE3 : ∀ j ≤ k, ‖∑ i ∈ Finset.range j, truncEnd T K (stepWj β 0 (fun _ => T) Y i)‖ < x)
    (u : ℝ≥0) (hu : u ≤ (k : ℝ≥0) * T) : ‖stepReg β Y u‖ < ε + K + x := by
  set s : ℕ → ℝ≥0 := fun _ => T with hs
  obtain ⟨j, hjk, hlow, hup⟩ := exists_block s k hk u
  have hSj : stepPartial s j = (j : ℝ≥0) * T := stepPartial_const T j
  have hexp := stepNatTilde_apply β 0 s k Y j u hjk hlow hup
  have hsum : ∑ i ∈ Finset.range j, stepWalkZ β 0 s Y i (s i) =
      ∑ i ∈ Finset.range j, truncEnd T K (stepWj β 0 s Y i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < k := lt_of_lt_of_le (Finset.mem_range.1 hi) hjk.le
    rw [truncEnd, Set.indicator_of_mem (show stepWj β 0 s Y i ∈ (farSet K T)ᶜ from hE2 i hik)]
    simp [stepWj, hs]
  have hv : u - stepPartial s j ≤ T := by
    rw [tsub_le_iff_left, hSj]
    by_cases hj1 : j + 1 < k
    · have := hup hj1
      rw [stepPartial_const] at this
      calc u ≤ ((j + 1 : ℕ) : ℝ≥0) * T := this
        _ = (j : ℝ≥0) * T + T := by push_cast; ring
    · have hjk' : j = k - 1 := by omega
      calc u ≤ (k : ℝ≥0) * T := hu
        _ = (j : ℝ≥0) * T + T := by
          have : (k : ℝ≥0) = j + 1 := by rw [hjk']; exact_mod_cast (Nat.sub_add_cancel hk).symm
          rw [this]; ring
  have hZj : ‖stepWalkZ β 0 s Y j (u - stepPartial s j)‖ < K := by
    have := lt_of_not_mem_farSet (isRegPath_stepWj (β := β) hY 0 s j) hv (hE2 j hjk)
    have hmin : min (u - stepPartial s j) (s j) = u - stepPartial s j := min_eq_left hv
    simp only [stepWj, hmin] at this
    exact this
  have hW : stepReg β (stepShift 0 Y) u = stepReg β Y u := by
    rw [stepShift, shiftPath_zero hY]
  have h1 := hE1 u hu
  have h2 : ‖stepNatTilde β 0 s k Y u‖ < x + K := by
    rw [hexp, hsum]
    calc _ ≤ ‖∑ i ∈ Finset.range j, truncEnd T K (stepWj β 0 s Y i)‖ +
          ‖stepWalkZ β 0 s Y j (u - stepPartial s j)‖ := norm_add_le _ _
      _ < x + K := add_lt_add (hE3 j hjk.le) hZj
  rw [hW] at h1
  calc ‖stepReg β Y u‖ = ‖(stepReg β Y u - stepNatTilde β 0 s k Y u) + stepNatTilde β 0 s k Y u‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖stepReg β Y u - stepNatTilde β 0 s k Y u‖ + ‖stepNatTilde β 0 s k Y u‖ := norm_add_le _ _
    _ < ε + K + x := by linarith

omit [Fact (0 < β)] in
theorem sum_travelX {Ω : Type} {Y : Ω → PathSpace d} (a T : ℝ≥0) (K : ℝ) (ω : Ω) (j : ℕ) :
    ∑ i ∈ Finset.range j, travelX β a T K Y i ω =
      fun c => (((∑ i ∈ Finset.range j, truncEnd T K (stepWj β a (fun _ => T) (Y ω) i)) c : ℤ) :
        ℝ) := by
  funext c
  simp [travelX, Finset.sum_apply]

/-- **The engine of Lemmas 7.3 and 7.4** (conditional on `StepCor72`, the conclusion of
Corollary 7.2). In the regime `SR(n₁; β, n, t₀)`, for `k` blocks of length `h` with
`4^{n₁} < h ≤ 4ⁿ` and `kh ≤ t_n`, with truncation level `K`, Freedman level `x`, tail bound `p` for
a block exceeding `K`, and second-moment bound `v`:
`ℙ(∃ s ≤ kh, k t_n^{2ε} + K + x ≤ ‖W(s)‖) ≤ (k-1)e^{-c n³} + k p + 2d exp(-x²/(2(kv + Kx/3)))`. -/
theorem step_travel_engine (hd : 1 ≤ d) {cCat : ℝ} {βCat : ℕ → ℝ}
    (hCor : StepCor72 d cCat βCat) {n₁ n : ℕ} {t₀ : ℝ} (hR : StepRegime d n₁ β n t₀)
    (hβc : βCat n₁ ≤ β) (hβ : (12 : ℝ) ^ 16 ≤ β) {k : ℕ} (hk : 1 ≤ k) {h : ℝ}
    (h1 : (4 : ℝ) ^ n₁ < h) (h2 : h ≤ 4 ^ n) (hkh : (k : ℝ) * h ≤ indScale t₀ n)
    {K x v p : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x)
    (hv : 6 * d * h + 2 * h ^ (2 * indThetaH) + K ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2)) ≤ v)
    (hV : 0 < (k : ℝ) * v)
    {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (htail : Pe.real {ω | ∃ s : ℝ≥0, s ≤ h.toNNReal ∧
      K ≤ ‖regenWalk (fun j => copyEnv (N ω) j) (s : ℝ)‖} ≤ p) :
    Pe.real {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ k * h ∧
        (k : ℝ) * indScale t₀ n ^ (2 * heavyEps d) + K + x ≤
          ‖regenWalk (fun j => copyEnv (N ω) j) (s : ℝ)‖} ≤
      ((k : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3)) + k * p +
        2 * d * Real.exp (-(x ^ 2 / (2 * ((k : ℝ) * v + K * x / 3)))) := by
  have hPe := hN.isProbabilityMeasure
  obtain ⟨Ω', _, P', N₀, hP', hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hY : IsSRW P' (canonical d N₀) := canonical_isSRW hN₀
  have hYp : ∀ ω, canonical d N₀ ω ∈ StepPath d := fun ω => walkPath_isDriving (N₀ ω)
  have hP'prob : IsProbabilityMeasure P' := hY.isProbabilityMeasure
  set Y := canonical d N₀ with hYdef
  have hh1 : 1 < h := lt_of_le_of_lt (one_le_pow₀ (by norm_num)) h1
  set T : ℝ≥0 := h.toNNReal with hT
  have hTc : (T : ℝ) = h := Real.coe_toNNReal h (by linarith)
  have hTpos : 0 < T := by rw [← NNReal.coe_pos, hTc]; linarith
  set s : ℕ → ℝ≥0 := fun _ => T with hs
  have hS : ((stepPartial s k : ℝ≥0) : ℝ) = k * h := by
    rw [stepPartial_const]; push_cast; rw [hTc]
  set ε : ℝ := (k : ℝ) * indScale t₀ n ^ (2 * heavyEps d) with hε
  set kT : ℝ≥0 := (k : ℝ≥0) * T with hkT
  have hkTc : (kT : ℝ) = k * h := by rw [hkT]; push_cast; rw [hTc]
  -- the events
  set E1 : Set Ω' := {ω | ∃ u : ℝ≥0, u ≤ stepPartial s k ∧ ε ≤
    ‖stepReg β (stepShift 0 (Y ω)) u - stepNatTilde β 0 s k (Y ω) u‖} with hE1
  set E2 : Set Ω' := ⋃ i ∈ Finset.range k, {ω | stepWj β 0 s (Y ω) i ∈ farSet K T} with hE2
  set E3 : Set Ω' := {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩
    (fun j => ‖∑ i ∈ Finset.range j, travelX β 0 T K Y i ω‖)} with hE3
  have hP1 : P'.real E1 ≤ ((k : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3)) :=
    hCor n₁ hR.1 β n t₀ hβc hR Ω' P' Y hY hYp 0 k s hk (fun _ => hTpos) (by
      rw [hS]; exact hkh)
  have hP2 : P'.real E2 ≤ k * p := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    have : ∀ i ∈ Finset.range k, P'.real {ω | stepWj β 0 s (Y ω) i ∈ farSet K T} ≤ p := by
      intro i _
      refine le_trans ?_ htail
      rw [Measure.real, Measure.real, measure_stepWj_farSet (β := β) hY hYp hN 0 T K i]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (ppLaw_tail hN T K)
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have hP3 : P'.real E3 ≤ 2 * d * Real.exp (-(x ^ 2 / (2 * ((k : ℝ) * v + K * x / 3)))) := by
    have hsq : ∀ (i : Fin k) (c : Fin d), ∫ ω, (travelX β 0 T K Y i ω c) ^ 2 ∂P' ≤ v := fun i c =>
      integral_travelX_sq_le hY hYp hN 0 T hK
        (by simpa [hT] using ppLaw_second_moment hR hβ h1 h2 hK hN |>.trans hv) i c
    exact concFreedman_indep hd (X := travelX β 0 T K Y) (b := K) (V := k * v) (x := x)
      (fun i => measurable_travelX hY hYp 0 T K i) (iIndepFun_travelX hY hYp 0 T K k) hK
      (fun i => Filter.Eventually.of_forall fun ω => norm_travelX 0 T hK i ω)
      (fun i => integral_travelX hY hYp hN 0 T hK i)
      (fun c => by
        refine (Finset.sum_le_sum fun i _ => hsq i c).trans ?_
        simp)
      hx hV
  -- pathwise inclusion
  have hsub : {ω | (fun t : ℝ≥0 => stepReg β (Y ω) t) ∈ farSet (ε + K + x) kT} ⊆
      (E1 ∪ E2) ∪ E3 := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨c1, c2⟩, c3⟩ := hcon
    obtain ⟨q, hq, hRq⟩ := mem_iUnion₂.1 hω
    have hqle : q ≤ kT := checkTimes_le hq
    have key := travel_pathwise (β := β) (hYp ω) T k hk (K := K) (x := x) (ε := ε)
      (fun u hu => by
        by_contra hcon
        exact c1 ⟨u, by rw [stepPartial_const]; exact hu, not_lt.1 hcon⟩)
      (fun i hi => fun hmem => c2 (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hmem⟩))
      (fun j hj => by
        have hle := Finset.le_sup' (fun j => ‖∑ i ∈ Finset.range j, travelX β 0 T K Y i ω‖)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
        have hlt : (Finset.range (k + 1)).sup' ⟨0, by simp⟩
            (fun j => ‖∑ i ∈ Finset.range j, travelX β 0 T K Y i ω‖) < x := not_le.1 c3
        have := hle.trans_lt hlt
        rw [sum_travelX, norm_intCast_pi] at this
        exact this) q hqle
    exact absurd hRq (not_le.2 key)
  have hfar : P'.real {ω | (fun t : ℝ≥0 => stepReg β (Y ω) t) ∈ farSet (ε + K + x) kT} ≤
      ((k : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3)) + k * p +
        2 * d * Real.exp (-(x ^ 2 / (2 * ((k : ℝ) * v + K * x / 3)))) :=
    calc _ ≤ P'.real ((E1 ∪ E2) ∪ E3) := measureReal_mono hsub
      _ ≤ P'.real (E1 ∪ E2) + P'.real E3 := measureReal_union_le _ _
      _ ≤ (P'.real E1 + P'.real E2) + P'.real E3 := by gcongr; exact measureReal_union_le _ _
      _ ≤ _ := by linarith
  -- transfer to the Poisson environment
  have hlaw := stepReg_law hY hYp hN
  have hm : Measurable fun ω (t : ℝ≥0) => stepReg β (Y ω) t :=
    measurable_stepReg_path hY.1 fun ω => (hYp ω).toIsRegPath
  have hae := aemeasurable_ppPath hN
  refine le_trans ?_ hfar
  rw [Measure.real, Measure.real]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  have e1 : P' ((fun ω (t : ℝ≥0) => stepReg β (Y ω) t) ⁻¹' farSet (ε + K + x) kT) =
      Pe ((ppPath N) ⁻¹' farSet (ε + K + x) kT) := by
    rw [← Measure.map_apply hm (measurableSet_farSet _ _),
      ← Measure.map_apply_of_aemeasurable hae (measurableSet_farSet _ _)]
    have hlaw' : P'.map (fun ω (t : ℝ≥0) => stepReg β (Y ω) t) = Pe.map (ppPath N) := hlaw
    rw [hlaw']
  refine le_trans (measure_mono_ae ?_) (le_of_eq e1.symm)
  filter_upwards [Cyclic.ae_cycGood hN] with ω hω hmem
  obtain ⟨u, hu, hRu⟩ := hmem
  have hrc : ∀ u : ℝ≥0, ∀ᶠ v : ℝ≥0 in 𝓝[≥] u, ppPath N ω v = ppPath N ω u := fun u => by
    simp only [copyEnv_eq_cycSlice, ppPath]
    exact regenWalk_rc hω u
  have huk : u ≤ kT := by rw [← NNReal.coe_le_coe, hkTc]; exact hu
  obtain ⟨q, hq, hKq⟩ := exists_check_of_rc hrc huk (P := fun z => ε + K + x ≤ ‖z‖) hRu
  exact mem_iUnion₂.2 ⟨q, hq, hKq⟩

end ElboimSly.Paper.Step
