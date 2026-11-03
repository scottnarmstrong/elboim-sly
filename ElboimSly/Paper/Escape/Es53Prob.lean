/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53BM
public import ElboimSly.Paper.Escape.Es53Core
public import ElboimSly.Paper.Avoid.CoreBad
public import ElboimSly.Paper.Avoid.Claim2Final
public import ElboimSly.Paper.Avoid.Hyp
public import ElboimSly.Foundations.Cyclic.CycFast
public import Mathlib

/-!
# The probability of `𝒥` for the regenerated walk

ES22 Lemma 5.3, the bounds on `ℬ`, `ℬ'`, `𝒞`, `𝒟`, `𝒢`.  For the regenerated walk
`W = avoidPath N` (the walk `W'_i - p_i`), each event has an error bound from ES22 Claim 4.3
(`ℬ`, `ℬ'`), ES22 Claim 4.2 (`𝒞`), ES22 Claim 2.3 (`𝒟`) and the induction hypothesis at arbitrary times (d) with
ES22 Lemma 5.3: the event ℐ (`𝒢`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}

/-- The absolute path `p + W`. -/
noncomputable def absPath (p : Fin (k + 2) → ℤ) (N : Ω → Measure (CycS ℕ (k + 2) β)) (ω : Ω) :
    ℝ≥0 → Fin (k + 2) → ℤ := fun q => p + avoidPath N ω q

omit [Fact (0 < β)] [MeasurableSpace Ω] in
theorem norm_absPath_sub (p : Fin (k + 2) → ℤ) (ω : Ω) (q : ℝ≥0) :
    ‖absPath p N ω q - p‖ = ‖avoidPath N ω q‖ := by
  unfold absPath; rw [add_sub_cancel_left]

/-- The error terms of `ℬ`. -/
noncomputable def errB (C : ℝ) (k m₁ n : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ Finset.Icc m₁ n, ENNReal.ofReal
    (C * (2 ^ (m + 3) / (m : ℝ)) ^ k * ((4 : ℝ) ^ m) ^ (-(k : ℝ) / 2))

theorem prob_B_bad (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ (k + 2) β)),
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        ∀ (p : Fin (k + 2) → ℤ) {m₁ : ℕ}, n₀ + 1 ≤ m₁ →
        (∀ m : ℕ, 1 ≤ m → ((4 : ℝ) ^ m) ^ indThetaH ≤ 2 ^ (m + 3) / m) →
        Pr {ω | ¬ EsB n m₁ p (absPath p N ω)} ≤ errB C k m₁ n := by
  obtain ⟨C, hC, H⟩ := es4_claim3_bad_process (d := k + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN p m₁ hm₁ hθ
  have := hN.isProbabilityMeasure
  have hsub : {ω | ¬ EsB n m₁ p (absPath p N ω)} ⊆
      ⋃ m ∈ Finset.Icc m₁ n, {ω | ∃ q ∈ qSet (((4 : ℝ) ^ m).toNNReal) (((4 : ℝ) ^ n).toNNReal),
        ‖avoidPath N ω q‖ < 2 ^ (m + 3) / m} := by
    intro ω hω
    simp only [EsB, not_forall, not_not] at hω
    obtain ⟨m, hm1, hm2, q, hq, hlt⟩ := hω
    simp only [mem_iUnion, mem_ofPred_eq, Finset.mem_Icc]
    refine ⟨m, ⟨hm1, hm2⟩, q, hq, ?_⟩
    rwa [norm_absPath_sub] at hlt
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  unfold errB
  refine Finset.sum_le_sum fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have hm1 : 1 ≤ m := by omega
  have h1 : (4 : ℝ) ^ (n₀ + 1) ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (4 : ℝ) ^ m ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hm.2
  have := H β n₀ n t₀ hp Pr N hN (t := (4 : ℝ) ^ m) (L := 2 ^ (m + 3) / m) h1 h2 (hθ m hm1)
    Pr (avoidPath N) (aemeasurable_avoidPath hN) rfl
  simpa using this

theorem prob_B'_bad (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ (k + 2) β)),
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        ∀ (p : Fin (k + 2) → ℤ) (j : ℕ), (4 : ℝ) ^ (n₀ + 1) ≤ (j : ℝ) * 4 ^ j →
        (j : ℝ) * 4 ^ j ≤ 4 ^ n → ((j : ℝ) * 4 ^ j) ^ indThetaH ≤ 2 ^ j →
        Pr {ω | ¬ EsB' n j p (absPath p N ω)} ≤
          ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ k * ((j : ℝ) * 4 ^ j) ^ (-(k : ℝ) / 2)) := by
  obtain ⟨C, hC, H⟩ := es4_claim3_bad_process (d := k + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN p j h1 h2 hθ
  have := hN.isProbabilityMeasure
  have := H β n₀ n t₀ hp Pr N hN (t := (j : ℝ) * 4 ^ j) (L := 2 ^ j) h1 h2 hθ
    Pr (avoidPath N) (aemeasurable_avoidPath hN) rfl
  refine le_trans (measure_mono ?_) (by simpa using this)
  intro ω hω
  simp only [EsB', not_not] at hω
  obtain ⟨q, hq, hlt⟩ := hω
  exact ⟨q, hq, by rwa [norm_absPath_sub] at hlt⟩

theorem prob_C_bad (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ (k + 2) β)),
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        ∀ (p : Fin (k + 2) → ℤ) (A : Set (Fin (k + 2) → ℤ)) {L : ℝ},
        (4 : ℝ) ^ (n₀ + 1) ≤ L → L ≤ (4 : ℝ) ^ n → (∀ z ∈ A, L ≤ ‖z - p‖) →
        (∀ r : ℝ, L ≤ r → ((A ∩ {z | ‖z - p‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)) →
        Pr {ω | ¬ EsC n A (absPath p N ω)} ≤ ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 30)) := by
  obtain ⟨C, hC, H⟩ := es4_claim2_bad_process (d := k + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN p A L hL1 hL2 hA1 hA2
  have := hN.isProbabilityMeasure
  set Ar : Set (Fin (k + 2) → ℤ) := (fun z => p + z) ⁻¹' A with hAr
  have hA1' : ∀ z ∈ Ar, L ≤ ‖z‖ := by
    intro z hz
    have := hA1 (p + z) hz
    rwa [add_sub_cancel_left] at this
  have hA2' : ∀ r : ℝ, L ≤ r → ((Ar ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
    intro r hr
    refine le_trans ?_ (hA2 r hr)
    have hfin : (A ∩ {z | ‖z - p‖ ≤ r}).Finite := (box_finite p r).subset Set.inter_subset_right
    have hsub : (fun z => p + z) '' (Ar ∩ {u | ‖u‖ ≤ r}) ⊆ A ∩ {z | ‖z - p‖ ≤ r} := by
      rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
      exact ⟨hz1, by simpa using hz2⟩
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_image_of_injective _ (add_right_injective p)] at this
    exact_mod_cast this
  have := H β n₀ n t₀ hp Pr N hN hL1 hL2 hA1' hA2' Pr (avoidPath N) (aemeasurable_avoidPath hN) rfl
  refine le_trans (measure_mono ?_) this
  intro ω hω
  simp only [EsC, not_not] at hω
  obtain ⟨q, hq, hmem⟩ := hω
  exact ⟨q, hq, hmem⟩

/-- The error terms of `𝒟`. -/
noncomputable def errD (C c : ℝ) (m₁ n : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ Finset.Icc m₁ n, ENNReal.ofReal (C * ((4 : ℝ) ^ m) ^ 2 * Real.exp (-(c * ((m : ℝ) ^ 2))))

theorem prob_D_bad (hk : 3 ≤ k) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ (k + 2) β)),
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        ∀ (p : Fin (k + 2) → ℤ) {m₁ : ℕ}, 1 ≤ m₁ →
        Pr {ω | ¬ EsD n m₁ (absPath p N ω)} ≤ errD C c m₁ n := by
  obtain ⟨Cf, cf, hCf, hcf, hf⟩ := cyc_fast.{0} (d := k + 2) (by omega)
  refine ⟨Cf, cf, hCf, hcf, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN p m₁ hm₁
  have := hN.isProbabilityMeasure
  have hβ1 : (1 : ℝ) ≤ β := le_trans (by norm_num) hp.beta_sigma
  have hfast : ∀ {L' t : ℝ}, 1 ≤ L' → 1 ≤ t →
      Pr.real {ω | cycTfast (avoidEnv N ω) L' ≤ ENNReal.ofReal t} ≤
        Cf * t ^ 2 * Real.exp (-(cf * L')) := by
    intro L' t h1 h2
    have := hf β hβ1 Ω Pr N hN h1 h2
    simpa only [avoidEnv_eq_cycSlice] using this
  have hsub : {ω | ¬ EsD n m₁ (absPath p N ω)} ⊆
      ⋃ m ∈ Finset.Icc m₁ n, {ω | cycTfast (avoidEnv N ω) ((m : ℝ) ^ 2) ≤
        ENNReal.ofReal ((4 : ℝ) ^ m)} := by
    intro ω hω
    simp only [EsD, not_forall, not_not] at hω
    obtain ⟨m, hm1, hm2, t, ht, s, hs, ht0, hst, hts1, hdisp⟩ := hω
    simp only [mem_iUnion, mem_ofPred_eq, Finset.mem_Icc]
    refine ⟨m, ⟨hm1, hm2⟩, ?_⟩
    have htT : t ≤ tn ((4 : ℝ) ^ m) := (mem_qSet_Icc bot_le ht).2
    have htm : (t : ℝ) ≤ 4 ^ m := by
      have := NNReal.coe_le_coe.2 htT
      rwa [tn, Real.coe_toNNReal _ (by positivity)] at this
    have hd : (m : ℝ) ^ 2 ≤ ‖avoidWalk N ω (t : ℝ) - avoidWalk N ω (max (s : ℝ) 0)‖ := by
      rw [max_eq_left (NNReal.coe_nonneg s)]
      have : absPath p N ω t - absPath p N ω s = avoidPath N ω t - avoidPath N ω s := by
        unfold absPath; abel
      rw [this] at hdisp
      exact hdisp
    have hmem : (t : ℝ) ∈ {t : ℝ | 0 < t ∧ ∃ s' : ℝ, t - 1 ≤ s' ∧ s' ≤ t ∧
        (m : ℝ) ^ 2 ≤ ‖avoidWalk N ω t - avoidWalk N ω (max s' 0)‖} := by
      refine ⟨by exact_mod_cast ht0, (s : ℝ), ?_, by exact_mod_cast hst, ?_⟩
      · have : (t : ℝ) ≤ s + 1 := by exact_mod_cast hts1
        linarith
      · rw [max_eq_left (NNReal.coe_nonneg s)]
        rw [max_eq_left (NNReal.coe_nonneg s)] at hd
        exact hd
    calc cycTfast (avoidEnv N ω) ((m : ℝ) ^ 2) = pathTfast (avoidWalk N ω) ((m : ℝ) ^ 2) := rfl
      _ ≤ ENNReal.ofReal (t : ℝ) := by
          unfold pathTfast
          exact iInf₂_le (f := fun t (_ : t ∈ _) => ENNReal.ofReal t) (t : ℝ) hmem
      _ ≤ ENNReal.ofReal ((4 : ℝ) ^ m) := ENNReal.ofReal_le_ofReal htm
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  unfold errD
  refine Finset.sum_le_sum fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans hm₁ hm.1)
    nlinarith
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  rw [← ofReal_measureReal (μ := Pr) (measure_ne_top Pr _)]
  exact ENNReal.ofReal_le_ofReal (hfast hm1 h4)

theorem prob_G (hk : 3 ≤ k) (hp : Es4Params (k + 2) β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    (hn53 : n53 (k + 2) ≤ n) (u : Fin (k + 2) → ℤ) {i : ℕ} (hi1 : 1 ≤ i)
    (hiI : i ≤ escIstar n (escJ n)) (hIn : escIstar n (escJ n) ≤ n ^ 3)
    (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n) (hj2 : 2 ≤ escJ n)
    (hT1 : (4 : ℝ) ^ n₀ < (escJ n : ℝ) * 4 ^ escJ n) (hT2 : (escJ n : ℝ) * 4 ^ escJ n ≤ 4 ^ n)
    (hε1 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ (n : ℝ) ^ 17 / 30)
    (hε2 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ 3 * (2 : ℝ) ^ escJ n / 40) :
    ENNReal.ofReal (cline (k + 2)) -
        ENNReal.ofReal (Real.exp (-((avoidLevel ((escJ n : ℝ) * 4 ^ escJ n) : ℕ) : ℝ) ^ 2)) ≤
      Pr {ω | EsG n (escJ n) (escIstar n (escJ n)) u i (absPath (escPoint n (escJ n) u i) N ω)} := by
  have := hN.isProbabilityMeasure
  set T' : ℝ := (escJ n : ℝ) * 4 ^ escJ n with hT'
  have hT0 : 0 < T' := lt_of_le_of_lt (by positivity) hT1
  obtain ⟨σ, hσ, hc⟩ := es4_hyp_d hp hN hT1 hT2
  have hε0 : 0 < T' ^ indThetaH := Real.rpow_pos_of_pos hT0 _
  have hG := lawW_G_ge hk hn53 u hi1 hiI hIn hj1 hj2 hσ.1 hσ.2 hε0 hε1 hε2 hc
  have hmeas : AEMeasurable (fun (ω : Ω) (t : Set.Icc (0 : ℝ≥0) T'.toNNReal) =>
      avoidWalk N ω ((t : ℝ≥0) : ℝ)) Pr := by
    have hr : Measurable (fun (w : ℝ≥0 → Fin (k + 2) → ℤ) (t : Set.Icc (0 : ℝ≥0) T'.toNNReal) =>
        w (t : ℝ≥0)) := measurable_pi_iff.2 fun t => measurable_pi_apply (t : ℝ≥0)
    exact hr.comp_aemeasurable (aemeasurable_avoidPath hN)
  rw [Measure.map_apply_of_aemeasurable hmeas (measurableSet_GsetW _ _ _ _ _ _)] at hG
  refine hG.trans (le_of_eq (congrArg Pr ?_))
  ext ω
  simp only [mem_preimage, GsetW, EsG, mem_ofPred_eq]
  have hq : ∀ q : ℝ≥0, q ∈ qSet 0 T'.toNNReal → q ≤ T'.toNNReal := fun q hq =>
    (mem_qSet_Icc bot_le hq).2
  constructor
  · rintro h ⟨q, hqs, hbad⟩
    exact h ⟨q, hqs, hq q hqs, hbad⟩
  · rintro h ⟨q, hqs, hqT, hbad⟩
    exact h ⟨q, hqs, hbad⟩

end ElboimSly.Paper.Escape
