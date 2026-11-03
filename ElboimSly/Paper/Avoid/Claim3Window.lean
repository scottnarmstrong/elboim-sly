/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim2Count
public import ElboimSly.Paper.Avoid.ProcessLaw
public import ElboimSly.Paper.Avoid.Claim2Final
public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Foundations.Brownian.FarHit
public import Mathlib

/-!
# ES22 §4: Claim 4.3, the window estimate

ES22 Claim 4.3. For a window `[4^{ℓ-1}, 4^ℓ]` with `n₀ < ℓ ≤ n`, the probability that
`‖W(s)‖ < L` for some (test) time `s` of the window is at most `e^{-(ℓ-1)²}` plus
`C_far ((L + 4^{θℓ}) / 2^{ℓ-1})^{d-2}`: by the induction hypothesis at arbitrary times (d) the walk is within `4^{θℓ}` of
`σ B` (`σ ≥ 1`) except with probability `e^{-(ℓ-1)²}`, and ES22 Lemma 9.2: hitting a cube after time s^2 bounds the probability
that `σ B` enters the ball of radius `L + 4^{θℓ}` after time `4^{ℓ-1}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

theorem avoid_norm_intCast_pi {d : ℕ} (u : Fin d → ℤ) : ‖(fun i => ((u i : ℤ) : ℝ))‖ = ‖u‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    simpa [Int.norm_eq_abs] using norm_le_pi_norm u i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have := norm_le_pi_norm (fun i => ((u i : ℤ) : ℝ)) i
    simpa [Int.norm_eq_abs] using this

section

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ d β)}

/-- **Window `ℓ`** of ES22 Claim 4.3. -/
theorem es4_window3 (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) {L : ℝ} (hL : 0 < L)
    {ℓ : ℕ} (hℓ0 : n₀ < ℓ) (hℓn : ℓ ≤ n) :
    Pr {ω | ∃ q ∈ qSet ((4 : ℝ) ^ (ℓ - 1)).toNNReal ((4 : ℝ) ^ ℓ).toNNReal,
        ‖avoidWalk N ω (q : ℝ)‖ < L} ≤
      ENNReal.ofReal (Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2))) +
        ENNReal.ofReal (ElboimSly.Brownian.Cfar d *
          ((L + ((4 : ℝ) ^ ℓ) ^ indThetaH) / 2 ^ (ℓ - 1)) ^ (d - 2)) := by
  have hℓ1 : 1 ≤ ℓ := by have := hp.eight_le; omega
  have hd3 : 3 ≤ d := by have := hp.five_le; omega
  have hh1 : (4 : ℝ) ^ n₀ < 4 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hℓ0
  have hh2 : (4 : ℝ) ^ ℓ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hℓn
  obtain ⟨σ, hσ, hc⟩ := es4_hyp_d hp hN hh1 hh2
  rw [avoidLevel_pow ℓ hℓ1] at hc
  set b : ℝ≥0 := ((4 : ℝ) ^ ℓ).toNNReal with hb
  set a : ℝ≥0 := ((4 : ℝ) ^ (ℓ - 1)).toNNReal with ha
  have hbR : (b : ℝ) = 4 ^ ℓ := Real.coe_toNNReal _ (by positivity)
  have haR : (a : ℝ) = 4 ^ (ℓ - 1) := Real.coe_toNNReal _ (by positivity)
  have hab : a ≤ b := by
    rw [← NNReal.coe_le_coe, hbR, haR]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  set ε : ℝ := ((4 : ℝ) ^ ℓ) ^ indThetaH with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨Q, hQ, hlaw, hB, hae, hfail⟩ :=
    Bridge.exists_standardBrownianMotion_of_admitsBMCoupling hc
  -- the cylinder set on path space
  set S : Set (Set.Icc (0 : ℝ≥0) b → Fin d → ℤ) :=
    {w | ∃ q : qSet a b, ‖w ⟨(q : ℝ≥0), bot_le, (mem_qSet_Icc hab q.2).2⟩‖ < L} with hS
  have hSm : MeasurableSet S := by
    have : S = ⋃ q : qSet a b, {w : Set.Icc (0 : ℝ≥0) b → Fin d → ℤ |
        ‖w ⟨(q : ℝ≥0), bot_le, (mem_qSet_Icc hab q.2).2⟩‖ < L} := by
      ext w; simp [hS]
    rw [this]
    have : Countable (qSet a b) := (qSet_countable a b).to_subtype
    have hm : MeasurableSet {v : Fin d → ℤ | ‖v‖ < L} := (Set.to_countable _).measurableSet
    exact MeasurableSet.iUnion fun q =>
      (measurable_pi_apply (X := fun _ : Set.Icc (0 : ℝ≥0) b => Fin d → ℤ) (⟨(q : ℝ≥0), bot_le, (mem_qSet_Icc hab q.2).2⟩ :
        Set.Icc (0 : ℝ≥0) b)) hm
  set Φ : Ω → Set.Icc (0 : ℝ≥0) b → Fin d → ℤ := fun ω t => avoidWalk N ω ((t : ℝ≥0) : ℝ)
    with hΦ
  have hΦm : AEMeasurable Φ Pr := by
    have : Φ = (fun (x : ℝ≥0 → Fin d → ℤ) (t : Set.Icc (0 : ℝ≥0) b) => x t) ∘ avoidPath N := rfl
    rw [this]
    exact (Measurable.of_eval fun t => measurable_pi_apply _).comp_aemeasurable
      (aemeasurable_avoidPath hN)
  have hev : {ω | ∃ q ∈ qSet a b, ‖avoidWalk N ω (q : ℝ)‖ < L} = Φ ⁻¹' S := by
    ext ω
    constructor
    · rintro ⟨q, hq, h⟩
      exact ⟨⟨q, hq⟩, h⟩
    · rintro ⟨⟨q, hq⟩, h⟩
      exact ⟨q, hq, h⟩
  rw [hev]
  have hf : Measurable (fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have h1 : Pr (Φ ⁻¹' S) = Q ((fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' S) := by
    calc Pr (Φ ⁻¹' S) = (Pr.map Φ) S := (Measure.map_apply_of_aemeasurable hΦm hSm).symm
      _ = (Q.map (fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1)) S :=
        (congrArg (fun m => m S) hlaw).symm
      _ = _ := Measure.map_apply hf hSm
  rw [h1]
  -- the Brownian side
  set Bz := Bridge.zeroMod (Prod.snd : WalkPath d b × C(ℝ≥0, Fin d → ℝ) → _) with hBz
  set G : Set (WalkPath d b × C(ℝ≥0, Fin d → ℝ)) := {p | ENNReal.ofReal ε ≤
    ⨆ t : Set.Icc (0 : ℝ≥0) b,
      ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖} with hG
  set K : Set (WalkPath d b × C(ℝ≥0, Fin d → ℝ)) :=
    {p | ⨅ (t : ℝ≥0) (_ : ((2 : ℝ) ^ (ℓ - 1)) ^ 2 ≤ (t : ℝ)),
      ((‖(0 : Fin d → ℝ) + σ • Bz t p‖ : ℝ) : EReal) ≤ ((L + ε : ℝ) : EReal)} with hK
  have hsub : (fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' S ⊆ G ∪ K := by
    intro p hp'
    by_cases hg : p ∈ G
    · exact Or.inl hg
    right
    obtain ⟨⟨q, hq⟩, hqL⟩ := hp'
    have hqab := mem_qSet_Icc hab hq
    have hgt : ∀ t : Set.Icc (0 : ℝ≥0) b,
        ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖ < ε := by
      intro t
      have h2 : ⨆ t : Set.Icc (0 : ℝ≥0) b, ENNReal.ofReal
          ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖ < ENNReal.ofReal ε :=
        not_le.1 hg
      have := lt_of_le_of_lt (le_iSup _ t) h2
      exact (ENNReal.ofReal_lt_ofReal_iff hε0).1 this
    have hn := hgt ⟨q, bot_le, hqab.2⟩
    have hqq : ‖σ • Bz q p‖ < L + ε := by
      have : ‖σ • Bz q p‖ ≤ ‖(fun i => ((p.1.1 ⟨q, bot_le, hqab.2⟩ i : ℤ) : ℝ))‖ +
          ‖(fun i => ((p.1.1 ⟨q, bot_le, hqab.2⟩ i : ℤ) : ℝ)) - σ • Bz q p‖ := by
        calc _ = ‖(fun i => ((p.1.1 ⟨q, bot_le, hqab.2⟩ i : ℤ) : ℝ)) -
              ((fun i => ((p.1.1 ⟨q, bot_le, hqab.2⟩ i : ℤ) : ℝ)) - σ • Bz q p)‖ := by
              rw [sub_sub_cancel]
          _ ≤ _ := norm_sub_le _ _
      rw [avoid_norm_intCast_pi] at this
      linarith
    have hqge : ((2 : ℝ) ^ (ℓ - 1)) ^ 2 ≤ (q : ℝ) := by
      have : (a : ℝ) ≤ q := by exact_mod_cast hqab.1
      rw [haR] at this
      calc ((2 : ℝ) ^ (ℓ - 1)) ^ 2 = 4 ^ (ℓ - 1) := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ q := this
    have hmem : (⨅ (t : ℝ≥0) (_ : ((2 : ℝ) ^ (ℓ - 1)) ^ 2 ≤ (t : ℝ)),
        ((‖(0 : Fin d → ℝ) + σ • Bz t p‖ : ℝ) : EReal)) ≤ ((L + ε : ℝ) : EReal) :=
      le_trans (iInf₂_le q hqge) (by rw [zero_add]; exact_mod_cast hqq.le)
    exact hmem
  have hKb : Q K ≤ ENNReal.ofReal (ElboimSly.Brownian.Cfar d *
      ((L + ε) / 2 ^ (ℓ - 1)) ^ (d - 2)) := by
    have hr : 0 < L + ε := by linarith
    have hs : (0 : ℝ) < 2 ^ (ℓ - 1) := by positivity
    have hσ0 : 0 < σ := by linarith [hσ.1]
    have := hQ
    have hfh := ElboimSly.Brownian.far_hit_le (P := Q) (B := Bz) hB hd3 (0 : Fin d → ℝ) hr hs hσ0
    refine hfh.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    all_goals first | exact (ElboimSly.Brownian.Cfar_pos d).le | nlinarith [hσ.1, hs]
  calc Q ((fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' S) ≤ Q (G ∪ K) :=
        measure_mono hsub
    _ ≤ Q G + Q K := measure_union_le _ _
    _ ≤ _ := add_le_add hfail hKb

end

end ElboimSly.Paper

end
