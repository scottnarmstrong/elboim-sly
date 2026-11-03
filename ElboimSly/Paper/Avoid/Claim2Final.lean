/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim2
public import ElboimSly.Paper.Avoid.ProcessLaw
public import Mathlib

/-!
# ES22 §4: Claim 4.2, final form

ES22 Claim 4.2. The complementary (survival) form, for `W` and for every process with
right-continuous paths and the law of `W` (here: `Pr'.map X = Pr.map (avoidPath N)`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

section

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk is an a.e.-measurable random path (its path map agrees a.s. with a
measurable function of the environment). -/
theorem aemeasurable_avoidPath {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (CycS ℕ d β)} (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) :
    AEMeasurable (avoidPath N) Pr := by
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  have hm : Measurable fun ω => regRecProc ((regPlan d β).envFinalOr CycRec.empty (N ω)) :=
    measurable_regRecProc.comp (((regPlan d β).measurable_envFinalOr CycRec.empty).comp
      hN.measurable)
  refine hm.aemeasurable.congr ?_
  filter_upwards [regen_env_ae hN] with ω h
  funext t
  show _ = regenWalk (avoidEnv N ω) _
  rw [avoidEnv_eq_cycSlice]
  exact (congrFun h t).symm

/-- A set of small measure has a complement of large measure. -/
theorem ofReal_one_sub_le_compl {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (h1 : μ univ = 1) {B : Set Ω} {c : ℝ} (hc : 0 ≤ c) (hB : μ B ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (1 - c) ≤ μ Bᶜ := by
  rw [ENNReal.ofReal_sub _ hc, ENNReal.ofReal_one, tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = μ univ := h1.symm
    _ = μ (B ∪ Bᶜ) := by rw [union_compl_self]
    _ ≤ μ B + μ Bᶜ := measure_union_le _ _
    _ ≤ μ Bᶜ + ENNReal.ofReal c := by rw [add_comm]; gcongr

/-- **ES22 Claim 4.2** (ES22 Claim 4.2, with the range `4^{n₀+1} ≤ L ≤ 4ⁿ`, deviation F03; the
exponent is `1/30`). There is `C` depending only on `d` such that under (S1)–(S2), for every real
`L ∈ [4^{n₀+1}, 4ⁿ]` and every `A ⊆ {‖u‖ ≥ L}` with `|A ∩ [-r, r]^d| ≤ r^{8/3}` for all `r ≥ L`:
(i) `P(∀ s ≤ 4ⁿ, W(s) ∉ A) ≥ 1 - C L^{-1/30}`; (ii) the same holds for every process `X` with
right-continuous paths and the law of `W` on `(ℝ≥0 → ℤ^d)`. -/
theorem es4_claim2 (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params d β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ d β)), IsPoissonPointProcess N (cycIntensity ℕ d β) Pr →
        ∀ {L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ L → L ≤ (4 : ℝ) ^ n →
        ∀ {A : Set (Fin d → ℤ)}, (∀ u ∈ A, L ≤ ‖u‖) →
        (∀ r : ℝ, L ≤ r → ((A ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)) →
        ENNReal.ofReal (1 - C * L ^ (-(1 : ℝ) / 30)) ≤
          Pr {ω | ∀ s : ℝ, 0 ≤ s → s ≤ (4 : ℝ) ^ n → avoidWalk N ω s ∉ A} ∧
        ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Pr' : Measure Ω') (X : Ω' → ℝ≥0 → Fin d → ℤ),
          AEMeasurable X Pr' → (∀ ω, IsRCPath (X ω)) → Pr'.map X = Pr.map (avoidPath N) →
          ENNReal.ofReal (1 - C * L ^ (-(1 : ℝ) / 30)) ≤
            Pr' {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ (4 : ℝ) ^ n → X ω s ∉ A} := by
  obtain ⟨C, hC, H⟩ := es4_claim2_bad hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN L hL1 hL2 A hA1 hA2
  have := hN.isProbabilityMeasure
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL1
  have hc : 0 ≤ C * L ^ (-(1 : ℝ) / 30) := by positivity
  have hbad := H β n₀ n t₀ hp Pr N hN hL1 hL2 hA1 hA2
  refine ⟨?_, ?_⟩
  · have := ofReal_one_sub_le_compl (μ := Pr) (measure_univ) hc hbad
    refine this.trans (measure_mono ?_)
    intro ω hω s hs0 hs1 hsA
    exact hω ⟨s, hs0, hs1, hsA⟩
  · intro Ω' _ Pr' X hX hrc hlaw
    have hu : Pr' univ = 1 := by
      have := Measure.map_apply_of_aemeasurable hX MeasurableSet.univ
      rw [hlaw, Measure.map_apply_of_aemeasurable (aemeasurable_avoidPath hN)
        MeasurableSet.univ] at this
      simpa using this.symm
    set b : ℝ≥0 := 4 ^ n with hb
    have hbR : (b : ℝ) = 4 ^ n := by simp [hb]
    have hq : Pr' {ω | ∃ s : ℝ≥0, 0 ≤ s ∧ s ≤ b ∧ X ω s ∈ A} ≤
        ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 30)) := by
      have e : {ω | ∃ s : ℝ≥0, 0 ≤ s ∧ s ≤ b ∧ X ω s ∈ A} =
          {ω | ∃ q ∈ qSet 0 b, X ω q ∈ A} := by
        ext ω
        exact exists_Icc_iff_qSet (hrc ω) (bot_le : (0 : ℝ≥0) ≤ b) (fun v => v ∈ A)
      rw [e, prob_cyl_eq hX (aemeasurable_avoidPath hN) hlaw 0 b (fun v => v ∈ A)]
      refine le_trans (measure_mono ?_) hbad
      rintro ω ⟨q, hq, hqA⟩
      have := mem_qSet_Icc (bot_le : (0 : ℝ≥0) ≤ b) hq
      exact ⟨(q : ℝ), q.2, by rw [← hbR]; exact_mod_cast this.2, hqA⟩
    have := ofReal_one_sub_le_compl (μ := Pr') hu hc hq
    refine this.trans (measure_mono ?_)
    intro ω hω s hs hsA
    exact hω ⟨s, bot_le, by rw [← NNReal.coe_le_coe, hbR]; exact hs, hsA⟩

end

end ElboimSly.Paper

end
