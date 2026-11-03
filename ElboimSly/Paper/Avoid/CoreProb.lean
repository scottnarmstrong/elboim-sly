/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Core
public import Mathlib

/-!
# ES22 §4, Lemma 4.1 (core form): the probability of the good event for a fixed history

ES22 Lemma 4.1, "Two events". For a fixed relaxed history `w|[a,T]` and an
independent continuation `X̃` with the law of `W`, `P((u_w, X̃) ∈ Γ) ≥ 1 - C β^{-δ/30}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ}

/-- The recorded history of a fixed path `w` on `[a, T]`. -/
noncomputable def histOf (w : ℝ → Fin d → ℤ) (a T : ℝ) : HistE d :=
  (fun s : ℝ≥0 => w (min (a + s) T), (T - a).toNNReal, w T)

theorem histVisited_subset {w : ℝ → Fin d → ℤ} {a T : ℝ} (haT : a ≤ T) :
    histVisited (histOf w a T) ⊆ visitedSet w a T := by
  rintro v (hv | ⟨s, -, hsl, rfl⟩)
  · have : v = w T := hv
    exact ⟨T, ⟨haT, le_rfl⟩, this.symm⟩
  · have hl : (((T - a).toNNReal : ℝ≥0) : ℝ) = T - a := Real.coe_toNNReal _ (by linarith)
    have : (s : ℝ) ≤ T - a := by rw [← hl]; exact_mod_cast hsl
    refine ⟨min (a + s) T, ⟨?_, min_le_right _ _⟩, rfl⟩
    exact le_min (by linarith [s.2]) haT

/-- **The good event has probability `≥ 1 - C β^{-δ/30}`** for a relaxed fixed history. -/
theorem gamma_prob (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → Es4Params d β n₀ n t₀ →
      ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] (Pr₀ : Measure Ω₀) (N₀ : Ω₀ → Measure (CycS ℕ d β)),
        IsPoissonPointProcess N₀ (cycIntensity ℕ d β) Pr₀ →
      ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Pr' : Measure Ω') [IsProbabilityMeasure Pr']
        (X : Ω' → ℝ≥0 → Fin d → ℤ), Measurable X → Pr'.map X = Pr₀.map (avoidPath N₀) →
      ∀ (w : ℝ → Fin d → ℤ) (a T : ℝ), a ≤ T → IsRelaxedTimeWrt β w a T →
        ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) ≤
          Pr' (X ⁻¹' {y | (histOf w a T, y) ∈
            cylGamma d (β ^ indDelta d / 2) (β ^ indDelta d) (β ^ (3 * indDelta d)).toNNReal
              ((4 : ℝ) ^ n).toNNReal}) := by
  obtain ⟨C42, hC42, H42⟩ := es4_claim2_bad_process hd
  obtain ⟨C43, hC43, H43⟩ := es4_claim3_bad_process hd
  refine ⟨2 * C42 + C43, by positivity, fun n₀ => ?_⟩
  obtain ⟨β41, hβ41a, hβ41⟩ := exists_beta41 hd n₀
  refine ⟨β41, ?_⟩
  intro β _ n t₀ hβ hp Ω₀ _ Pr₀ N₀ hN₀ Ω' _ Pr' _ X hXm hlaw w a T haT hrel
  have hδ := avoid_indDelta_pos (d := d) (by omega)
  obtain ⟨hL4, hL3, hb3⟩ := hβ41 β hβ
  have hβ1 : (10 : ℝ) ^ 14 ≤ β := hβ41a.trans hβ
  have hβ1' : (1 : ℝ) ≤ β := le_trans (by norm_num) hβ1
  have hβ0 : 0 < β := by linarith
  have hn1 : 1 ≤ n := by have := hp.lt; omega
  have hβn : β < (4 : ℝ) ^ (n + 1) := by
    have h1 := hp.beta_lt
    have h2 : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1) := by
      unfold indScale; rw [pow_succ]; nlinarith [hp.le_four, pow_pos (by norm_num : (0 : ℝ) < 4) n]
    linarith
  set b1 : ℝ := β ^ indDelta d with hb1
  set b3 : ℝ := β ^ (3 * indDelta d) with hb3def
  have hb1pos : 0 < b1 := Real.rpow_pos_of_pos hβ0 _
  have hb3pos : 0 < b3 := Real.rpow_pos_of_pos hβ0 _
  have hb1b3 : b1 ≤ b3 := Real.rpow_le_rpow_of_exponent_le hβ1' (by linarith)
  have hb3n : b3 ≤ (4 : ℝ) ^ n := beta_pow_le hd hβ1' hn1 hβn
  have hb1big : (2 : ℝ) < b1 := by
    have : (4 : ℝ) ≤ 4 ^ (n₀ + 1) := by
      calc (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (n₀ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  set L1 : ℝ := b1 / 2 with hL1
  have hL1n : L1 ≤ (4 : ℝ) ^ n := by rw [hL1]; linarith
  -- the relevant sets
  set V := visitedSet w a T with hV
  set x₀ := w T with hx₀
  have hdens : ∀ r : ℝ, L1 ≤ r → ((histSet V x₀ L1 ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
    refine density_of_relaxed (w := w) (a := a) (T := T) (by simpa [hL1] using hL3) ?_
    intro ρ hρ
    refine hrel.1 ρ ?_
    rw [hL1] at hρ; linarith
  have hB1 := H42 β n₀ n t₀ hp Pr₀ N₀ hN₀ (L := L1) (by simpa [hL1] using hL4) hL1n
    (A := histSet V x₀ L1) (fun u hu => hu.1) hdens Pr' X hXm.aemeasurable hlaw
  have hb3t : (4 : ℝ) ^ (n₀ + 1) ≤ b3 := by
    have : (4 : ℝ) ^ (n₀ + 1) ≤ L1 := by simpa [hL1] using hL4
    linarith
  have hθ3 : b3 ^ indThetaH ≤ b3 ^ indThetaH := le_rfl
  have hB2 := H43 β n₀ n t₀ hp Pr₀ N₀ hN₀ (t := b3) (L := b3 ^ indThetaH) hb3t hb3n hθ3
    Pr' X hXm.aemeasurable hlaw
  have hL2 : b1 ≤ b3 ^ indThetaH := by
    have h1 : β ^ indDelta d ≤ β ^ (3 * indDelta d * indThetaH) := by
      apply Real.rpow_le_rpow_of_exponent_le hβ1'
      have : indThetaH = 41 / 100 := rfl
      rw [this]; nlinarith
    calc b1 ≤ β ^ (3 * indDelta d * indThetaH) := h1
      _ = b3 ^ indThetaH := by rw [hb3def, ← Real.rpow_mul hβ0.le]
  -- failure sets
  set Γx : Set (ℝ≥0 → Fin d → ℤ) := {y | (histOf w a T, y) ∈
    cylGamma d L1 b1 b3.toNNReal ((4 : ℝ) ^ n).toNNReal} with hΓx
  have hΓm : MeasurableSet Γx := measurable_prodMk_left (measurableSet_cylGamma L1 b1 _ _)
  have hcompl : (X ⁻¹' Γx)ᶜ ⊆ {ω | ∃ q ∈ qSet 0 ((4 : ℝ) ^ n).toNNReal,
        X ω q ∈ histSet V x₀ L1} ∪ {ω | ∃ q ∈ qSet b3.toNNReal ((4 : ℝ) ^ n).toNNReal,
        ‖X ω q‖ < b3 ^ indThetaH} := by
    intro ω hω
    simp only [mem_compl_iff, mem_preimage, hΓx, mem_ofPred_eq, cylGamma, not_and_or, not_forall,
      not_le, exists_prop] at hω
    rcases hω with ⟨q, hq, hbad⟩ | ⟨q, hq, hbad⟩
    · left
      push Not at hbad
      obtain ⟨h1, v, hv, h2⟩ := hbad
      exact ⟨q, hq, h1, v, histVisited_subset haT hv, h2⟩
    · right
      exact ⟨q, hq, lt_of_lt_of_le hbad hL2⟩
  have hbound : Pr' (X ⁻¹' Γx)ᶜ ≤ ENNReal.ofReal ((2 * C42 + C43) * β ^ (-indDelta d / 30)) := by
    refine (measure_mono hcompl).trans ((measure_union_le _ _).trans ?_)
    have e1 : C42 * L1 ^ (-(1 : ℝ) / 30) ≤ 2 * C42 * β ^ (-indDelta d / 30) := by
      have := half_pow_le hβ1' (indDelta d) hδ
      calc C42 * L1 ^ (-(1 : ℝ) / 30) ≤ C42 * (2 * β ^ (-indDelta d / 30)) := by
            rw [hL1]; gcongr
        _ = _ := by ring
    have e2 : C43 * (b3 ^ indThetaH) ^ (d - 2) * b3 ^ (-((d - 2 : ℕ) : ℝ) / 2) ≤
        C43 * β ^ (-indDelta d / 30) := by
      have := claim3_exponent hd hβ1'
      calc C43 * (b3 ^ indThetaH) ^ (d - 2) * b3 ^ (-((d - 2 : ℕ) : ℝ) / 2)
          = C43 * ((b3 ^ indThetaH) ^ (d - 2) * b3 ^ (-((d - 2 : ℕ) : ℝ) / 2)) := by ring
        _ ≤ C43 * β ^ (-indDelta d / 30) := by gcongr
    calc _ ≤ ENNReal.ofReal (C42 * L1 ^ (-(1 : ℝ) / 30)) +
          ENNReal.ofReal (C43 * (b3 ^ indThetaH) ^ (d - 2) * b3 ^ (-((d - 2 : ℕ) : ℝ) / 2)) :=
          add_le_add hB1 hB2
      _ ≤ ENNReal.ofReal (2 * C42 * β ^ (-indDelta d / 30)) +
          ENNReal.ofReal (C43 * β ^ (-indDelta d / 30)) :=
          add_le_add (ENNReal.ofReal_le_ofReal e1) (ENNReal.ofReal_le_ofReal e2)
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  have hu : Pr' univ = 1 := measure_univ
  have hfin := ofReal_one_sub_le_compl (μ := Pr') hu (B := (X ⁻¹' Γx)ᶜ) (by positivity) hbound
  rwa [compl_compl] at hfin

end ElboimSly.Paper

end
