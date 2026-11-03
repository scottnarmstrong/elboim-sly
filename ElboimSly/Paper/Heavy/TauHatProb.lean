/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauBad
public import ElboimSly.Paper.Heavy.Twelve

/-!
# Each piece is in `Γ_n` with high probability

mathbbP(𝒢(i))ge1-e^-cn^3 (ES22 §6, ES22 §6).

`P(𝒢(i)^c) ≤ A_n e^{-c_♭ n³}`.  The proof is a union bound over the four stopping times
`τ_fast, τ_jump, τ', τ_bad ≤ T ∧ t_n`, with the four inputs entering as hypotheses:

* `hfast`, `hjump`: eq. (taufast), `P(τ_fast ≤ t_n) ≤ ϖ_n`, `P(τ_jump ≤ t_n) ≤ ϖ_n`;
* `hprime`: corollary after Lemma 6.2, `P(τ' ≤ t_n ∧ t_reg) ≤ ϖ_n + (n+1) 5^{d(n+1)} (e^{-n³/17} + e^{-c₅ n³})`;
* `hbad`: eq. (tau.bad) (`es6_taubad_of`);
* `hiid`: the pieces are identically distributed (regenerated cyclic walk).

`es6_tauhat_of` is the conditional statement.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}

/-- The numerical comparison of mathbbP(𝒢(i))ge1-e^-cn^3. -/
theorem tauhat_numeric {E : HeavyEscConsts} (hd : 1 ≤ d) (n : ℕ) :
    4 * (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2))) +
      (n + 1) * 5 ^ (d * (n + 1)) * (Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3))) +
      max (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))))
        (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2))) ≤
    heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3)) := by
  have hδ := heavy_indDelta_pos hd
  have hc := heavyc_pos (d := d) (E := E) hd
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  set c := heavyc d E with hcdef
  have hc1 : c ≤ 1 / 17 := heavyc_le
  have hc2 : c ≤ E.c5 := (min_le_left _ _).trans (min_le_left _ _)
  have hc3 : c ≤ indDelta d ^ 3 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc4 : c ≤ indDelta d ^ 2 / (2 * 33 ^ d) := (min_le_right _ _).trans (min_le_right _ _)
  have e1 : Real.exp (-((n : ℝ) ^ 3 / 2)) ≤ Real.exp (-(c * (n : ℝ) ^ 3)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-((n : ℝ) ^ 3 / 17)) ≤ Real.exp (-(c * (n : ℝ) ^ 3)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-(E.c5 * (n : ℝ) ^ 3)) ≤ Real.exp (-(c * (n : ℝ) ^ 3)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e4 : Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2)) ≤ Real.exp (-(c * (n : ℝ) ^ 3)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e5 : Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))) ≤
      Real.exp (-(c * (n : ℝ) ^ 3)) := by
    apply Real.exp_le_exp.2
    have h33 : (0 : ℝ) < 2 * 33 ^ d := by positivity
    have : c * (n : ℝ) ^ 3 ≤ indDelta d ^ 2 / (2 * 33 ^ d) * (n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hc4 hn3
    have e : indDelta d ^ 2 / (2 * 33 ^ d) * (n : ℝ) ^ 3 =
        indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d) := by ring
    linarith
  have hmax := max_le e5 e4
  have hCJ := heavyCJ_pos (d := d)
  unfold heavyA
  set X := Real.exp (-(c * (n : ℝ) ^ 3)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have h16 : 0 ≤ heavyCJ d * 16 ^ (n + 1) := by positivity
  have h5 : 0 ≤ ((n : ℝ) + 1) * 5 ^ (d * (n + 1)) := by positivity
  calc _ ≤ 4 * (heavyCJ d * 16 ^ (n + 1) * X) + ((n : ℝ) + 1) * 5 ^ (d * (n + 1)) * (X + X) + X := by
        gcongr
    _ = _ := by ring

/-- mathbbP(𝒢(i))ge1-e^-cn^3, conditional on the four stopping-time bounds and on the pieces
being identically distributed (`hiid`). -/
theorem es6_tauhat_of {E : HeavyEscConsts} {n : ℕ} {t₀ : ℝ} (hd : 5 ≤ d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hfast : Pe {ω | pathTfastCube (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) n ≤
      min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2))))
    (hjump : Pe {ω | pathTjumpCube (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) n ≤
      min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2))))
    (hprime : Pe {ω | heavyTauPrime d t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        (n + 1) * 5 ^ (d * (n + 1)) *
          (Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3)))))
    (hbad : Pe {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        max (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))))
          (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2)))))
    (hiid : ∀ k : ℕ, Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} =
      Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) 0)}) (k : ℕ) :
    Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3))) := by
  rw [hiid k]
  have hCJ := heavyCJ_pos (d := d)
  set ϖ : ℝ := heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) with hϖ
  have hϖ0 : 0 ≤ ϖ := by positivity
  have hgood := ae_cycGood hN
  have hsub : {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) 0)} ≤ᵐ[Pe]
      (({ω | pathTfastCube (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) n ≤
          min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ∪
        {ω | pathTjumpCube (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) n ≤
          min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))}) ∪
      {ω | heavyTauPrime d t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))}) ∪
      {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} := by
    filter_upwards [hgood] with ω hω hmem
    have hcyc : IsCyclicPath (heavyPiece (geoSlices N ω) 0) :=
      isCyclicPath_cycWalk (hω 0)
    have hcl : cycClosingTime β (heavyPiece (geoSlices N ω) 0) = cycTreg (cycSlice 0 (N ω)) :=
      cycClosingTime_cycWalk _
    simp only [heavyGamma, not_and, hcyc, true_implies, not_lt] at hmem
    rw [hcl] at hmem
    simp only [min_le_iff] at hmem
    simp only [mem_union, mem_ofPred_eq]
    rcases hmem with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (h.trans (le_of_eq (min_comm _ _)))))
    · exact Or.inl (Or.inl (Or.inr (h.trans (le_of_eq (min_comm _ _)))))
    · exact Or.inl (Or.inr (h.trans (le_of_eq (min_comm _ _))))
    · exact Or.inr (h.trans (le_of_eq (min_comm _ _)))
  refine (measure_mono_ae hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add hfast hjump)) hprime)) hbad).trans ?_
  have hnum := tauhat_numeric (E := E) (n := n) (by omega : 1 ≤ d)
  rw [← ENNReal.ofReal_add hϖ0 hϖ0, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hB : 0 ≤ ((n : ℝ) + 1) * 5 ^ (d * (n + 1)) *
      (Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3))) := by positivity
  nlinarith [hnum]

end ElboimSly.Paper.Heavy
