/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Wald
public import ElboimSly.Foundations.StrongApprox.ExitTail
public import ElboimSly.Foundations.StrongApprox.ExpMoment
public import Mathlib

/-!
# Mean and exponential moment of the exit time

Exit times of Brownian motion from symmetric intervals (a), (c), (d) (Part II).

For a standard real Brownian motion `β` and `r > 0`, the exit time `τ` from `(-r, r)` satisfies
`τ < ∞` a.s., `E τ = r²` and `E exp(τ / (36 r²)) ≤ 6`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

lemma abs_apply_le_of_le_exitTime {w : ℝ≥0 → ℝ} (hw : IsC0 w) {ρ : ℝ} (hρ : 0 ≤ ρ) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) ≤ exitTime ρ w) : |w s| ≤ ρ := by
  rcases hs.lt_or_eq with h | h
  · exact (lt_of_lt_exitTime h).le
  · have hlt : exitTime ρ w < ⊤ := by rw [← h]; exact ENNReal.coe_lt_top
    have := abs_endVal_exitTime hw hρ hlt
    rw [endVal, ite_eq_right hlt.ne, ← h, ENNReal.toNNReal_coe] at this
    exact this.le

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

/-- Exit times of Brownian motion from symmetric intervals (c): `E τ = r²`. -/
theorem lintegral_bmExit [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {r : ℝ}
    (hr : 0 < r) : ∫⁻ ω, bmExit r β ω ∂P = ENNReal.ofReal (r ^ 2) := by
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have hτm : Measurable (bmExit r β) := measurable_bmExit hβ r
  have hfin : ∀ᵐ ω ∂P, bmExit r β ω < ⊤ := bmExit_lt_top_ae hβ hr
  set τ : Ω → ℝ≥0∞ := bmExit r β with hτ
  set ρ : ℕ → Ω → ℝ≥0∞ := fun K ω => τ ω ⊓ (K : ℝ≥0∞) with hρ
  have hρm : ∀ K, Measurable (ρ K) := fun K => hτm.inf measurable_const
  have hρstop : ∀ (K : ℕ) (t : ℝ≥0), MeasurableSet[realFiltration β t] {ω | ρ K ω ≤ t} := by
    intro K t
    by_cases hKt : (K : ℝ≥0∞) ≤ t
    · have : {ω | ρ K ω ≤ t} = Set.univ := by
        ext ω; simp only [hρ, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact inf_le_right.trans hKt
      rw [this]; exact @MeasurableSet.univ _ (realFiltration β t)
    · have : {ω | ρ K ω ≤ t} = {ω | τ ω ≤ t} := by
        ext ω
        simp only [hρ, Set.mem_ofPred_eq]
        constructor
        · intro h
          rcases le_total (τ ω) (K : ℝ≥0∞) with h1 | h1
          · exact (inf_of_le_left h1 ▸ h : τ ω ≤ t)
          · exact absurd (inf_of_le_right h1 ▸ h) hKt
        · intro h; exact inf_le_left.trans h
      rw [this]; exact bmExit_stopping hβ r t
  have hρle : ∀ (K : ℕ) ω, ρ K ω ≤ ((K : ℝ≥0) : ℝ≥0∞) := fun K ω => by
    simp [hρ]
  have hρτ : ∀ K ω, ρ K ω ≤ τ ω := fun K ω => inf_le_left
  have hρlt : ∀ K ω, ρ K ω ≠ ⊤ := fun K ω =>
    ne_top_of_le_ne_top (by simp) (hρle K ω)
  -- the pointwise bound `|β(ρ)| ≤ r`
  have hbound : ∀ K ω, (β (ρ K ω).toNNReal ω) ^ 2 ≤ r ^ 2 := by
    intro K ω
    have h1 : |β (ρ K ω).toNNReal ω| ≤ r := by
      refine abs_apply_le_of_le_exitTime (w := fun t => β t ω) (hproc.1 ω) hr.le ?_
      rw [ENNReal.coe_toNNReal (hρlt K ω)]
      exact hρτ K ω
    exact sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  -- Wald: `E β(ρ)² = E ρ`
  have hwald : ∀ K : ℕ, ∫⁻ ω, ENNReal.ofReal ((β (ρ K ω).toNNReal ω) ^ 2) ∂P =
      ∫⁻ ω, ρ K ω ∂P := by
    intro K
    have h := wald_stopped hβ (hρstop K) (K := (K : ℝ≥0)) (hρle K)
    have hsum : ∫⁻ ω, ENNReal.ofReal ((K : ℝ) - (ρ K ω).toReal) ∂P + ∫⁻ ω, ρ K ω ∂P =
        ENNReal.ofReal K := by
      rw [← lintegral_add_left]
      · have : ∀ ω, ENNReal.ofReal ((K : ℝ) - (ρ K ω).toReal) + ρ K ω = ENNReal.ofReal K := by
          intro ω
          have hle : (ρ K ω).toReal ≤ K := by
            have := ENNReal.toReal_mono (by simp) (hρle K ω)
            simpa using this
          calc ENNReal.ofReal ((K : ℝ) - (ρ K ω).toReal) + ρ K ω
              = ENNReal.ofReal ((K : ℝ) - (ρ K ω).toReal) + ENNReal.ofReal (ρ K ω).toReal := by
                rw [ENNReal.ofReal_toReal (hρlt K ω)]
            _ = ENNReal.ofReal (((K : ℝ) - (ρ K ω).toReal) + (ρ K ω).toReal) :=
                (ENNReal.ofReal_add (by linarith) ENNReal.toReal_nonneg).symm
            _ = ENNReal.ofReal K := by congr 1; ring
        simp_rw [this]
        simp
      · exact ENNReal.measurable_ofReal.comp (measurable_const.sub
          (ENNReal.measurable_toReal.comp (hρm K)))
    have hB : ∫⁻ ω, ENNReal.ofReal ((K : ℝ) - (ρ K ω).toReal) ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal K) ENNReal.ofReal_ne_top ?_
      calc _ ≤ ∫⁻ _ω, ENNReal.ofReal K ∂P := by
            refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
            have := ENNReal.toReal_nonneg (a := ρ K ω)
            linarith
        _ = ENNReal.ofReal K := by simp
    have hsum' : ∫⁻ ω, ρ K ω ∂P + ∫⁻ ω, ENNReal.ofReal ((K : ℝ) - (ρ K ω).toReal) ∂P =
        ENNReal.ofReal K := by rw [add_comm]; exact hsum
    exact (ENNReal.add_left_inj hB).1 (h.trans hsum'.symm)
  have hA_le : ∀ K : ℕ, ∫⁻ ω, ρ K ω ∂P ≤ ENNReal.ofReal (r ^ 2) := fun K => by
    rw [← hwald K]
    calc _ ≤ ∫⁻ _ω, ENNReal.ofReal (r ^ 2) ∂P :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hbound K ω)
      _ = _ := by simp
  have hsup : ∀ ω, τ ω = ⨆ K : ℕ, ρ K ω := by
    intro ω
    simp only [hρ]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]
    simp
  have hmono : Monotone ρ := fun K K' h ω => inf_le_inf_left _ (Nat.cast_le.2 h)
  have hint_sup : ∫⁻ ω, τ ω ∂P = ⨆ K : ℕ, ∫⁻ ω, ρ K ω ∂P := by
    rw [show τ = fun ω => ⨆ K : ℕ, ρ K ω from funext hsup]
    exact lintegral_iSup hρm hmono
  refine le_antisymm (hint_sup ▸ iSup_le hA_le) ?_
  -- lower bound by dominated convergence
  have hfm : ∀ K : ℕ, Measurable fun ω => ENNReal.ofReal ((β (ρ K ω).toNNReal ω) ^ 2) := fun K =>
    ENNReal.measurable_ofReal.comp
      ((hproc.measurable_uncurry.comp ((hρm K).ennreal_toNNReal.prodMk measurable_id)).pow_const 2)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun K : ℕ => ENNReal.ofReal ((β (ρ K ω).toNNReal ω) ^ 2))
      atTop (nhds (ENNReal.ofReal (r ^ 2))) := by
    filter_upwards [hfin] with ω hω
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨⌈(τ ω).toReal⌉₊, fun K hK => ?_⟩)
    have hle : τ ω ≤ (K : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_toReal hω.ne]
      calc ENNReal.ofReal (τ ω).toReal ≤ ENNReal.ofReal K :=
            ENNReal.ofReal_le_ofReal ((Nat.le_ceil _).trans (by exact_mod_cast hK))
        _ = K := ENNReal.ofReal_natCast K
    have hρeq : ρ K ω = τ ω := inf_of_le_left hle
    have habs := abs_endVal_exitTime (w := fun t => β t ω) (hproc.1 ω) hr.le (ρ := r) hω
    have hne : exitTime r (fun t => β t ω) ≠ ⊤ := hω.ne
    rw [endVal, ite_eq_right hne] at habs
    have hsq : (β (τ ω).toNNReal ω) ^ 2 = r ^ 2 := by
      calc (β (τ ω).toNNReal ω) ^ 2 = |β (τ ω).toNNReal ω| ^ 2 := (sq_abs _).symm
        _ = r ^ 2 := congrArg (· ^ 2) habs
    show ENNReal.ofReal (r ^ 2) = ENNReal.ofReal ((β (ρ K ω).toNNReal ω) ^ 2)
    rw [hρeq, hsq]
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := P)
    (fun _ => ENNReal.ofReal (r ^ 2)) hfm
    (fun K => Filter.Eventually.of_forall fun ω => ENNReal.ofReal_le_ofReal (hbound K ω))
    (by simp) hlim
  have hle : ∫⁻ _ω, ENNReal.ofReal (r ^ 2) ∂P ≤ ∫⁻ ω, τ ω ∂P := by
    refine le_of_tendsto' hdct fun K => ?_
    rw [hwald K]
    exact lintegral_mono fun ω => hρτ K ω
  simpa using hle

/-- Exit times of Brownian motion from symmetric intervals (d): `E exp(τ/(36 r²)) ≤ 6`. -/
theorem lintegral_exp_bmExit_le [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {r : ℝ}
    (hr : 0 < r) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((bmExit r β ω).toReal / (36 * r ^ 2))) ∂P ≤ 6 := by
  have hh : (0 : ℝ≥0) < (16 * r ^ 2).toNNReal := by
    rw [Real.toNNReal_pos]; positivity
  have hhR : (((16 * r ^ 2).toNNReal : ℝ≥0) : ℝ) = 16 * r ^ 2 :=
    Real.coe_toNNReal _ (by positivity)
  have := lintegral_exp_le_of_tail (measurable_bmExit hβ r) (bmExit_lt_top_ae hβ hr) hh
    (fun k => tail_pow hβ hr k)
  rw [hhR] at this
  convert this using 5
  ring

end ElboimSly.StrongApprox
