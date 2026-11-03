/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
import Mathlib

/-!
# Series of independent Gaussians

Series of independent Gaussians.

If `(ξ_α)` are independent `N(0,1)` variables, `c : A → ℝ`, `F_N` finite sets, and the partial sums
`∑_{α ∈ F_N} c_α ξ_α` converge almost surely to `Y`, while `∑_{α ∈ F_N} c_α²` converges to `s`,
then `Y ~ N(0, s)`. The proof computes the characteristic functions of the partial sums (finite
sums of independent Gaussians are Gaussian), and passes to the limit by dominated convergence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal Topology

namespace ElboimSly.Brownian

variable {Ω A : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : A → Ω → ℝ}

/-- The square of a real number as an element of `ℝ≥0`. -/
abbrev nnsq (x : ℝ) : ℝ≥0 := ⟨x ^ 2, sq_nonneg x⟩

/-- A finite linear combination of independent standard Gaussians is Gaussian. -/
lemma hasLaw_finset_sum (hind : iIndepFun ξ P) (hlaw : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P)
    (c : A → ℝ) (s : Finset A) [DecidableEq A] :
    HasLaw (fun ω => ∑ α ∈ s, c α * ξ α ω)
      (gaussianReal 0 (∑ α ∈ s, nnsq (c α))) P := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by fun_prop, ?_⟩
    simp [Measure.map_const, gaussianReal_zero_var]
  | insert a s ha ih =>
    have hg : iIndepFun (fun α ω => c α * ξ α ω) P :=
      hind.comp (fun α x => c α * x) fun α => measurable_const.mul measurable_id
    have hgm : ∀ α, AEMeasurable (fun ω => c α * ξ α ω) P := fun α =>
      (hlaw α).aemeasurable.const_mul _
    have hI : IndepFun (fun ω => ∑ α ∈ s, c α * ξ α ω) (fun ω => c a * ξ a ω) P := by
      have := hg.indepFun_finsetSum_of_notMem₀ hgm ha
      convert this using 1
      funext ω
      simp [Finset.sum_apply]
    have h1 := gaussianReal_const_mul (hlaw a) (c a)
    have h2 := gaussianReal_add_gaussianReal_of_indepFun hI.symm h1 ih
    refine ⟨by fun_prop, ?_⟩
    have e : (fun ω => ∑ α ∈ insert a s, c α * ξ α ω) =
        (fun ω => c a * ξ a ω) + fun ω => ∑ α ∈ s, c α * ξ α ω := by
      funext ω; simp [Finset.sum_insert ha]
    rw [e, h2, Finset.sum_insert ha]
    congr 1
    · simp
    · rw [mul_one]; rfl

/-- Series of independent Gaussians. An almost sure limit of finite Gaussian combinations
`∑_{α ∈ F_N} c_α ξ_α` of independent standard Gaussians, with `∑_{F_N} c_α² → s`, has law
`N(0, s)`. -/
theorem hasLaw_of_tendsto_sums (hind : iIndepFun ξ P)
    (hlaw : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P) (c : A → ℝ) (F : ℕ → Finset A)
    {Y : Ω → ℝ} {s : ℝ≥0} (hY : AEMeasurable Y P)
    (hvar : Tendsto (fun N => ∑ α ∈ F N, c α ^ 2) atTop (𝓝 (s : ℝ)))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun N => ∑ α ∈ F N, c α * ξ α ω) atTop (𝓝 (Y ω))) :
    HasLaw Y (gaussianReal 0 s) P := by
  classical
  refine ⟨hY, Measure.ext_of_charFun ?_⟩
  funext u
  have hcont : Continuous fun x : ℝ => cexp (u * x * I) := by fun_prop
  have hn : ∀ x : ℝ, ‖cexp ((u : ℂ) * x * I)‖ = 1 := fun x => by
    rw [← Complex.ofReal_mul]; exact Complex.norm_exp_ofReal_mul_I _
  have hYN : ∀ N, HasLaw (fun ω => ∑ α ∈ F N, c α * ξ α ω)
      (gaussianReal 0 (∑ α ∈ F N, nnsq (c α))) P :=
    fun N => hasLaw_finset_sum hind hlaw c (F N)
  have h2 : ∀ N, ∫ ω, cexp (u * (∑ α ∈ F N, c α * ξ α ω) * I) ∂P =
      cexp (u * (0 : ℝ) * I - ((∑ α ∈ F N, c α ^ 2 : ℝ) : ℂ) * u ^ 2 / 2) := by
    intro N
    have := charFun_gaussianReal (μ := 0)
      (v := ∑ α ∈ F N, nnsq (c α)) u
    rw [← (hYN N).map_eq, charFun_apply_real,
      integral_map (hYN N).aemeasurable hcont.aestronglyMeasurable] at this
    have hv : ((∑ α ∈ F N, nnsq (c α) : ℝ≥0) : ℝ) = ∑ α ∈ F N, c α ^ 2 := by
      rw [NNReal.coe_sum]; rfl
    rw [this, hv]
  have h1 : Tendsto (fun N => ∫ ω, cexp (u * (∑ α ∈ F N, c α * ξ α ω) * I) ∂P) atTop
      (𝓝 (∫ ω, cexp (u * Y ω * I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1)
      (fun N => (hcont.measurable.comp_aemeasurable (hYN N).aemeasurable).aestronglyMeasurable)
      (integrable_const _) (fun N => ae_of_all _ fun ω => (hn _).le) ?_
    filter_upwards [hlim] with ω hω
    exact (hcont.tendsto _).comp hω
  have h3 : Tendsto (fun N => cexp (u * (0 : ℝ) * I - ((∑ α ∈ F N, c α ^ 2 : ℝ) : ℂ) * u ^ 2 / 2))
      atTop (𝓝 (cexp (u * (0 : ℝ) * I - ((s : ℝ) : ℂ) * u ^ 2 / 2))) := by
    have : Tendsto (fun N => ((∑ α ∈ F N, c α ^ 2 : ℝ) : ℂ)) atTop (𝓝 ((s : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hvar
    exact ((Complex.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.sub ((this.mul_const _).div_const _)))
  have h4 := tendsto_nhds_unique h1 (h3.congr fun N => (h2 N).symm)
  rw [charFun_apply_real, integral_map hY hcont.aestronglyMeasurable, h4, charFun_gaussianReal]

end ElboimSly.Brownian
