/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.OneInterface
public import Mathlib

/-!
# A canonical `Es4Setting` for a Poisson environment

Standing assumptions (Step 0 of ES22 Lemma 6.2: the probability of an event that is a
measurable function of the environment does not depend on the probability space).

For a Poisson point process `N` on any probability space `(Ω, Pe)`, the product space `Ω × Ω` with
`P := Pe ⊗ Pe`, environments `N ∘ fst` and `N ∘ snd`, and the trivial `σ`-algebra `𝒢₀ = ⊥` is an
`Es4Space` (`es4Space_canon`).  Events depending on `N` only have the same probability there
(`prod_fst_preimage`).  This turns the `Es4Setting` statements `*_of_interface` into statements for
an arbitrary Poisson environment, with the standing parameters `Es4Params`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω] {Pe : Measure Ω}
  {N : Ω → Measure (CycS ℕ d β)}

theorem es4Space_canon (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pe) :
    Es4Space d β (⊥ : MeasurableSpace (Ω × Ω)) (Pe.prod Pe) (fun p => N p.1)
      (fun p => N p.2) := by
  have := hN.isProbabilityMeasure
  have h1 : IsPoissonPointProcess (fun p : Ω × Ω => N p.1) (cycIntensity ℕ d β) (Pe.prod Pe) := by
    refine hN.of_map_eq (hN.measurable.comp measurable_fst) ?_
    change (Pe.prod Pe).map (N ∘ Prod.fst) = Pe.map N
    rw [← Measure.map_map hN.measurable measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul]
  have h2 : IsPoissonPointProcess (fun p : Ω × Ω => N p.2) (cycIntensity ℕ d β) (Pe.prod Pe) := by
    refine hN.of_map_eq (hN.measurable.comp measurable_snd) ?_
    change (Pe.prod Pe).map (N ∘ Prod.snd) = Pe.map N
    rw [← Measure.map_map hN.measurable measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul]
  refine ⟨h1, h2, bot_le, indep_bot_left _, ?_⟩
  rw [bot_sup_eq]
  have := indepFun_prod (μ := Pe) (ν := Pe) hN.measurable hN.measurable
  exact this.symm

theorem prod_fst_preimage [IsProbabilityMeasure Pe] (A : Set Ω) :
    (Pe.prod Pe) {p : Ω × Ω | p.1 ∈ A} = Pe A := by
  have : {p : Ω × Ω | p.1 ∈ A} = A ×ˢ univ := by ext; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]

/-- The canonical `Es4Setting` of a Poisson environment with standing parameters `Es4Params`. -/
theorem es4Setting_canon (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pe) {n₀ n : ℕ}
    {t₀ : ℝ} (hp : Es4Params d β n₀ n t₀) :
    Es4Setting d β n₀ n t₀ (⊥ : MeasurableSpace (Ω × Ω)) (Pe.prod Pe) (fun p => N p.1)
      (fun p => N p.2) :=
  ⟨hp, es4Space_canon hN⟩

/-- mathbbP(𝒢(i))ge1-e^-cn^3, for an arbitrary Poisson environment, up to the interface. -/
theorem es6_tauhat_of_params {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pe) (hp : Es4Params d β n₀ n t₀)
    (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β) (k : ℕ) :
    Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3))) := by
  have := hN.isProbabilityMeasure
  rw [← prod_fst_preimage]
  exact es6_tauhat_of_interface hI _ (es4Setting_canon hN hp) hT hβ5 k

/-- ES22 Theorem 6.1 for an arbitrary Poisson environment, up to the
interface interface with S6: with probability at least `1 - e^{-c₆ n³}`, for every
`t ∈ [0, t_n - t_n^ε]`, `|𝒯 ∩ [t, t + t_n^ε]| ≥ (0.9 + 2/n) t_n^ε`. -/
theorem es6_one_of_params {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pe) (hp : Es4Params d β n₀ n t₀)
    (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β) :
    Pe {ω | ¬ ∀ t : ℝ, 0 ≤ t → t + indScale t₀ n ^ heavyEps d ≤ indScale t₀ n →
        ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * indScale t₀ n ^ heavyEps d) ≤
          volume ({s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s} ∩
            Icc t (t + indScale t₀ n ^ heavyEps d))} ≤
      ENNReal.ofReal (Real.exp (-(heavyC6 d E * (n : ℝ) ^ 3))) := by
  have := hN.isProbabilityMeasure
  rw [← prod_fst_preimage]
  exact es6_one_of_interface hI _ (es4Setting_canon hN hp) hT hβ5

end ElboimSly.Paper.Heavy
