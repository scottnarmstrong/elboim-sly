/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMeancov
public import ElboimSly.Paper.Step.RegenMeas
public import Mathlib

/-!
# Lattice symmetry of the regenerated walk

Lattice symmetry of the regenerated walk (ES22 §7, ES22 §7).

For a lattice automorphism `g` fixing `0` (signed permutations of the coordinates), `g ∘ W` and `W`
have the same law as processes (`step_symmetry_law`). Consequently, for `F` a path functional with
`F (g ∘ w) = g (F w)`, the law of `F (W|_{[0,h]})` is `g`-invariant (`step_symmetry_functional`), and
if `‖F‖²` is integrable it is centred with covariance `θ I` (`step_symmetry_meancov`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Lattice symmetry of the regenerated walk, first assertion: `g ∘ W` and `W` have the same law as
processes on `ℝ≥0 → ℤ^d`. -/
theorem step_symmetry_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (g : Interchange.LatticeAut d) (hg : g.toEquiv 0 = 0) :
    P.map (fun ω (t : ℝ≥0) => g.toEquiv (regenWalk (fun k => copyEnv (N ω) k) (t : ℝ))) =
      P.map (fun ω (t : ℝ≥0) => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) := by
  have : Nonempty (Cyclic.CycEntry ℕ d) := ⟨(Cyclic.regPlan d β).junk⟩
  have hN' := Cyclic.isPoissonPointProcess_envMap hN g
  set G : Measure (ℕ × RingSpace d β) → ℝ≥0 → Fin d → ℤ := fun ν =>
    Cyclic.regRecProc ((Cyclic.regPlan d β).envFinalOr Cyclic.CycRec.empty ν) with hG
  have hGm : Measurable G := Cyclic.measurable_regRecProc.comp
    ((Cyclic.regPlan d β).measurable_envFinalOr Cyclic.CycRec.empty)
  have hgm : Measurable (fun p : ℝ≥0 → Fin d → ℤ => fun t => g.toEquiv (p t)) :=
    measurable_pi_iff.2 fun t => (measurable_of_countable g.toEquiv).comp (measurable_pi_apply t)
  have h1 : ∀ᵐ ω ∂P, (fun t : ℝ≥0 => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) = G (N ω) := by
    filter_upwards [Cyclic.regen_env_ae hN] with ω h
    simpa only [copyEnv_eq_cycSlice] using h
  have h2 : ∀ᵐ ω ∂P, (fun t : ℝ≥0 => regenWalk (fun k => copyEnv (Cyclic.envMap g (N ω)) k)
      (t : ℝ)) = G (Cyclic.envMap g (N ω)) := by
    filter_upwards [Cyclic.regen_env_ae hN'] with ω h
    simpa only [copyEnv_eq_cycSlice] using h
  have h3 : ∀ᵐ ω ∂P, (fun t : ℝ≥0 => regenWalk (fun k => copyEnv (Cyclic.envMap g (N ω)) k)
      (t : ℝ)) = fun t : ℝ≥0 => g.toEquiv (regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) := by
    filter_upwards [Cyclic.ae_cycGood hN] with ω hω
    funext t
    simp only [copyEnv_eq_cycSlice, Cyclic.cycSlice_envMap]
    exact Cyclic.regenWalk_latticeMeasure hω g hg t
  have e1 : P.map (fun ω (t : ℝ≥0) => g.toEquiv (regenWalk (fun k => copyEnv (N ω) k) (t : ℝ))) =
      P.map (fun ω => G (Cyclic.envMap g (N ω))) := by
    refine Measure.map_congr ?_
    filter_upwards [h2, h3] with ω a b
    rw [← b, a]
  have e2 : P.map (fun ω (t : ℝ≥0) => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) =
      P.map (fun ω => G (N ω)) := Measure.map_congr h1
  rw [e1, e2]
  have hm1 : Measurable fun ω => Cyclic.envMap g (N ω) := hN'.1
  have a1 : P.map (fun ω => G (Cyclic.envMap g (N ω))) =
      (P.map (fun ω => Cyclic.envMap g (N ω))).map G := (Measure.map_map hGm hm1).symm
  have a2 : P.map (fun ω => G (N ω)) = (P.map N).map G := (Measure.map_map hGm hN.1).symm
  rw [a1, a2, hN.map_eq_map hN']

/-- Lattice symmetry of the regenerated walk, second assertion. If `F` is a measurable functional of paths on
`[0, h]` with values in `ℤ^d` and `F (g ∘ w) = g (F w)` for every lattice automorphism `g` fixing
`0`, then the law of `F (W|_{[0,h]})` is invariant under every such `g`. -/
theorem step_symmetry_functional {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (T : ℝ≥0) (F : (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) → Fin d → ℤ) (hF : Measurable F)
    (hFg : ∀ (g : Interchange.LatticeAut d), g.toEquiv 0 = 0 →
      ∀ w, F (fun t => g.toEquiv (w t)) = g.toEquiv (F w))
    (g : Interchange.LatticeAut d) (hg : g.toEquiv 0 = 0) :
    P.map (fun ω => g.toEquiv (F (fun t : Set.Icc (0 : ℝ≥0) T =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)))) =
      P.map (fun ω => F (fun t : Set.Icc (0 : ℝ≥0) T =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ))) := by
  set Wp : Ω → ℝ≥0 → Fin d → ℤ := fun ω t => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ) with hWp
  have hWae : AEMeasurable Wp P := aemeasurable_regenWalk_path hN
  have hR : Measurable (fun p : ℝ≥0 → Fin d → ℤ => fun t : Set.Icc (0 : ℝ≥0) T => p t) :=
    measurable_pi_iff.2 fun t => measurable_pi_apply (t : ℝ≥0)
  have hgm : Measurable (fun p : ℝ≥0 → Fin d → ℤ => fun t => g.toEquiv (p t)) :=
    measurable_pi_iff.2 fun t => (measurable_of_countable g.toEquiv).comp (measurable_pi_apply t)
  have hgF : Measurable (fun v : Fin d → ℤ => g.toEquiv v) := measurable_of_countable _
  have hgWae : AEMeasurable (fun ω t => g.toEquiv (Wp ω t)) P := hgm.comp_aemeasurable hWae
  have key := step_symmetry_law hN g hg
  set Q : (ℝ≥0 → Fin d → ℤ) → Fin d → ℤ := fun p => F (fun t : Set.Icc (0 : ℝ≥0) T => p t) with hQ
  have hQm : Measurable Q := hF.comp hR
  have e1 : P.map (fun ω => g.toEquiv (F (fun t : Set.Icc (0 : ℝ≥0) T => Wp ω t))) =
      (P.map (fun ω t => g.toEquiv (Wp ω t))).map Q := by
    rw [AEMeasurable.map_map_of_aemeasurable hQm.aemeasurable hgWae]
    refine Measure.map_congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (hFg g hg _).symm
  have e2 : P.map (fun ω => F (fun t : Set.Icc (0 : ℝ≥0) T => Wp ω t)) = (P.map Wp).map Q :=
    (AEMeasurable.map_map_of_aemeasurable hQm.aemeasurable hWae).symm
  rw [e1, e2]
  exact congrArg (Measure.map Q) key

/-- Lattice symmetry of the regenerated walk, last assertion: a square-integrable equivariant functional is
centred and its coordinates have equal second moments (covariance `θ I`). -/
theorem step_symmetry_meancov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (hd : 1 ≤ d) (T : ℝ≥0) (F : (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) → Fin d → ℤ)
    (hF : Measurable F)
    (hFg : ∀ (g : Interchange.LatticeAut d), g.toEquiv 0 = 0 →
      ∀ w, F (fun t => g.toEquiv (w t)) = g.toEquiv (F w))
    (hint : Integrable (fun ω => ‖F (fun t : Set.Icc (0 : ℝ≥0) T =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ))‖ ^ 2) P) :
    (∀ i, ∫ ω, (F (fun t : Set.Icc (0 : ℝ≥0) T =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)) i : ℝ) ∂P = 0) ∧
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ i j, ∫ ω, (F (fun t : Set.Icc (0 : ℝ≥0) T =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)) i : ℝ) *
        (F (fun t : Set.Icc (0 : ℝ≥0) T =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)) j : ℝ) ∂P =
        if i = j then θ else 0 := by
  have hR : Measurable (fun p : ℝ≥0 → Fin d → ℤ => fun t : Set.Icc (0 : ℝ≥0) T => p t) :=
    measurable_pi_iff.2 fun t => measurable_pi_apply (t : ℝ≥0)
  have hZ := (hF.comp hR).comp_aemeasurable (aemeasurable_regenWalk_path hN)
  obtain ⟨-, -, h3, h4⟩ := Cyclic.meancov_of_symm hd hZ hint
    (fun g hg => step_symmetry_functional hN T F hF hFg g hg)
  exact ⟨h3, h4⟩

end ElboimSly.Paper
