/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMeancovSym
public import ElboimSly.Foundations.Cyclic.CycFarDriven
public import ElboimSly.Foundations.Cyclic.CycFarRegen
public import ElboimSly.Foundations.SRW.MomentsCanon
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# Symmetric mean and covariance (symmetric mean and covariance)

Symmetric mean and covariance. For every `t ≥ 0` the regenerated walk `W` of a Poisson environment
on `ℕ × S_β` has `E W(t) = 0` and `Cov W(t) = θ_t I` for some `θ_t ≥ 0`, and these moments exist
(`cyc_meancov`).

* `meancov_of_symm`: a square-integrable random vector in `ℤᵈ` whose law is invariant under every
  lattice automorphism fixing `0` has mean `0` and covariance `θ I`; the automorphisms used are the
  reflections of one coordinate and the transpositions of two coordinates.
* `integrable_sq_regen`: `E ‖W(t)‖² < ∞`. In construction (iii), `‖W(t)‖ ≤ 2 M((0, t])` with
  `M((0,t]) ~ Poi(2dt)` (`norm_drivenRegenFrom_le`), and the laws of (i) and (iii) agree
  (`regen_law_env_cut_map`). This is the pathwise core of ES22 Lemma 2.2, which gives the
  exponential moments; here the Poisson square integrability is used directly.
* `law_regen_lattice` gives the symmetry (invariance in law).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange ElboimSly.SRW

variable {d : ℕ}

theorem reflect_apply (i j : Fin d) (z : Fin d → ℤ) :
    (LatticeAut.reflect i).toEquiv z j = if j = i then -z j else z j := rfl

theorem reflect_zero (i : Fin d) : (LatticeAut.reflect i).toEquiv 0 = 0 := by
  funext j; simp [reflect_apply]

theorem permute_apply (σ : Equiv.Perm (Fin d)) (z : Fin d → ℤ) (j : Fin d) :
    (LatticeAut.permute σ).toEquiv z j = z (σ j) := by
  simp [LatticeAut.permute]

theorem permute_zero (σ : Equiv.Perm (Fin d)) : (LatticeAut.permute σ).toEquiv 0 = 0 := by
  funext j; simp [permute_apply]

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω} [IsProbabilityMeasure Pe]
  {Z : Ω → Fin d → ℤ}

omit [IsProbabilityMeasure Pe] in
theorem integral_comp_lattice (hZ : AEMeasurable Z Pe) (g : LatticeAut d)
    (hlaw : Pe.map (fun ω => g.toEquiv (Z ω)) = Pe.map Z) (h : (Fin d → ℤ) → ℝ) :
    ∫ ω, h (g.toEquiv (Z ω)) ∂Pe = ∫ ω, h (Z ω) ∂Pe := by
  have hm : Measurable h := measurable_of_countable h
  have hgZ : AEMeasurable (fun ω => g.toEquiv (Z ω)) Pe :=
    (measurable_of_countable g.toEquiv).comp_aemeasurable hZ
  rw [← integral_map hgZ hm.aestronglyMeasurable, hlaw, integral_map hZ hm.aestronglyMeasurable]

/-- A square-integrable random vector in `ℤᵈ` with a lattice-symmetric law has mean `0` and
covariance `θ I`. -/
theorem meancov_of_symm (hd : 1 ≤ d) (hZ : AEMeasurable Z Pe)
    (hint : Integrable (fun ω => ‖Z ω‖ ^ 2) Pe)
    (hsymm : ∀ g : LatticeAut d, g.toEquiv 0 = 0 →
      Pe.map (fun ω => g.toEquiv (Z ω)) = Pe.map Z) :
    (∀ i, Integrable (fun ω => (Z ω i : ℝ)) Pe) ∧
    (∀ i j, Integrable (fun ω => (Z ω i : ℝ) * (Z ω j : ℝ)) Pe) ∧
    (∀ i, ∫ ω, (Z ω i : ℝ) ∂Pe = 0) ∧
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ i j, ∫ ω, (Z ω i : ℝ) * (Z ω j : ℝ) ∂Pe = if i = j then θ else 0 := by
  have hcoord : ∀ (z : Fin d → ℤ) (i : Fin d), |(z i : ℝ)| ≤ ‖z‖ := fun z i => by
    have := norm_le_pi_norm z i
    rwa [Int.norm_eq_abs] at this
  have hone : Integrable (fun ω => 1 + ‖Z ω‖ ^ 2) Pe := (integrable_const (1 : ℝ)).add hint
  have hI1 : ∀ i, Integrable (fun ω => (Z ω i : ℝ)) Pe := by
    intro i
    refine hone.mono' ((measurable_of_countable (fun z : Fin d → ℤ => (z i : ℝ))).comp_aemeasurable
      hZ).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have := hcoord (Z ω) i
    nlinarith [norm_nonneg (Z ω), sq_nonneg (‖Z ω‖ - 1)]
  have hI2 : ∀ i j, Integrable (fun ω => (Z ω i : ℝ) * (Z ω j : ℝ)) Pe := by
    intro i j
    refine hint.mono' ((measurable_of_countable
      (fun z : Fin d → ℤ => (z i : ℝ) * (z j : ℝ))).comp_aemeasurable hZ).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hcoord (Z ω) i
    have h2 := hcoord (Z ω) j
    nlinarith [abs_nonneg ((Z ω i : ℝ)), abs_nonneg ((Z ω j : ℝ))]
  refine ⟨hI1, hI2, ?_, ?_⟩
  · intro i
    have h := integral_comp_lattice hZ (LatticeAut.reflect i)
      (hsymm _ (reflect_zero i)) (fun z => (z i : ℝ))
    simp only [reflect_apply, ite_true, Int.cast_neg] at h
    rw [integral_neg] at h
    linarith
  · have hi0 : Fin d := ⟨0, hd⟩
    set i0 : Fin d := ⟨0, hd⟩ with hi0def
    refine ⟨∫ ω, (Z ω i0 : ℝ) * (Z ω i0 : ℝ) ∂Pe, integral_nonneg fun ω => mul_self_nonneg _, ?_⟩
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      have h := integral_comp_lattice hZ (LatticeAut.permute (Equiv.swap i0 i))
        (hsymm _ (permute_zero _)) (fun z => (z i0 : ℝ) * (z i0 : ℝ))
      simp only [permute_apply, Equiv.swap_apply_left] at h
      exact h
    · simp only [hij, ite_false]
      have h := integral_comp_lattice hZ (LatticeAut.reflect i)
        (hsymm _ (reflect_zero i)) (fun z => (z i : ℝ) * (z j : ℝ))
      simp only [reflect_apply, ite_true, Ne.symm hij, ite_false, Int.cast_neg] at h
      have h' : ∫ ω, -((Z ω i : ℝ) * (Z ω j : ℝ)) ∂Pe = ∫ ω, (Z ω i : ℝ) * (Z ω j : ℝ) ∂Pe := by
        simpa only [neg_mul] using h
      rw [integral_neg] at h'
      linarith

end Abstract

variable {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}

theorem aemeasurable_regen
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (t : ℝ≥0) :
    AEMeasurable (fun ω => ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ)) Pe := by
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  have hm : Measurable fun ω => regRecProc ((regPlan d β).envFinalOr CycRec.empty (N ω)) :=
    measurable_regRecProc.comp (((regPlan d β).measurable_envFinalOr CycRec.empty).comp
      hN.measurable)
  have := ((measurable_pi_apply t).comp hm).aemeasurable (μ := Pe)
  refine this.congr ?_
  filter_upwards [regen_env_ae hN] with ω h
  exact (congrFun h t).symm

/-- `E ‖W(t)‖² < ∞`. -/
theorem integrable_sq_regen (_hd : 1 ≤ d) [IsProbabilityMeasure Pe]
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (t : ℝ≥0) :
    Integrable (fun ω => ‖ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ)‖ ^ 2) Pe := by
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  obtain ⟨Ω', _, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  set T : (ℝ≥0 → Fin d → ℤ) → ℝ := fun f => ‖f t‖ ^ 2 with hT
  have hTm : Measurable T :=
    (measurable_of_countable (fun v : Fin d → ℤ => ‖v‖ ^ 2)).comp (measurable_pi_apply t)
  have hlaw := regen_law_env_cut_map hN hN₀ hTm
  have hVm : Measurable fun ω (u : ℝ≥0) =>
      drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u := by
    have hV : (fun ω (u : ℝ≥0) => drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u) =
        fun ω (u : ℝ≥0) => drivenRegenFrom β.toNNReal (drivePath (N₀ ω)).fn u := by
      funext ω u
      have h0 : canonical d N₀ ω 0 = 0 := by simp [canonical, walk_zero]
      exact drivenRegenWalkCut_eq_drivenRegenFrom hb h0 u
    rw [hV]
    exact measurable_pi_iff.2 fun u => measurable_drivenRegenFrom_at hb
      (X := fun ω => drivePath (N₀ ω)) (measurable_drivePath.comp hN₀.measurable) u
  have hWae : AEMeasurable (fun ω => T (fun u : ℝ≥0 =>
      ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((u : ℝ≥0) : ℝ))) Pe :=
    ((measurable_of_countable (fun v : Fin d → ℤ => ‖v‖ ^ 2)).comp_aemeasurable
      (aemeasurable_regen hN t))
  -- integrability transfers through the law
  have hdrv : Integrable (fun ω => T (fun u : ℝ≥0 =>
      drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u)) Pd := by
    have hmeas : Measurable fun ω => T (fun u : ℝ≥0 =>
        drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u) := hTm.comp hVm
    have hwin := hasLaw_winCount hN₀ (a := 0) (b := (t : ℝ)) le_rfl t.2
    have hsq := poisson_integrable_sq hwin
    refine (hsq.const_mul 4).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_canonical_mem_cycCF hN₀ β.toNNReal hb] with ω hω
    have h0 : canonical d N₀ ω 0 = 0 := by simp [canonical, walk_zero]
    have hq := drivenRegenWalkCut_eq_drivenRegenFrom hb h0 t
    have hcan : canonical d N₀ ω = fun u : ℝ≥0 => walk d (N₀ ω) (u : ℝ) := rfl
    have hle := norm_drivenRegenFrom_le hb (ν := N₀ ω) (by rw [← hcan]; exact hω)
      (le_refl t)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [hT]
    rw [hq]
    rw [← hcan] at hle
    have hw : (winCount N₀ 0 (t : ℝ) ω : ℝ) = (natOf (tot (N₀ ω) (Ioc 0 (t : ℝ))) : ℝ) := rfl
    rw [hw]
    nlinarith [norm_nonneg (drivenRegenFrom β.toNNReal (canonical d N₀ ω) t)]
  have hmapI : Integrable id (Pd.map fun ω => T (fun u : ℝ≥0 =>
      drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) u)) :=
    (integrable_map_measure aestronglyMeasurable_id (hTm.comp hVm).aemeasurable).2 hdrv
  rw [← hlaw] at hmapI
  exact (integrable_map_measure aestronglyMeasurable_id hWae).1 hmapI

/-- **symmetric mean and covariance** (symmetric mean and covariance): for every `t ≥ 0` the regenerated walk
`W(t)` has integrable coordinates and products, `E W(t) = 0`, and
`Cov W(t) = E [W(t) W(t)ᵀ] = θ_t I` for some `θ_t ≥ 0`. -/
theorem cyc_meancov (hd : 1 ≤ d) [IsProbabilityMeasure Pe]
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (t : ℝ≥0) :
    (∀ i, Integrable (fun ω =>
        (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) i : ℝ)) Pe) ∧
    (∀ i j, Integrable (fun ω =>
        (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) i : ℝ) *
        (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) j : ℝ)) Pe) ∧
    (∀ i, ∫ ω, (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) i : ℝ) ∂Pe = 0) ∧
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ i j, ∫ ω, (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) i : ℝ) *
        (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) j : ℝ) ∂Pe =
        if i = j then θ else 0 :=
  meancov_of_symm hd (aemeasurable_regen hN t) (integrable_sq_regen hd hN t)
    (fun g hg => law_regen_lattice hN g hg t)

end ElboimSly.Cyclic

end
