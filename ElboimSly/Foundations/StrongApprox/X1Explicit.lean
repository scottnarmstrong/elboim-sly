/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1Err3
public import ElboimSly.Foundations.StrongApprox.X1Numerics
public import Mathlib

/-!
# X1θ with an explicit threshold

X1θ with the explicit threshold ell_0(d)=max100,10d (Part II).

For `ℓ ≥ max (10^5) (10 d)`, a measure `μ` as in X1θ and `1 ≤ M ≤ (log ℓ)³`, the coupling space
carries a coupling `Q` of `μ^{⊗ℓ}` and `(N(0,I_d))^{⊗ℓ}` with the stated error bound.
(The written proof's threshold `max 100 (10 d)` is also admissible; the larger threshold simplifies
the elementary estimates.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

lemma measurable_Yvec (d ℓ : ℕ) : Measurable (Yvec (d := d) (ℓ := ℓ)) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hB := (isStandardBM_Bd d).measurable
  exact ((hB _).comp measurable_snd).sub ((hB _).comp measurable_snd)

/-- X1θ with the explicit threshold ell_0(d)=max100,10d. -/
theorem x1_explicit {d : ℕ} (ℓ : ℕ) (hℓ : max (10 ^ 5) (10 * d) ≤ ℓ) (M : ℝ) (hM1 : 1 ≤ M)
    (hM : M ≤ Real.log ℓ ^ 3) (μ : Measure (Fin d → ℝ)) (hμ : IsProbabilityMeasure μ)
    (hsupp : μ {x | ‖x‖ ≤ M} = 1)
    (hsym : ∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) → μ.map (fun x => ε * x) = μ)
    (hsq : ∀ k, ∫ x, x k ^ 2 ∂μ = 1) :
    ∃ Q : Measure ((Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.pi (fun _ : Fin ℓ => μ) ∧
      Q.map Prod.snd = Measure.pi (fun _ : Fin ℓ =>
        Measure.pi (fun _ : Fin d => gaussianReal 0 1)) ∧
      Q.real {p | ∃ j : Fin ℓ,
          (ℓ : ℝ) ^ ((1 : ℝ) / 4) * Real.log ℓ ^ 12 ≤
            ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖}
        ≤ Real.exp (-(Real.log ℓ ^ 3)) := by
  have := hμ
  have : IsProbabilityMeasure (μ.map absVec) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_absVec d).aemeasurable).2 inferInstance
  set P := P1 d ℓ (μ.map absVec) with hP
  have hpair : Measurable fun ω : Ω1 d ℓ => (Xvec ω, Yvec ω) :=
    (measurable_Xvec ℓ).prodMk (measurable_Yvec d ℓ)
  refine ⟨P.map fun ω => (Xvec ω, Yvec ω), ?_, ?_, ?_, ?_⟩
  · exact (Measure.isProbabilityMeasure_map_iff hpair.aemeasurable).2 inferInstance
  · rw [Measure.map_map measurable_fst hpair]
    exact map_Xvec ℓ μ hsym
  · rw [Measure.map_map measurable_snd hpair]
    have e : (Prod.snd ∘ fun ω : Ω1 d ℓ => (Xvec ω, Yvec ω)) =
        unitIncr (Bd d) ℓ ∘ Prod.snd := rfl
    have hu : Measurable (unitIncr (Bd d) ℓ : ΩB d → Fin ℓ → Fin d → ℝ) := by
      refine measurable_pi_iff.2 fun i => ?_
      have hB := (isStandardBM_Bd d).measurable
      exact (hB _).sub (hB _)
    rw [e, ← Measure.map_map hu measurable_snd]
    have hsnd : P.map Prod.snd = PB d := by
      rw [hP, P1, Measure.map_snd_prod]; simp
    rw [hsnd]
    exact map_unitIncr ℓ (isStandardBM_Bd d)
  · set L := Real.log ℓ with hL
    have hℓ1 : 10 ^ 5 ≤ ℓ := le_trans (le_max_left _ _) hℓ
    have h10d : 10 * d ≤ ℓ := le_trans (le_max_right _ _) hℓ
    have hℓR : (100000 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    have hℓ0 : 0 < (ℓ : ℝ) := by linarith
    have hℓ2 : 2 ≤ ℓ := by omega
    have hL4 : 4 ≤ L := four_le_log (by linarith)
    have hcube : L ^ 3 ≤ ℓ := log_cube_le (by linarith)
    set thr : ℝ := (ℓ : ℝ) ^ ((1 : ℝ) / 4) * L ^ 12 with hthr
    set S : Set ((Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ)) := {p | ∃ j : Fin ℓ,
      thr ≤ ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖} with hS
    have hSm : MeasurableSet S := by
      have : S = ⋃ j : Fin ℓ, {p : (Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ) |
          thr ≤ ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖} := by
        ext p; simp [hS]
      rw [this]
      refine MeasurableSet.iUnion fun j => measurableSet_le measurable_const ?_
      refine measurable_norm.comp (Finset.measurable_sum _ fun i _ => ?_)
      exact ((measurable_pi_apply i).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_snd)
    rw [measureReal_def, Measure.map_apply hpair hSm]
    have hγ1 : 1 ≤ 2 * L ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hL4 3]
    have hγ2 : 2 * L ^ 3 ≤ 2 * ℓ := by linarith
    have hmain := tail_general μ hℓ2 hM1 hsupp hsq hγ1 hγ2
    have hsub : (fun ω : Ω1 d ℓ => (Xvec ω, Yvec ω)) ⁻¹' S ⊆ {ω | ∃ j : Fin ℓ,
        59 * M * (ℓ : ℝ) ^ (1 / 4 : ℝ) * (2 * L ^ 3) ^ (3 / 4 : ℝ) ≤ ‖x1Spart ω j‖} := by
      rintro ω ⟨j, hj⟩
      refine ⟨j, le_trans ?_ hj⟩
      exact thr_le hℓ0 hM1 hM hL4
    have hb : 10 * (d : ℝ) * ℓ * Real.exp (-(2 * L ^ 3)) ≤ Real.exp (-(L ^ 3)) :=
      tail_le hℓ0 h10d hL4
    refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le ?_
    exact (measure_mono hsub).trans (hmain.trans (ENNReal.ofReal_le_ofReal hb))

end ElboimSly.StrongApprox
