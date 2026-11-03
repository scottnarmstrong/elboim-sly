/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Tube
public import ElboimSly.Foundations.Brownian.HitBall
import Mathlib

/-!
# Escaping a box for ever

Escaping a box for ever.

The coordinate direction `e₁` is the unit vector `e0 i0` of a fixed coordinate `i0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

/-- The unit vector `e_{i0}`. -/
noncomputable def e0 {d : ℕ} (i0 : Fin d) : Fin d → ℝ := Pi.single i0 1

lemma norm_e0 {d : ℕ} (i0 : Fin d) : ‖e0 i0‖ = 1 := by
  rw [e0, Pi.norm_single]; simp

lemma e0_apply_self {d : ℕ} (i0 : Fin d) : e0 i0 i0 = 1 := by simp [e0]

/-- Escaping a box for ever. `λ = max {4, 2 (2 C_hit)^{1/(d-2)}}`. -/
noncomputable def lamBox (d : ℕ) : ℝ := max 4 (2 * (2 * Chit d) ^ (1 / ((d : ℝ) - 2)))

/-- Escaping a box for ever. `q_box(d, M) = c_tube(d, 2 λ M)/2`. -/
noncomputable def qbox (d : ℕ) (M : ℝ) : ℝ := ctube d (2 * lamBox d * M) / 2

/-- The time `T = R ρ` with `R = λ M L` and `ρ = L/2`. -/
noncomputable def escT (d : ℕ) (M L : ℝ) : ℝ≥0 := (lamBox d * M * L * (L / 2)).toNNReal

/-- Escaping a box for ever. The path set `𝔈`: following `(u/T) R e₁` within `ρ` up to
time `T` (on the countable dense subset of `[0,T]`), and afterwards `‖σ w(T + v)‖ > M L` in the
sense of infima over the countable dense subsets of `[0, M']`, for every `M'`. -/
def escapeBoxSet (d : ℕ) (i0 : Fin d) (σ M L : ℝ) : Set (PathSpace d) :=
  {w | (∀ u ∈ denseSub (Set.Icc (0 : ℝ≥0) (escT d M L)),
      ‖σ • w u - ((u : ℝ) / escT d M L * (lamBox d * M * L)) • e0 i0‖ ≤ L / 2) ∧
    ∀ M' : ℕ, ((M * L : ℝ) : EReal) <
      ⨅ v ∈ denseSub (Set.Icc (0 : ℝ≥0) M'), ((‖σ • w (escT d M L + v)‖ : ℝ) : EReal)}

lemma measurableSet_escapeBoxSet (d : ℕ) (i0 : Fin d) (σ M L : ℝ) :
    MeasurableSet (escapeBoxSet d i0 σ M L) := by
  have e : escapeBoxSet d i0 σ M L =
      (⋂ u ∈ denseSub (Set.Icc (0 : ℝ≥0) (escT d M L)), {w : PathSpace d |
        ‖σ • w u - ((u : ℝ) / escT d M L * (lamBox d * M * L)) • e0 i0‖ ≤ L / 2}) ∩
      ⋂ M' : ℕ, {w : PathSpace d | ((M * L : ℝ) : EReal) <
        ⨅ v ∈ denseSub (Set.Icc (0 : ℝ≥0) M'), ((‖σ • w (escT d M L + v)‖ : ℝ) : EReal)} := by
    ext w; simp [escapeBoxSet]
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun u _ => ?_).inter
    (MeasurableSet.iInter fun M' => ?_)
  · exact measurableSet_le (by fun_prop : Measurable fun w : PathSpace d =>
      ‖σ • w u - ((u : ℝ) / escT d M L * (lamBox d * M * L)) • e0 i0‖) measurable_const
  · refine measurableSet_lt measurable_const (Measurable.biInf _ (denseSub_countable _) fun v _ => ?_)
    exact measurable_coe_real_ereal.comp
      (by fun_prop : Measurable fun w : PathSpace d => ‖σ • w (escT d M L + v)‖)

section B

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- Escaping a box for ever (b), for the paths in `𝔈`. -/
theorem escapeBox_avoids {w : PathSpace d} (hw : Continuous w) {i0 : Fin d} {σ M L : ℝ}
    (_hσ : 0 < σ) (hM : 1 ≤ M) (hL : 0 < L) (hlam : 4 ≤ lamBox d) (hmem : w ∈ escapeBoxSet d i0 σ M L)
    (x : Fin d → ℝ) {Q : Set (Fin d → ℝ)}
    (hQ : Q ⊆ {y | y i0 ≤ x i0 - L} ∩ Metric.closedBall x (M * L)) :
    ∀ s : ℝ≥0, x + σ • w s ∉ Q := by
  obtain ⟨H1, H2⟩ := hmem
  intro s hs
  have hT : (escT d M L : ℝ) = lamBox d * M * L * (L / 2) :=
    Real.coe_toNNReal _ (by have : 0 ≤ lamBox d := by linarith
                            positivity)
  have hTpos : 0 < (escT d M L : ℝ) := by
    rw [hT]; have : 0 < lamBox d := by linarith
    positivity
  have hq := hQ hs
  by_cases hsT : s ≤ escT d M L
  · -- before time `T`
    have hg : Continuous fun u : ℝ≥0 =>
        ‖σ • w u - ((u : ℝ) / escT d M L * (lamBox d * M * L)) • e0 i0‖ :=
      (((hw.const_smul σ).sub ((NNReal.continuous_coe.div_const _ |>.mul continuous_const).smul
        continuous_const))).norm
    have hall := le_on_of_denseSub (J := Set.Icc (0 : ℝ≥0) (escT d M L)) Set.ordConnected_Icc hg H1
    have h1 := hall s ⟨zero_le, hsT⟩
    have h2 := norm_le_pi_norm (σ • w s - ((s : ℝ) / escT d M L * (lamBox d * M * L)) • e0 i0) i0
    have h3 : (σ • w s - ((s : ℝ) / escT d M L * (lamBox d * M * L)) • e0 i0) i0 =
        σ * w s i0 - (s : ℝ) / escT d M L * (lamBox d * M * L) := by
      simp [e0_apply_self]
    rw [h3, Real.norm_eq_abs] at h2
    have h4 : 0 ≤ (s : ℝ) / escT d M L * (lamBox d * M * L) := by
      have : 0 < lamBox d := by linarith
      positivity
    have h5 : -(L / 2) ≤ σ * w s i0 := by
      have := (abs_le.1 (h2.trans h1)).1
      linarith
    have h6 : (x + σ • w s) i0 ≤ x i0 - L := hq.1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h6
    linarith
  · -- after time `T`
    have hs' := not_le.1 hsT
    have hv : s - escT d M L ∈ Set.Icc (0 : ℝ≥0) ⌈((s - escT d M L : ℝ≥0) : ℝ)⌉₊ := by
      refine ⟨zero_le, ?_⟩
      rw [← NNReal.coe_le_coe]
      simpa using Nat.le_ceil (((s - escT d M L : ℝ≥0)) : ℝ)
    have hcont : Continuous fun v : ℝ≥0 => ‖σ • w (escT d M L + v)‖ :=
      ((hw.comp (continuous_const.add continuous_id)).const_smul σ).norm
    have key := H2 ⌈((s - escT d M L : ℝ≥0) : ℝ)⌉₊
    rw [← iInf_eq_denseSub (J := Set.Icc (0 : ℝ≥0) _) Set.ordConnected_Icc hcont] at key
    have h1 : ((M * L : ℝ) : EReal) < ((‖σ • w (escT d M L + (s - escT d M L))‖ : ℝ) : EReal) :=
      key.trans_le (biInf_le _ hv)
    rw [add_tsub_cancel_of_le hs'.le] at h1
    have h2 := EReal.coe_lt_coe_iff.1 h1
    have h3 := hq.2
    rw [Metric.mem_closedBall, dist_eq_norm] at h3
    have e : x + σ • w s - x = σ • w s := by abel
    rw [e] at h3
    linarith

end B

end ElboimSly.Brownian
