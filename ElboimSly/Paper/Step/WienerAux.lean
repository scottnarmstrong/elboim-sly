/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsWienerMeasure
public import Mathlib

/-!
# Second moment under Wiener measure

Support for second moment of a truncated endpoint (moments for `IsWienerMeasure`): for a Wiener
measure `𝕎` on `C(ℝ≥0, ℝ^d)`, `∫⁻ ofReal (‖w t‖²) ≤ d t`. The statement is in `lintegral` form since
only almost-everywhere measurability of the evaluations is available.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ}

theorem wiener_aemeasurable_eval {𝕎 : Measure C(ℝ≥0, Fin d → ℝ)} (hW : IsWienerMeasure d 𝕎)
    (t : ℝ≥0) (i : Fin d) : AEMeasurable (fun w : C(ℝ≥0, Fin d → ℝ) => w t i) 𝕎 :=
  (hW.2.1 i).aemeasurable t

theorem wiener_aemeasurable_norm_sq {𝕎 : Measure C(ℝ≥0, Fin d → ℝ)} (hW : IsWienerMeasure d 𝕎)
    (t : ℝ≥0) : AEMeasurable (fun w : C(ℝ≥0, Fin d → ℝ) => ENNReal.ofReal (‖w t‖ ^ 2)) 𝕎 := by
  have : AEMeasurable (fun w : C(ℝ≥0, Fin d → ℝ) => w t) 𝕎 :=
    aemeasurable_pi_iff.2 fun i => wiener_aemeasurable_eval hW t i
  exact ((this.norm).pow_const 2).ennreal_ofReal

theorem wiener_lintegral_sq {𝕎 : Measure C(ℝ≥0, Fin d → ℝ)} (hW : IsWienerMeasure d 𝕎)
    (t : ℝ≥0) (i : Fin d) :
    ∫⁻ w, ENNReal.ofReal ((w t i) ^ 2) ∂𝕎 = ENNReal.ofReal t := by
  have hlaw := (hW.2.1 i).hasLaw_eval t
  have h1 : ∫⁻ w, ENNReal.ofReal ((w t i) ^ 2) ∂𝕎 =
      ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 t) := by
    rw [← hlaw.map_eq]
    rw [lintegral_map' (by fun_prop) hlaw.aemeasurable]
  rw [h1]
  have hmem : MemLp id 2 (gaussianReal 0 t) := memLp_id_gaussianReal 2
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 t) := hmem.integrable_sq
  have hvar : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 t) = t := by
    have h := variance_id_gaussianReal (μ := 0) (v := t)
    rw [variance_eq_integral aemeasurable_id] at h
    have h0 : ∫ x : ℝ, id x ∂(gaussianReal 0 t) = 0 := integral_id_gaussianReal
    rw [h0] at h
    simpa using h
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg x),
    hvar]

theorem wiener_lintegral_norm_sq_le {𝕎 : Measure C(ℝ≥0, Fin d → ℝ)} (hW : IsWienerMeasure d 𝕎)
    (t : ℝ≥0) :
    ∫⁻ w, ENNReal.ofReal (‖w t‖ ^ 2) ∂𝕎 ≤ ENNReal.ofReal (d * t) := by
  have hpt : ∀ w : C(ℝ≥0, Fin d → ℝ), ENNReal.ofReal (‖w t‖ ^ 2) ≤
      ∑ i, ENNReal.ofReal ((w t i) ^ 2) := by
    intro w
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : ‖w t‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      simp [this]
    · obtain ⟨i, hi⟩ : ∃ i, ‖w t‖ = |w t i| := by
        have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
          Finset.univ_nonempty (fun b => ‖w t b‖₊)
        refine ⟨i, ?_⟩
        rw [Pi.norm_def, hi]; simp
      rw [hi, sq_abs]
      exact Finset.single_le_sum (f := fun i => ENNReal.ofReal ((w t i) ^ 2))
        (fun j _ => zero_le) (Finset.mem_univ i)
  calc ∫⁻ w, ENNReal.ofReal (‖w t‖ ^ 2) ∂𝕎
      ≤ ∫⁻ w, ∑ i, ENNReal.ofReal ((w t i) ^ 2) ∂𝕎 := lintegral_mono hpt
    _ = ∑ i, ∫⁻ w, ENNReal.ofReal ((w t i) ^ 2) ∂𝕎 :=
        lintegral_finsetSum' _ fun i _ =>
          ((wiener_aemeasurable_eval hW t i).pow_const 2).ennreal_ofReal
    _ = ∑ _i : Fin d, ENNReal.ofReal t := by simp_rw [wiener_lintegral_sq hW]
    _ = ENNReal.ofReal (d * t) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        simp

end ElboimSly.Paper
