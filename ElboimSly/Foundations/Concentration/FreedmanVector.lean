/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.Freedman

/-!
# Freedman's inequality, vector version

Vector version via coordinates. The coordinatewise hypotheses of the written proof are stated
as: each coordinate process `fun j ω => M j ω c` is a martingale with `M 0 = 0`.
-/

public section

namespace ElboimSly

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Freedman's inequality, vector version.** Vector version via coordinates.
The vector martingale `M : ℕ → Ω → Fin d → ℝ` (sup norm) has coordinate martingales
`fun j ω => M j ω c`, increments of norm at most `b`, and for each coordinate `c` a predictable
bound `v c` for the conditional variances with total at most `V` a.s. -/
theorem concFreedman_vector [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {d k : ℕ} (hd : 1 ≤ d)
    {M : ℕ → Ω → Fin d → ℝ} {v : Fin d → ℕ → Ω → ℝ} {b V x : ℝ}
    (hM0 : M 0 = 0) (hM : ∀ c, Martingale (fun j ω => M j ω c) ℱ μ) (hb : 0 ≤ b)
    (hbd : ∀ j < k, ∀ᵐ ω ∂μ, ‖M (j + 1) ω - M j ω‖ ≤ b)
    (hv : ∀ c, ∀ j < k, StronglyMeasurable[ℱ j] (v c (j + 1)))
    (hv0 : ∀ c, ∀ j < k, 0 ≤ v c (j + 1))
    (hvar : ∀ c, ∀ j < k,
      μ[(fun ω => M (j + 1) ω c - M j ω c) ^ 2 | ℱ j] ≤ᵐ[μ] v c (j + 1))
    (hx : 0 ≤ x) (hV : 0 < V)
    (hQ : ∀ c, ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range k, v c (i + 1) ω ≤ V) :
    μ.real {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩ (fun j => ‖M j ω‖)} ≤
      2 * d * Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) := by
  set R : ℝ := Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rcases hx.eq_or_lt with rfl | hxpos
  · refine measureReal_le_one.trans ?_
    have hR1 : R = 1 := by simp [hR]
    rw [hR1]; linarith
  -- coordinatewise
  have hcoord : ∀ c : Fin d, μ.real {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩
        (fun j => |M j ω c|)} ≤ 2 * R := fun c =>
    concFreedman_max_abs_ge (M := fun j ω => M j ω c) (v := v c) (by funext ω; simp [hM0]) (hM c) hb
      (fun j hj => (hbd j hj).mono fun ω h =>
        (norm_le_pi_norm (M (j + 1) ω - M j ω) c).trans h)
      (hv c) (hv0 c) (hvar c) hx hV (hQ c)
  have hsub : {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩ (fun j => ‖M j ω‖)} ⊆
      ⋃ c : Fin d, {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩ (fun j => |M j ω c|)} := by
    intro ω hω
    obtain ⟨j, hj, hxj⟩ := (Finset.le_sup'_iff (f := fun j => ‖M j ω‖) _).1 (show x ≤ _ from hω)
    have hne : ¬ ‖M j ω‖ < x := not_lt.2 hxj
    rw [pi_norm_lt_iff hxpos] at hne
    push Not at hne
    obtain ⟨c, hc⟩ := hne
    refine Set.mem_iUnion.2 ⟨c, ?_⟩
    show x ≤ _
    exact le_trans (by simpa using hc) (Finset.le_sup' (f := fun j => |M j ω c|) hj)
  calc μ.real {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩ (fun j => ‖M j ω‖)}
      ≤ μ.real (⋃ c : Fin d, {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩
        (fun j => |M j ω c|)}) := measureReal_mono hsub
    _ ≤ ∑ c : Fin d, μ.real {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩
        (fun j => |M j ω c|)} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : Fin d, 2 * R := Finset.sum_le_sum fun c _ => hcoord c
    _ = 2 * d * R := by simp; ring

end ElboimSly
