/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.SegmentsPath
public import Mathlib

/-!
# The law of `Γ(w)` for an i.i.d. family of segments

A driving path from independent segments.

* `stepGamma_stepWin`: for segments `w i` constant after `T` and starting at `0`,
  `θ_{jT} Γ_ℓ(w) = w j` on `[0, T]`, for `j < ℓ`.
* `map_stepGamma`: if `w_0, …, w_{ℓ-1}, …` are independent with the law `ν_T` of
  `X(· ∧ T)`, then `Γ_ℓ(w)` has the law of `X(· ∧ ℓT)`.
* `map_stepGamma_functional`: hence `Φ(Γ_ℓ(w))` has the law of `Φ(X)` for every measurable `Φ`
  that depends only on the path on `[0, ℓT]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.SRW
open scoped NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- `θ_{jT} Γ_ℓ(w) = w_j` on `[0, T]`, for `j < ℓ`. -/
theorem stepGamma_stepWin (T : ℝ≥0) {w : ℕ → ℝ≥0 → Fin d → ℤ} (_hw0 : ∀ i, w i 0 = 0)
    (_hwT : ∀ i s, w i s = w i (min s T)) (j : ℕ) :
    ∀ (ℓ : ℕ) (w : ℕ → ℝ≥0 → Fin d → ℤ), (∀ i, w i 0 = 0) → (∀ i s, w i s = w i (min s T)) →
      j < ℓ → stepWin ((j : ℝ≥0) * T) T (stepGamma T ℓ w) = w j := by
  clear _hw0 _hwT w
  induction j with
  | zero =>
    intro ℓ w hw0 hwT hj
    obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
    funext u
    have h0 := stepGamma_apply_zero T (ℓ + 1) hw0
    simp only [stepWin, SRW.stopPath, SRW.theta, Nat.cast_zero, zero_mul, zero_add, h0, sub_zero]
    rw [stepGamma, stepCat_of_le _ _ (min_le_right u T), ← hwT 0 u]
  | succ j ih =>
    intro ℓ w hw0 hwT hj
    obtain ⟨ℓ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ℓ ≠ 0)
    have hsh := stepGamma_shift T ℓ hw0
    have key := ih ℓ (fun i => w (i + 1)) (fun i => hw0 (i + 1)) (fun i s => hwT (i + 1) s)
      (by omega)
    rw [← key]
    funext u
    have e1 : ∀ v, stepGamma T (ℓ + 1) w (T + v) = stepGamma T (ℓ + 1) w T +
        stepGamma T ℓ (fun i => w (i + 1)) v := by
      intro v
      have := congrFun hsh v
      rw [← this]; abel
    have e2 : ((j + 1 : ℕ) : ℝ≥0) * T = T + (j : ℝ≥0) * T := by push_cast; ring
    simp only [stepWin, SRW.stopPath, SRW.theta]
    rw [e2, add_assoc T, e1, e1]
    abel

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {Z : Ω → PathSpace d}

/-- **The law of `Γ_ℓ(w)`** (a driving path from independent segments). If `w_0, w_1, …` are independent with the law
of the SRW stopped at `T`, then `Γ_ℓ(w)` has the law of the SRW stopped at `ℓT`. -/
theorem map_stepGamma (hZ : IsSRW P Z) (hZ0 : ∀ ω, Z ω 0 = 0) (T : ℝ≥0) (ℓ : ℕ)
    {w : ℕ → Ω' → PathSpace d} (hwm : ∀ i, Measurable (w i)) (hwi : iIndepFun w P')
    (hwl : ∀ i, P'.map (w i) = P.map (fun ω => SRW.stopPath T (Z ω))) :
    P'.map (fun ω => stepGamma T ℓ fun i => w i ω) =
      P.map (fun ω => SRW.stopPath ((ℓ : ℝ≥0) * T) (Z ω)) := by
  have := hZ.isProbabilityMeasure
  have := hwi.isProbabilityMeasure
  -- the windows of `Z`
  set v : ℕ → Ω → PathSpace d := fun j ω => stepWin ((j : ℝ≥0) * T) T (Z ω) with hv
  have hvm : ∀ j, Measurable (v j) := fun j => (measurable_stepWin _ _).comp hZ.1
  have hvi : iIndepFun v P :=
    iIndepFun_stepWin hZ (fun j => (j : ℝ≥0) * T) (fun _ => T) (fun j => by
      push_cast; rw [add_mul, one_mul])
  have hvl : ∀ j, P.map (v j) = P.map (fun ω => SRW.stopPath T (Z ω)) :=
    fun j => map_stepWin hZ _ _
  have hjoint : P'.map (fun ω i => w i ω) = P.map (fun ω i => v i ω) := by
    rw [hwi.map_fun_eq_infinitePi_map hwm, hvi.map_fun_eq_infinitePi_map hvm]
    congr 1
    funext i
    rw [hwl i, hvl i]
  have hG : Measurable (fun f : ℕ → PathSpace d => stepGamma T ℓ f) := measurable_stepGamma T ℓ
  have hwm' : Measurable fun ω i => w i ω := measurable_pi_iff.2 hwm
  have hvm' : Measurable fun ω i => v i ω := measurable_pi_iff.2 hvm
  calc P'.map (fun ω => stepGamma T ℓ fun i => w i ω)
      = (P'.map (fun ω i => w i ω)).map (stepGamma T ℓ) := (Measure.map_map hG hwm').symm
    _ = (P.map (fun ω i => v i ω)).map (stepGamma T ℓ) := by rw [hjoint]
    _ = P.map (fun ω => stepGamma T ℓ fun i => v i ω) := Measure.map_map hG hvm'
    _ = _ := map_stepGamma_windows hZ hZ0 T ℓ

/-- `Φ(Γ_ℓ(w))` has the law of `Φ(X)` for every measurable `Φ` that depends only on the path on
`[0, ℓT]`. -/
theorem map_stepGamma_functional (hZ : IsSRW P Z) (hZ0 : ∀ ω, Z ω 0 = 0) (T : ℝ≥0) (ℓ : ℕ)
    {w : ℕ → Ω' → PathSpace d} (hwm : ∀ i, Measurable (w i)) (hwi : iIndepFun w P')
    (hwl : ∀ i, P'.map (w i) = P.map (fun ω => SRW.stopPath T (Z ω)))
    {Φ : PathSpace d → ℝ≥0} (hΦ : Measurable Φ)
    (hΦT : ∀ x, Φ x = Φ (SRW.stopPath ((ℓ : ℝ≥0) * T) x)) :
    P'.map (fun ω => Φ (stepGamma T ℓ fun i => w i ω)) = P.map (fun ω => Φ (Z ω)) := by
  have hG : Measurable fun ω => stepGamma T ℓ fun i => w i ω :=
    (measurable_stepGamma T ℓ).comp (measurable_pi_iff.2 hwm)
  have h1 := map_stepGamma hZ hZ0 T ℓ hwm hwi hwl
  have hS : Measurable fun ω => SRW.stopPath ((ℓ : ℝ≥0) * T) (Z ω) :=
    (measurable_stopPath _).comp hZ.1
  calc P'.map (fun ω => Φ (stepGamma T ℓ fun i => w i ω))
      = (P'.map fun ω => stepGamma T ℓ fun i => w i ω).map Φ := (Measure.map_map hΦ hG).symm
    _ = (P.map fun ω => SRW.stopPath ((ℓ : ℝ≥0) * T) (Z ω)).map Φ := by rw [h1]
    _ = P.map (fun ω => Φ (SRW.stopPath ((ℓ : ℝ≥0) * T) (Z ω))) := Measure.map_map hΦ hS
    _ = P.map (fun ω => Φ (Z ω)) := by
      congr 1
      funext ω
      exact (hΦT (Z ω)).symm

end ElboimSly.Paper
