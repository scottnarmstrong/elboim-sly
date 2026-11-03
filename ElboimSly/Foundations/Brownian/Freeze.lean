/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Markov
import Mathlib

/-!
# Freezing an independent variable; the Markov property in freezing form

Freezing an independent variable; Markov property at a fixed time (c).

* `lintegral_freeze`: freezing an independent variable, for independent `X : Ω → E`, `Y : Ω → F` and a measurable
  `φ : E → F → [0,∞]`, `E φ(X,Y) = E Ψ(X)` with `Ψ(x) = ∫ φ(x,y) dμ_Y`. The `σ`-algebras on `E`
  and `F` are explicit, so that `E` may be `Ω` with a sub-`σ`-algebra (the case used for Markov).
* `IsStandardBrownianMotion.lintegral_shift_freeze`: Markov property at a fixed time (c), the freezing form.
* `IsStandardBrownianMotion.lintegral_indicator_shift`: Markov property at a fixed time (c), second statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

section Freeze

variable {Ω E F : Type*} [mΩ : MeasurableSpace Ω] {mE : MeasurableSpace E}
  {mF : MeasurableSpace F} {P : Measure Ω}

/-- Freezing an independent variable. -/
theorem lintegral_freeze [IsProbabilityMeasure P] {X : Ω → E} {Y : Ω → F}
    (hX : Measurable X) (hY : Measurable Y) (h : IndepFun X Y P)
    {φ : E → F → ℝ≥0∞} (hφ : Measurable (Function.uncurry φ)) :
    ∫⁻ ω, φ (X ω) (Y ω) ∂P = ∫⁻ ω, ∫⁻ y, φ (X ω) y ∂(P.map Y) ∂P := by
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 h
  have hΦ : Measurable (fun x => ∫⁻ y, φ x y ∂(P.map Y)) :=
    Measurable.lintegral_prod_right' (ν := P.map Y) hφ
  calc ∫⁻ ω, φ (X ω) (Y ω) ∂P
      = ∫⁻ z, Function.uncurry φ z ∂(P.map (fun ω => (X ω, Y ω))) := by
        rw [lintegral_map hφ hpair]; rfl
    _ = ∫⁻ x, ∫⁻ y, φ x y ∂(P.map Y) ∂(P.map X) := by
        rw [hmap, lintegral_prod _ hφ.aemeasurable]; rfl
    _ = ∫⁻ ω, ∫⁻ y, φ (X ω) y ∂(P.map Y) ∂P := by
        rw [lintegral_map hΦ hX]

end Freeze

section Markov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The law of the shifted path is Wiener measure. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.map_shiftPath [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (a : ℝ≥0) :
    P.map (shiftPath B a) = wienerMeasure d :=
  (hB.shift a).map_pathMap_eq_wiener

/-- Markov property at a fixed time (c), freezing form. For `φ : Ω × W → [0,∞]` measurable for
`ℱ_a ⊗ 𝒫`, `E φ(·, sh_a B) = ∫∫ φ(ω,w) Wiener(dw) P(dω)`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.lintegral_shift_freeze [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (a : ℝ≥0)
    {φ : Ω → (ℝ≥0 → Fin d → ℝ) → ℝ≥0∞}
    (hφ : @Measurable (Ω × (ℝ≥0 → Fin d → ℝ)) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω _ (bmFiltration B a) _) _ (Function.uncurry φ)) :
    ∫⁻ ω, φ ω (shiftPath B a ω) ∂P = ∫⁻ ω, ∫⁻ w, φ ω w ∂(wienerMeasure d) ∂P := by
  have hX : @Measurable Ω Ω mΩ (bmFiltration B a) id := by
    intro t ht
    exact bmFiltration_le hB.measurable a _ ht
  have hind : @IndepFun Ω Ω (ℝ≥0 → Fin d → ℝ) mΩ (bmFiltration B a) _ id (shiftPath B a) P := by
    have := (hB.indep_shift a).symm
    show Indep (MeasurableSpace.comap (id : Ω → Ω) (bmFiltration B a))
      (MeasurableSpace.comap (shiftPath B a) inferInstance) P
    rw [MeasurableSpace.comap_id]
    exact this
  have := lintegral_freeze (mE := bmFiltration B a) (X := id) (φ := φ) hX
    (measurable_shiftPath hB.measurable a) hind hφ
  rw [hB.map_shiftPath a] at this
  exact this

/-- Markov property at a fixed time (c), the second statement. Let `Z` be `ℱ_a`-measurable with values
in a measurable space `E`, `A ∈ ℱ_a`, and `Φ : E × W → [0,∞]` measurable. Then
`E[1_A Φ(Z, sh_a B)] = E[1_A Ψ(Z)]`, `Ψ(z) = ∫ Φ(z,w) Wiener(dw)`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.lintegral_indicator_shift
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P)
    (a : ℝ≥0) {E : Type*} [MeasurableSpace E] {Z : Ω → E} (hZ : Measurable[bmFiltration B a] Z)
    {A : Set Ω} (hA : MeasurableSet[bmFiltration B a] A)
    {Φ : E → (ℝ≥0 → Fin d → ℝ) → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, A.indicator (fun ω => Φ (Z ω) (shiftPath B a ω)) ω ∂P =
      ∫⁻ ω, A.indicator (fun ω => ∫⁻ w, Φ (Z ω) w ∂(wienerMeasure d)) ω ∂P := by
  have hφ : @Measurable (Ω × (ℝ≥0 → Fin d → ℝ)) ℝ≥0∞
      (@Prod.instMeasurableSpace Ω _ (bmFiltration B a) _) _
      (Function.uncurry fun ω w => A.indicator (fun ω => Φ (Z ω) w) ω) := by
    let _ : MeasurableSpace Ω := bmFiltration B a
    have e : (Function.uncurry fun ω w => A.indicator (fun ω => Φ (Z ω) w) ω) =
        (A ×ˢ (Set.univ : Set (ℝ≥0 → Fin d → ℝ))).indicator
          (fun z : Ω × (ℝ≥0 → Fin d → ℝ) => Φ (Z z.1) z.2) := by
      funext ⟨ω, w⟩
      by_cases h : ω ∈ A <;> simp [h, Function.uncurry]
    rw [e]
    refine Measurable.indicator ?_ (hA.prod MeasurableSet.univ)
    exact hΦ.comp (hZ.comp measurable_fst |>.prodMk measurable_snd)
  have := hB.lintegral_shift_freeze a hφ
  refine (lintegral_congr fun ω => ?_).trans (this.trans (lintegral_congr fun ω => ?_))
  · by_cases h : ω ∈ A <;> simp [h]
  · by_cases h : ω ∈ A <;> simp [h]

end Markov

end ElboimSly.Brownian
