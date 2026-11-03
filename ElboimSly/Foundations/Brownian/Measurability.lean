/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Law
public import ElboimSly.Foundations.Brownian.PathDense
import Mathlib

/-!
# Measurability of path functionals

Measurability of path functionals (d)-(i); (a)-(c) are in `PathDense.lean`.

Infima, suprema, moduli of continuity, hitting events and counts of a standard Brownian motion are
measurable. They are of the form `Γ ∘ pathMap B` for a measurable functional `Γ` on the path space
`ℝ≥0 → Fin d → ℝ` given by the same formulas with `denseSub J` in place of `J` (part (h)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The path space `W_d = ℝ≥0 → Fin d → ℝ` (with its product `σ`-algebra). -/
abbrev PathSpace (d : ℕ) := ℝ≥0 → Fin d → ℝ

/-! ### Path-space functionals (part (h)) -/

/-- `Γ(w) = inf_{t ∈ J'} G(w(t))`. -/
noncomputable def pathInf (J : Set ℝ≥0) (G : (Fin d → ℝ) → ℝ) (w : PathSpace d) : EReal :=
  ⨅ t ∈ denseSub J, (G (w t) : EReal)

/-- The path set `𝔄 = {w : inf_{t ∈ J'} ‖w(t) - x‖ ≤ r}`. -/
def pathHit (J : Set ℝ≥0) (x : Fin d → ℝ) (r : ℝ) : Set (PathSpace d) :=
  {w | ⨅ t ∈ denseSub J, ((‖w t - x‖ : ℝ) : EReal) ≤ (r : EReal)}

/-- The count `#{i ∈ ℕ : y + σ w(i) ∈ D}` with values in `ℕ ∪ {∞} ⊆ [0,∞]`. -/
noncomputable def pathCount (y : Fin d → ℝ) (σ : ℝ) (D : Set (Fin d → ℝ)) (w : PathSpace d) : ℝ≥0∞ :=
  ∑' i : ℕ, {w : PathSpace d | y + σ • w i ∈ D}.indicator 1 w

/-- Measurability of path functionals (h): the general countable-infimum functional on
`ℝ^m × W_d` is measurable. -/
theorem measurable_biInf_path {m : ℕ} {J'' : Set ℝ≥0} (hJ : J''.Countable)
    {Γ₀ : (Fin m → ℝ) × (Fin d → ℝ) → ℝ} (hΓ : Continuous Γ₀) :
    Measurable fun p : (Fin m → ℝ) × PathSpace d => ⨅ u ∈ J'', (Γ₀ (p.1, p.2 u) : EReal) := by
  refine Measurable.biInf J'' hJ fun u _ => ?_
  exact measurable_coe_real_ereal.comp
    (hΓ.measurable.comp (measurable_fst.prodMk ((measurable_pi_apply u).comp measurable_snd)))

theorem measurable_pathInf (J : Set ℝ≥0) {G : (Fin d → ℝ) → ℝ} (hG : Continuous G) :
    Measurable (pathInf J G) := by
  refine Measurable.biInf _ (denseSub_countable J) fun u _ => ?_
  exact measurable_coe_real_ereal.comp (hG.measurable.comp (measurable_pi_apply u))

theorem measurableSet_pathHit (J : Set ℝ≥0) (x : Fin d → ℝ) (r : ℝ) :
    MeasurableSet (pathHit J x r) := by
  have : Measurable (pathInf J (fun z : Fin d → ℝ => ‖z - x‖)) :=
    measurable_pathInf J (continuous_norm.comp (continuous_id.sub continuous_const))
  exact measurableSet_le this measurable_const

theorem measurable_pathCount (y : Fin d → ℝ) (σ : ℝ) {D : Set (Fin d → ℝ)} (hD : MeasurableSet D) :
    Measurable (pathCount y σ D) := by
  refine Measurable.tsum fun i => ?_
  refine measurable_one.indicator ?_
  have : Measurable fun w : PathSpace d => y + σ • w i := by fun_prop
  exact this hD

/-! ### The path functionals of a Brownian motion (parts (d)-(g)) -/

section BM

variable {B : ℝ≥0 → Ω → (Fin d → ℝ)}

lemma continuous_path (hB : IsStandardBrownianMotion d B P) (ω : Ω) : Continuous (pathMap B ω) :=
  continuous_pi fun i => (continuous_apply i).comp (hB.continuous_zero ω).1

/-- Measurability of path functionals (f), hitting a ball in a compact interval. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.measurableSet_exists_mem {J : Set ℝ≥0}
    (hB : IsStandardBrownianMotion d B P) (hJ : J.OrdConnected) (hc : IsCompact J)
    (hne : J.Nonempty) (x : Fin d → ℝ) (r : ℝ) :
    MeasurableSet {ω | ∃ t ∈ J, ‖B t ω - x‖ ≤ r} := by
  have : {ω | ∃ t ∈ J, ‖B t ω - x‖ ≤ r} = pathMap B ⁻¹' pathHit J x r := by
    ext ω
    exact exists_mem_le_iff_iInf_le hJ hc hne (continuous_path hB ω) x r
  rw [this]
  exact hB.measurable_pathMap (measurableSet_pathHit J x r)

/-- Measurability of path functionals (g), the count of visits at integer times. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.measurable_count
    (hB : IsStandardBrownianMotion d B P) (y : Fin d → ℝ) (σ : ℝ) {D : Set (Fin d → ℝ)}
    (hD : MeasurableSet D) :
    Measurable fun ω => ∑' i : ℕ, {ω | y + σ • B i ω ∈ D}.indicator (1 : Ω → ℝ≥0∞) ω := by
  have : (fun ω => ∑' i : ℕ, {ω | y + σ • B i ω ∈ D}.indicator (1 : Ω → ℝ≥0∞) ω) =
      pathCount y σ D ∘ pathMap B := rfl
  rw [this]
  exact (measurable_pathCount y σ hD).comp hB.measurable_pathMap

/-- Measurability of path functionals (i), joint measurability of `(s, ω) ↦ B(s, ω)`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.measurable_uncurry
    (hB : IsStandardBrownianMotion d B P) : Measurable (Function.uncurry B) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun ω => (hB.continuous_zero ω).1) hB.measurable

/-- Lebesgue measure on `[0,∞)`, the pullback of Lebesgue measure on `ℝ`. -/
noncomputable def nnLebesgue : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

lemma nnLebesgue_Icc (t : ℝ≥0) : nnLebesgue (Set.Icc 0 t) = t := by
  unfold nnLebesgue
  rw [Measure.comap_apply _ NNReal.coe_injective (fun s hs =>
    hs.image_of_continuousOn_injOn NNReal.continuous_coe.continuousOn NNReal.coe_injective.injOn)
    _ measurableSet_Icc]
  have : ((↑) : ℝ≥0 → ℝ) '' Set.Icc 0 t = Set.Icc 0 (t : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      exact ⟨y.2, by exact_mod_cast hy⟩
    · rintro ⟨h0, h1⟩
      exact ⟨⟨x, h0⟩, ⟨bot_le, by exact_mod_cast h1⟩, rfl⟩
  rw [this, Real.volume_Icc]
  simp

/-- Measurability of path functionals (i), occupation times: for `S ⊆ [0,∞) × Ω` measurable,
`ω ↦ Leb {s ∈ [0,t] : (s,ω) ∈ S}` is measurable. -/
theorem measurable_occupation {S : Set (ℝ≥0 × Ω)} (hS : MeasurableSet S) (t : ℝ≥0) :
    Measurable fun ω => nnLebesgue {s ∈ Set.Icc (0 : ℝ≥0) t | (s, ω) ∈ S} := by
  have hS' : MeasurableSet (Prod.swap ⁻¹' S) := measurable_swap hS
  have : IsFiniteMeasure (nnLebesgue.restrict (Set.Icc (0 : ℝ≥0) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, nnLebesgue_Icc]; exact ENNReal.coe_lt_top⟩
  have := measurable_measure_prodMk_left
    (ν := nnLebesgue.restrict (Set.Icc (0 : ℝ≥0) t)) hS'
  convert this using 2 with ω
  rw [Measure.restrict_apply (measurable_prodMk_left hS')]
  congr 1
  ext s
  simp [and_comm]

end BM

end ElboimSly.Brownian
