/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.HitThm
public import ElboimSly.Foundations.SRW.Freeze
public import Mathlib

/-!
# Avoiding finitely many balls after a stopping time

Avoiding finitely many boxes after a stopping time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω} {T : Ω → WithTop ℝ≥0}

/-- The "bad" set of parameters and paths: some ball `B(z_l, ρ)`, `1 ≤ l ≤ M`, is visited at a
time `s ≥ a`. -/
def hitSet {M : ℕ} (ρ : ℝ) (a : ℝ≥0) : Set ((Fin (M + 1) → Fin d → ℤ) × PathSpace d) :=
  {p | ∃ s : ℝ≥0, a ≤ s ∧ ∃ l : Fin (M + 1), 1 ≤ l.val ∧
    ‖fun i => ((p.1 0 i + p.2 s i - p.1 l i : ℤ) : ℝ)‖ ≤ ρ}

theorem isVersion_hitSet {M : ℕ} (ρ : ℝ) (a : ℝ≥0) :
    ∃ V : Set ((Fin (M + 1) → Fin d → ℤ) × PathSpace d), MeasurableSet V ∧
      ∀ z γ, IsRegularPath γ → ((z, γ) ∈ hitSet (d := d) ρ a ↔ (z, γ) ∈ V) := by
  have h := isVersion_exists_Ici (E := Fin (M + 1) → Fin d → ℤ) (d := d)
    (α := fun _ => a)
    (K := {p : (Fin (M + 1) → Fin d → ℤ) × (Fin d → ℤ) | ∃ l : Fin (M + 1), 1 ≤ l.val ∧
      ‖fun i => ((p.1 0 i + p.2 i - p.1 l i : ℤ) : ℝ)‖ ≤ ρ}) measurable_const
    (MeasurableSet.of_discrete)
  exact ⟨_, h.1, fun z γ hγ => by
    have := h.2 z γ hγ
    simpa [hitSet] using this⟩

/-- Avoiding finitely many boxes after a stopping time. -/
theorem avoid_balls (hZ : IsSRW P Z) (hF : IsAdmissible P Z F)
    (hT : IsStoppingTime hF.filtration T) (hd : 3 ≤ d) (M : ℕ)
    {ξ : Ω → Fin (M + 1) → Fin d → ℤ} (hξ : Measurable[hT.measurableSpace] ξ) {ρ : ℝ}
    (hρ : 1 ≤ ρ) {a : ℝ≥0} (ha : 0 < a) {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) :
    P (A ∩ {ω | T ω < ⊤} ∩ {ω | ∃ s : ℝ≥0, a ≤ s ∧ ∃ l : Fin (M + 1), 1 ≤ l.val ∧
        ‖fun i => ((ξ ω 0 i + thetaAt T Z ω s i - ξ ω l i : ℤ) : ℝ)‖ ≤ ρ}) ≤
      ENNReal.ofReal (M * Chit d * (ρ / √(a : ℝ)) ^ (d - 2)) * P (A ∩ {ω | T ω < ⊤}) := by
  have := hZ.isProbabilityMeasure
  obtain ⟨V, hVm, hV⟩ := isVersion_hitSet (d := d) (M := M) ρ a
  have hp : ∀ z ∈ (Set.univ : Set (Fin (M + 1) → Fin d → ℤ)),
      P.map Z (Prod.mk z ⁻¹' V) ≤ ENNReal.ofReal (M * Chit d * (ρ / √(a : ℝ)) ^ (d - 2)) := by
    intro z _
    rw [Measure.map_apply hZ.1 (measurable_prodMk_left hVm)]
    have hsub : Z ⁻¹' (Prod.mk z ⁻¹' V) ⊆ ⋃ l ∈ (Finset.univ.filter
        fun l : Fin (M + 1) => 1 ≤ l.val),
        {ω | ∃ s : ℝ≥0, a ≤ s ∧ ‖fun i => ((z 0 i + Z ω s i - z l i : ℤ) : ℝ)‖ ≤ ρ} := by
      intro ω hω
      have hω' : (z, Z ω) ∈ V := hω
      rw [← hV z (Z ω) (hZ.2.1 ω)] at hω'
      obtain ⟨s, hs, l, hl, hn⟩ := hω'
      exact mem_iUnion₂.2 ⟨l, by simpa using hl, s, hs, hn⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    have hl : ∀ l ∈ Finset.univ.filter (fun l : Fin (M + 1) => 1 ≤ l.val),
        P {ω | ∃ s : ℝ≥0, a ≤ s ∧ ‖fun i => ((z 0 i + Z ω s i - z l i : ℤ) : ℝ)‖ ≤ ρ} ≤
          ENNReal.ofReal (Chit d * (ρ / √(a : ℝ)) ^ (d - 2)) := by
      intro l _
      have := hit hZ hd (z 0) (z l) hρ ha
      rw [measureReal_def] at this
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by
        have : 0 ≤ Chit d := by unfold Chit; have := kappa_ge (show 1 ≤ d by omega); positivity
        positivity)).2 this
    refine (Finset.sum_le_sum hl).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun l : Fin (M + 1) => 1 ≤ l.val)).card = M := by
      have : Finset.univ.filter (fun l : Fin (M + 1) => 1 ≤ l.val) = Finset.univ.erase 0 := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
          and_true]
        rw [Fin.ext_iff]
        simp only [Fin.val_zero]
        omega
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      simp
    rw [hcard, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hfr := hZ.freeze_param_le hF hT (E := Fin (M + 1) → Fin d → ℤ) hξ hA hVm
    (C := Set.univ) MeasurableSet.univ hp
  refine le_trans (measure_mono ?_) (le_trans hfr (by simp))
  intro ω ⟨⟨hA', hT'⟩, hex⟩
  refine ⟨⟨⟨hA', hT'⟩, mem_univ _⟩, ?_⟩
  obtain ⟨s, hs, l, hl, hn⟩ := hex
  show (ξ ω, thetaAt T Z ω) ∈ V
  rw [← hV _ _ (isRegularPath_thetaAt hZ.2.1 T ω)]
  exact ⟨s, hs, l, hl, hn⟩

end SRW
end ElboimSly
