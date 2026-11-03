/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Lemma82E
public import ElboimSly.Foundations.SRW.StoppedPosition
public import Mathlib

/-!
# The SRW content of Lemma 8.2: part (e), the consequence

SRW content of Lemma 8.2 (e).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem Chit_nonneg (hd : 1 ≤ d) : 0 ≤ Chit d := by
  unfold Chit
  have := kappa_ge hd
  positivity

/-- The threshold `n₂(d)` of SRW content of Lemma 8.2 (e). -/
noncomputable def lem82n2 (d : ℕ) : ℕ :=
  max 4 (if h : 5 ≤ d then Classical.choose (lemma82_n2 h (Chit_nonneg (by omega))) else 0)

theorem four_le_lem82n2 (d : ℕ) : 4 ≤ lem82n2 d := le_max_left _ _

theorem lem82n2_spec (hd : 5 ≤ d) {n : ℕ} (hn : lem82n2 d ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀)
    (ht4 : t₀ ≤ 4) :
    (lem82T n t₀ / (3.6 : ℝ) ^ n + 2) * Chit d *
        (1.9 ^ (n + 2) / √((3.89 : ℝ) ^ n)) ^ (d - 2) ≤ 1 / 2 := by
  have h := Classical.choose_spec (lemma82_n2 hd (Chit_nonneg (by omega)))
  unfold lem82n2 at hn
  rw [dite_eq_left hd] at hn
  exact h n (le_trans (le_max_right _ _) hn) t₀ ht1 ht4

theorem measurable_add_discrete {α : Type*} {m : MeasurableSpace α} {f g : α → Fin d → ℤ}
    (hf : Measurable[m] f) (hg : Measurable[m] g) : Measurable[m] (fun a => f a + g a) :=
  (measurable_of_countable (fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 + p.2)).comp (hf.prodMk hg)

/-- SRW content of Lemma 8.2 (e): the consequence. -/
theorem lemma82_e {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → PathSpace d}
    {F : ℝ≥0 → MeasurableSpace Ω} (hX : IsSRW P X) (hF : IsAdmissible P X F) (hd : 5 ≤ d)
    {n : ℕ} (hn : lem82n2 d ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    {ζ : Ω → WithTop ℝ≥0} (hζ : IsStoppingTime hF.filtration ζ)
    (Y₀ : Ω → PathSpace d) (hY₀ : Measurable[F 0] Y₀) (x₀ : Ω → Fin d → ℤ)
    (hx₀ : Measurable[F 0] x₀) (C₀ : Set Ω)
    (hcov : ∀ ω ∈ C₀, ∀ s s' : ℝ≥0, s ≤ s' → s' ≤ (lem82T n t₀).toNNReal →
      s' - s ≤ lem82h n → ‖Y₀ ω s' - Y₀ ω s‖ ≤ 1.9 ^ n)
    {A : Set Ω} (hA : MeasurableSet[hζ.measurableSpace] A) (hAC : A ⊆ C₀) :
    P (A ∩ {ω | ζ ω < ⊤} ∩ {ω | ∃ s : ℝ≥0, (3.89 : ℝ) ^ n ≤ s ∧
        ∃ s' : ℝ≥0, s' ≤ (lem82T n t₀).toNNReal ∧
          ‖x₀ ω + X ω (stopReal ζ ω + s) - Y₀ ω s'‖ ≤ 1.9 ^ (n + 1)}) ≤
      ENNReal.ofReal (1 / 2) * P (A ∩ {ω | ζ ω < ⊤}) := by
  classical
  have := hX.isProbabilityMeasure
  have hd1 : 1 ≤ d := by omega
  set Tn : ℝ≥0 := (lem82T n t₀).toNNReal with hTn
  have hn4 : 4 ≤ n := le_trans (four_le_lem82n2 d) hn
  have hTpos := lem82T_pos hn4 ht1
  have hTc : (Tn : ℝ) = lem82T n t₀ := Real.coe_toNNReal _ hTpos.le
  set M : ℕ := ⌈(Tn : ℝ) / lem82h n⌉₊ + 1 with hM
  set a : ℝ≥0 := ((3.89 : ℝ) ^ n).toNNReal with ha
  have hac : (a : ℝ) = (3.89 : ℝ) ^ n := Real.coe_toNNReal _ (by positivity)
  have ha0 : 0 < a := by
    have : (0 : ℝ) < a := by rw [hac]; positivity
    exact_mod_cast this
  set ρ : ℝ := (1.9 : ℝ) ^ (n + 2) with hρ
  have hρ1 : 1 ≤ ρ := one_le_pow₀ (by norm_num)
  -- the parameters
  set ξ : Ω → Fin (M + 1) → Fin d → ℤ := fun ω l =>
    if l.val = 0 then x₀ ω + (if ζ ω = ⊤ then 0 else X ω (stopReal ζ ω))
    else Y₀ ω (lem82g n Tn (l.val - 1)) with hξ
  have hF0 : F 0 ≤ hζ.measurableSpace := by
    have := hζ.le_measurableSpace_of_const_le (i := 0) (fun ω => bot_le)
    exact this
  have hξm : Measurable[hζ.measurableSpace] ξ := by
    refine (@measurable_pi_iff Ω (Fin (M + 1)) (fun _ => Fin d → ℤ) hζ.measurableSpace _ _).2
      fun l => ?_
    by_cases hl : l.val = 0
    · have hl' : l = 0 := Fin.ext hl
      have h1 : Measurable[hζ.measurableSpace] x₀ := hx₀.mono hF0 le_rfl
      have h2 := hF.measurable_stopped_position hX.2.1 hζ
      have := measurable_add_discrete h1 h2
      have e : (fun ω => ξ ω l) = fun ω => x₀ ω + (if ζ ω = ⊤ then (0 : Fin d → ℤ)
          else X ω (stopReal ζ ω)) := by
        funext ω; simp [hξ, hl']
      rw [e]; exact this
    · have hl' : l ≠ 0 := fun h => hl (by simp [h])
      have h1 : Measurable[F 0] (fun ω => Y₀ ω (lem82g n Tn (l.val - 1))) :=
        (measurable_pi_apply _).comp hY₀
      have := h1.mono hF0 le_rfl
      have e : (fun ω => ξ ω l) = fun ω => Y₀ ω (lem82g n Tn (l.val - 1)) := by
        funext ω; simp [hξ, hl']
      rw [e]; exact this
  have hav := avoid_balls hX hF hζ (by omega) (M := M) hξm (ρ := ρ) hρ1 ha0 hA
  -- the numerical bound
  have hnum : (M : ℝ) * Chit d * (ρ / √(a : ℝ)) ^ (d - 2) ≤ 1 / 2 := by
    have hspec := lem82n2_spec hd hn ht1 ht4
    have hh : (0 : ℝ) < lem82h n := by rw [coe_lem82h]; positivity
    have hMle : (M : ℝ) ≤ lem82T n t₀ / (3.6 : ℝ) ^ n + 2 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ (Tn : ℝ) / lem82h n by positivity)
      have hrew : (Tn : ℝ) / lem82h n = lem82T n t₀ / (3.6 : ℝ) ^ n := by
        rw [hTc, coe_lem82h]
      rw [hrew] at this
      rw [hM]; push_cast; rw [hrew]; linarith
    have hCn := Chit_nonneg hd1
    have e : ρ / √(a : ℝ) = 1.9 ^ (n + 2) / √((3.89 : ℝ) ^ n) := by rw [hac]
    rw [e]
    refine le_trans ?_ hspec
    gcongr
  have hsub : A ∩ {ω | ζ ω < ⊤} ∩ {ω | ∃ s : ℝ≥0, (3.89 : ℝ) ^ n ≤ s ∧
        ∃ s' : ℝ≥0, s' ≤ Tn ∧ ‖x₀ ω + X ω (stopReal ζ ω + s) - Y₀ ω s'‖ ≤ 1.9 ^ (n + 1)} ⊆
      A ∩ {ω | ζ ω < ⊤} ∩ {ω | ∃ s : ℝ≥0, a ≤ s ∧ ∃ l : Fin (M + 1), 1 ≤ l.val ∧
        ‖fun i => ((ξ ω 0 i + thetaAt ζ X ω s i - ξ ω l i : ℤ) : ℝ)‖ ≤ ρ} := by
    rintro ω ⟨⟨hωA, hζlt⟩, s, hs, s', hs'T, hnorm⟩
    refine ⟨⟨hωA, hζlt⟩, s, ?_, ?_⟩
    · rw [ha]; exact Real.toNNReal_le_iff_le_coe.2 hs
    have hωC := hAC hωA
    obtain ⟨l, hlT, hlnorm⟩ := lemma82_d (n := n) (T := Tn) (Y₀ ω) (hcov ω hωC)
      (z := x₀ ω + X ω (stopReal ζ ω + s)) ⟨s', hs'T, hnorm⟩
    have hlM : l + 1 < M + 1 := by rw [hM]; omega
    refine ⟨⟨l + 1, hlM⟩, by simp, ?_⟩
    have hne : ζ ω ≠ ⊤ := ne_of_lt hζlt
    have e : (fun i => ((ξ ω 0 i + thetaAt ζ X ω s i - ξ ω ⟨l + 1, hlM⟩ i : ℤ) : ℝ)) =
        fun i => (((x₀ ω + X ω (stopReal ζ ω + s) - Y₀ ω (lem82g n Tn l)) i : ℤ) : ℝ) := by
      funext i
      simp only [hξ, thetaAt, hne, ite_false, theta, Pi.add_apply, Pi.sub_apply]
      simp
    rw [e, norm_cast_vec]
    exact hlnorm.trans (le_of_eq hρ.symm)
  refine (measure_mono hsub).trans (hav.trans ?_)
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hnum) _

end SRW
end ElboimSly
