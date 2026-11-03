/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Cor72
public import Mathlib

/-!
# Corollary 7.2 from Lemma 7.1

ES22 Corollary 7.2.

`StepLem71 d cCat βCat` is the conclusion of Lemma 7.1 (two lengths `s 0, s 1`, natural coupling
with `ℓ = 2`). `stepCor72_of_lem71` is the induction of the written proof: peel the first segment,
use Lemma 7.1 for `(s 0, S_ℓ - s 0)` and the induction hypothesis at offset `a + s 0`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.SRW
open scoped NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- The conclusion of ES22 Lemma 7.1 (isolated). -/
def StepLem71 (d : ℕ) (cCat : ℝ) (βCat : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βCat n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → PathSpace d),
      IsSRW P Y → (∀ ω, Y ω ∈ StepPath d) →
      ∀ (a : ℝ≥0) (s : ℕ → ℝ≥0), 0 < s 0 → 0 < s 1 →
        ((stepPartial s 2 : ℝ≥0) : ℝ) ≤ indScale t₀ n →
        P.real {ω | ∃ u : ℝ≥0, u ≤ stepPartial s 2 ∧
          indScale t₀ n ^ (2 * heavyEps d) ≤
            ‖stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s 2 (Y ω) u‖} ≤
          Real.exp (-(cCat * (n : ℝ) ^ 3))

theorem stepPartial_succ' (s : ℕ → ℝ≥0) (j : ℕ) :
    stepPartial s (j + 1) = s 0 + stepPartial (fun i => s (i + 1)) j := by
  simp only [stepPartial]
  rw [Finset.sum_range_succ' s j, add_comm]

theorem stepCatList_cons_of_ne_nil {V : Type*} [Add V] [Zero V] (p : ℝ≥0 × (ℝ≥0 → V))
    {l : List (ℝ≥0 × (ℝ≥0 → V))} (hl : l ≠ []) :
    stepCatList (p :: l) = stepCat p.1 p.2 (stepCatList l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons q rest => rfl

/-- Peeling the first segment of the natural coupling. -/
theorem stepNatTilde_succ (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (k : ℕ) (Y : ℝ≥0 → Fin d → ℤ) :
    stepNatTilde β a s (k + 2) Y =
      stepCat (s 0) (stepReg β (stepShift a Y))
        (stepNatTilde β (a + s 0) (fun i => s (i + 1)) (k + 1) Y) := by
  have hZ : ∀ j, stepWalkZ β a s Y (j + 1) =
      stepWalkZ β (a + s 0) (fun i => s (i + 1)) Y j := by
    intro j
    simp only [stepWalkZ, stepPartial_succ', add_assoc]
  simp only [stepNatTilde]
  have hr : List.range (k + 2) = 0 :: (List.range (k + 1)).map Nat.succ :=
    List.range_succ_eq_map
  rw [hr, List.map_cons, List.map_map, stepCatList_cons_of_ne_nil _ (by simp)]
  simp only [Function.comp_def, hZ, stepWalkZ_zero]

theorem stepNatTilde_two (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (Y : ℝ≥0 → Fin d → ℤ) :
    stepNatTilde β a s 2 Y = stepCat (s 0) (stepReg β (stepShift a Y))
      (stepReg β (stepShift (a + s 0) Y)) := by
  have := stepNatTilde_succ β a s 0 Y
  rw [this, stepNatTilde_one]

/-- **ES22 Corollary 7.2** from **ES22 Lemma 7.1**. -/
theorem stepCor72_of_lem71 {cCat : ℝ} {βCat : ℕ → ℝ} (h : StepLem71 d cCat βCat) :
    StepCor72 d cCat βCat := by
  intro n₁ hn₁ β _ n t₀ hβ hreg Ω _ P Y hY hYp
  have := hY.isProbabilityMeasure
  set K : ℝ := indScale t₀ n ^ (2 * heavyEps d) with hK
  set q : ℝ := Real.exp (-(cCat * (n : ℝ) ^ 3)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hscale : 0 < indScale t₀ n := by
    have := hreg.2.2.2.1
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    unfold indScale; exact mul_pos h4 (by linarith [this.1])
  have hK0 : 0 < K := Real.rpow_pos_of_pos hscale _
  -- the induction, generalised over the offset and the lengths
  suffices H : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ (a : ℝ≥0) (s : ℕ → ℝ≥0), (∀ j, 0 < s j) →
      ((stepPartial s ℓ : ℝ≥0) : ℝ) ≤ indScale t₀ n →
      P.real {ω | ∃ u : ℝ≥0, u ≤ stepPartial s ℓ ∧
        (ℓ : ℝ) * K ≤
          ‖stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s ℓ (Y ω) u‖} ≤
        ((ℓ : ℝ) - 1) * q from
    fun a ℓ s hℓ hs hle => H ℓ hℓ a s hs hle
  intro ℓ hℓ
  induction ℓ, hℓ using Nat.le_induction with
  | base =>
    intro a s _ _
    have : {ω | ∃ u : ℝ≥0, u ≤ stepPartial s 1 ∧
        ((1 : ℕ) : ℝ) * K ≤
          ‖stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s 1 (Y ω) u‖} = ∅ := by
      ext ω
      simp [stepNatTilde_one, hK0]
    rw [this]
    simp
  | succ ℓ hℓ ih =>
    intro a s hs hle
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    set s' : ℕ → ℝ≥0 := fun i => if i = 0 then s 0 else if i = 1 then
        stepPartial (fun i => s (i + 1)) (k + 1) else 1 with hs'
    have hsum : stepPartial s (k + 1 + 1) = s 0 + stepPartial (fun i => s (i + 1)) (k + 1) :=
      stepPartial_succ' s (k + 1)
    have hpos : 0 < stepPartial (fun i => s (i + 1)) (k + 1) := by
      simp only [stepPartial]
      refine Finset.sum_pos (fun i _ => hs _) ⟨0, by simp⟩
    have hs'2 : stepPartial s' 2 = stepPartial s (k + 1 + 1) := by
      rw [hsum]
      show ∑ i ∈ Finset.range 2, s' i = _
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [hs']
    have hpartle : stepPartial (fun i => s (i + 1)) (k + 1) ≤ stepPartial s (k + 1 + 1) := by
      rw [hsum]; exact le_add_self
    have hrealle : ((stepPartial (fun i => s (i + 1)) (k + 1) : ℝ≥0) : ℝ) ≤ indScale t₀ n :=
      le_trans (by exact_mod_cast hpartle) hle
    have h71 := h n₁ hn₁ β n t₀ hβ hreg Ω P Y hY hYp a s' (by simpa [hs'] using hs 0)
      (by simpa [hs'] using hpos) (by rw [hs'2]; exact hle)
    have hIH := ih (a + s 0) (fun i => s (i + 1)) (fun j => hs _) hrealle
    -- the inclusion
    have hsub : {ω | ∃ u : ℝ≥0, u ≤ stepPartial s (k + 1 + 1) ∧
        ((k + 1 + 1 : ℕ) : ℝ) * K ≤
          ‖stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s (k + 1 + 1) (Y ω) u‖} ⊆
        {ω | ∃ u : ℝ≥0, u ≤ stepPartial s' 2 ∧
          K ≤ ‖stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s' 2 (Y ω) u‖} ∪
        {ω | ∃ u : ℝ≥0, u ≤ stepPartial (fun i => s (i + 1)) (k + 1) ∧
          ((k + 1 : ℕ) : ℝ) * K ≤
            ‖stepReg β (stepShift (a + s 0) (Y ω)) u -
              stepNatTilde β (a + s 0) (fun i => s (i + 1)) (k + 1) (Y ω) u‖} := by
      rintro ω ⟨u, hu, hnorm⟩
      by_cases hu0 : u ≤ s 0
      · exfalso
        rw [stepNatTilde_succ, stepCat_of_le _ _ hu0, sub_self, norm_zero] at hnorm
        have : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) * K := by positivity
        linarith
      · have hu1 : s 0 < u := not_le.1 hu0
        set v := u - s 0 with hv
        have hv' : v ≤ stepPartial (fun i => s (i + 1)) (k + 1) := by
          rw [hv, tsub_le_iff_left]; rw [hsum] at hu; exact hu
        have e1 : stepNatTilde β a s (k + 1 + 1) (Y ω) u =
            stepReg β (stepShift a (Y ω)) (s 0) +
              stepNatTilde β (a + s 0) (fun i => s (i + 1)) (k + 1) (Y ω) v := by
          rw [stepNatTilde_succ, stepCat_of_gt _ _ hu1]
        have e2 : stepNatTilde β a s' 2 (Y ω) u =
            stepReg β (stepShift a (Y ω)) (s 0) +
              stepReg β (stepShift (a + s 0) (Y ω)) v := by
          have hs0 : s' 0 = s 0 := by simp [hs']
          rw [stepNatTilde_two, hs0, stepCat_of_gt _ _ hu1]
        by_contra hcon
        simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_le] at hcon
        obtain ⟨hc1, hc2⟩ := hcon
        have h1 := hc1 u (hs'2 ▸ hu)
        have h2 := hc2 v hv'
        have e3 : stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s (k + 1 + 1) (Y ω) u =
            (stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s' 2 (Y ω) u) +
              (stepReg β (stepShift (a + s 0) (Y ω)) v -
                stepNatTilde β (a + s 0) (fun i => s (i + 1)) (k + 1) (Y ω) v) := by
          rw [e1, e2]; abel
        rw [e3] at hnorm
        have := norm_add_le (stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s' 2 (Y ω) u)
          (stepReg β (stepShift (a + s 0) (Y ω)) v -
            stepNatTilde β (a + s 0) (fun i => s (i + 1)) (k + 1) (Y ω) v)
        push_cast at hnorm h2
        nlinarith
    calc P.real _ ≤ P.real (_ ∪ _) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ q + ((((k + 1 : ℕ) : ℝ)) - 1) * q := add_le_add h71 hIH
      _ = _ := by push_cast; ring

end ElboimSly.Paper.Step
