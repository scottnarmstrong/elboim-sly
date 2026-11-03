/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Times
public import ElboimSly.Paper.Step.Lemma78Cover

/-!
# Ordering of the times of Lemma 7.8 and the covering of `𝔓_n`

Measurability (ordering `ζ_i ≤ ζ'_i ≤ ζ_{i+1} ≤ t'_n`) and covering fP_n
(ES22 §7), applied to the path-level times of `Step78Data`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*}

namespace Step78Data

variable (D : Step78Data d Ω) (ω : Ω)

theorem nextZeta_le_T (R : Ω → WithTop ℝ≥0) : D.nextZeta R ω ≤ (D.T : WithTop ℝ≥0) :=
  min_le_left _ _

theorem zp_le_T (i : ℕ) : D.zp i ω ≤ (D.T : WithTop ℝ≥0) := by
  cases i with
  | zero => exact bot_le
  | succ i =>
    exact max_le (D.nextZeta_le_T ω _) (min_le_left _ _)

theorem zeta_le_T (i : ℕ) : D.zeta i ω ≤ (D.T : WithTop ℝ≥0) := by
  cases i with
  | zero => exact bot_le
  | succ i => exact D.nextZeta_le_T ω _

theorem zeta_le_zp (i : ℕ) : D.zeta i ω ≤ D.zp i ω := by
  cases i with
  | zero => exact le_rfl
  | succ i => exact le_max_left _ _

theorem zp_le_zeta_succ (i : ℕ) : D.zp i ω ≤ D.zeta (i + 1) ω :=
  le_min (D.zp_le_T ω i) (le_iInf₂ fun _r hr => hr.2)

theorem zp_succ_eq (i : ℕ) :
    D.zp (i + 1) ω = max (D.zeta (i + 1) ω)
      (min (D.T : WithTop ℝ≥0) (D.zetaPP (D.zeta (i + 1)) ω)) := rfl

/-- Between `ζ_i + 3.89^n` and `ζ'_i` the path is not within `1.9^n` of `V`. -/
theorem not_mem_nearSet2 {i : ℕ} {r : ℝ≥0} (h1 : D.zeta (i + 1) ω + (D.gap : WithTop ℝ≥0) ≤ r)
    (h2 : (r : WithTop ℝ≥0) < D.zp (i + 1) ω) : (r : ℝ) ∉ D.nearSet2 ω := by
  intro hr
  rw [zp_succ_eq] at h2
  have hz : D.zeta (i + 1) ω ≤ r := le_trans le_self_add h1
  have h3 : (r : WithTop ℝ≥0) < min (D.T : WithTop ℝ≥0) (D.zetaPP (D.zeta (i + 1)) ω) :=
    lt_of_not_ge fun hh => absurd (max_le hz hh) (not_le.2 h2)
  have h4 : (r : WithTop ℝ≥0) < D.zetaPP (D.zeta (i + 1)) ω := lt_of_lt_of_le h3 (min_le_right _ _)
  have h5 : step78FirstGe D.nearSet2 (fun ω => D.zeta (i + 1) ω + (D.gap : WithTop ℝ≥0)) ω ≤ r :=
    iInf₂_le r ⟨hr, h1⟩
  have h6 : D.zetaPP (D.zeta (i + 1)) ω ≤ r :=
    le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) h5
  exact absurd h4 (not_lt.2 h6)

/-- The real value of a `WithTop ℝ≥0` time. -/
noncomputable def toR (x : WithTop ℝ≥0) : ℝ := ((x.untopD 0 : ℝ≥0) : ℝ)

theorem toR_coe (a : ℝ≥0) : toR (a : WithTop ℝ≥0) = a := rfl

theorem coe_untopD_of_le {x : WithTop ℝ≥0} {T : ℝ≥0} (h : x ≤ (T : WithTop ℝ≥0)) :
    x = ((x.untopD 0 : ℝ≥0) : WithTop ℝ≥0) := by
  cases x with
  | top => exact absurd h (WithTop.not_top_le_coe _)
  | coe a => rfl

theorem toR_mono {x y : WithTop ℝ≥0} {T : ℝ≥0} (hy : y ≤ (T : WithTop ℝ≥0)) (h : x ≤ y) :
    toR x ≤ toR y := by
  have hx : x ≤ (T : WithTop ℝ≥0) := h.trans hy
  cases x with
  | top => exact absurd hx (WithTop.not_top_le_coe _)
  | coe a =>
    cases y with
    | top => exact absurd hy (WithTop.not_top_le_coe _)
    | coe b =>
      show ((a : ℝ≥0) : ℝ) ≤ (b : ℝ≥0)
      exact_mod_cast WithTop.coe_le_coe.1 h

/-- **covering fP_n** at the path level. `W₁` is the first walk, `V = W₁([0,t'_n])`,
`J ≥ 1` with `ζ_J = t'_n`, and `𝔓_n` is the set of `s₂ ∈ [0,t'_n]` within `1.9^n` of `W₁([0,t'_n])`. -/
theorem cover_path {W1 : ℝ → Fin d → ℤ} {J : ℕ} (hJ : 1 ≤ J)
    (hzJ : D.zeta J ω = (D.T : WithTop ℝ≥0))
    (hV : D.V ω = W1 '' Icc 0 (D.T : ℝ)) :
    volume {s : ℝ | s ∈ Icc 0 (D.T : ℝ) ∧ ∃ s₁ ∈ Icc 0 (D.T : ℝ),
        ‖W1 s₁ - D.path ω s‖ ≤ (19 / 10 : ℝ) ^ D.n} ≤
      ENNReal.ofReal (∑ i ∈ Finset.Icc 1 J,
          (toR (D.zeta i ω) - toR (D.zp (i - 1) ω)) +
        ((J : ℝ) - 1) * (389 / 100 : ℝ) ^ D.n) := by
  have hT := fun i => D.zp_le_T ω i
  have hgap : (D.gap : ℝ) = (389 / 100 : ℝ) ^ D.n := by
    simp only [Step78Data.gap]
    exact Real.coe_toNNReal _ (by positivity)
  rw [← hgap]
  refine step78_cover (z := fun i => toR (D.zeta i ω)) (zp := fun i => toR (D.zp i ω))
    (T := (D.T : ℝ)) (D.gap.2) ?_ ?_ ?_ hJ ?_ ?_ ?_
  · rfl
  · exact fun i => toR_mono (D.zeta_le_T ω _) (D.zp_le_zeta_succ ω i)
  · exact fun i _ => toR_mono (D.zp_le_T ω _) (D.zeta_le_zp ω i)
  · simp only [hzJ, toR_coe]
  · intro s ⟨hs, _⟩
    exact hs
  · intro i hi _ r hr1 hr2 hrP
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hz0 : 0 ≤ toR (D.zeta (j + 1) ω) := NNReal.coe_nonneg _
    have hr0 : 0 ≤ r := by linarith [D.gap.2]
    set r' : ℝ≥0 := r.toNNReal with hr'
    have hrr : (r' : ℝ) = r := Real.coe_toNNReal _ hr0
    have hzfin := D.zeta_le_T ω (j + 1)
    have hpfin := D.zp_le_T ω (j + 1)
    have e1 : D.zeta (j + 1) ω = ((D.zeta (j + 1) ω).untopD 0 : ℝ≥0) := coe_untopD_of_le hzfin
    have e2 : D.zp (j + 1) ω = ((D.zp (j + 1) ω).untopD 0 : ℝ≥0) := coe_untopD_of_le hpfin
    refine D.not_mem_nearSet2 ω (i := j) (r := r') ?_ ?_ ?_
    · rw [e1, ← WithTop.coe_add, WithTop.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add, hrr]
      exact hr1
    · rw [e2, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe, hrr]
      exact hr2
    · obtain ⟨_, s₁, hs₁, hn⟩ := hrP
      refine ⟨W1 s₁, by rw [hV]; exact ⟨s₁, hs₁, rfl⟩, ?_⟩
      show ‖D.path ω (r' : ℝ) - W1 s₁‖ ≤ _
      rw [hrr, norm_sub_rev]
      exact hn

end Step78Data

end ElboimSly.Paper.Step

end
