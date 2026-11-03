/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Segment
import Mathlib

/-!
# ES22 Claim 5.7: staying in a box and visiting `B^-`

ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-.

Throughout, `L > 0` stands for `2^j`, so that `4^j = L²`, `4^{j-1} = L²/4`, `2^{j-6} = L/64`.
The first coordinate of ES22 is the coordinate `i0` and the second is `i1`, with `i0 ≠ i1`
(so `d ≥ 2`; ES22 uses `d = 5`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {d : ℕ}

/-- ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-. `c_57(d) = c_tube(d, 1024²)`. -/
noncomputable def c57 (d : ℕ) : ℝ := ctube d (1024 ^ 2)

/-- The displacement `g - p = (-2^{j-1}, -η, 0, …, 0)` along the segment. -/
noncomputable def c57Dg (i0 i1 : Fin d) (L η : ℝ) : Fin d → ℝ :=
  fun k => if k = i0 then -L / 2 else if k = i1 then -η else 0

/-- The starting point `p = u + (3·2^{j-2}, 2^{j-1} + η, 2^{j-1}, …)`. -/
noncomputable def c57P (i0 i1 : Fin d) (u : Fin d → ℝ) (L η : ℝ) : Fin d → ℝ :=
  fun k => u k + (if k = i0 then 3 * L / 4 else if k = i1 then L / 2 + η else L / 2)

/-- The first box `u + [2^{j-6}, 7·2^{j-3} - 2^{j-6}] × [2^{j-2} + 2^{j-6}, 3·2^{j-2} - 2^{j-6}]^{d-1}`. -/
def c57Box1 (i0 : Fin d) (u : Fin d → ℝ) (L : ℝ) : Set (Fin d → ℝ) :=
  {y | ∀ k, if k = i0 then u k + L / 64 ≤ y k ∧ y k ≤ u k + 7 * L / 8 - L / 64
    else u k + L / 4 + L / 64 ≤ y k ∧ y k ≤ u k + 3 * L / 4 - L / 64}

/-- The second box `u + [2^{j-6}, 2^{j-1} - 2^{j-6}] × [2^{j-6}, 2^j - 2^{j-6}]^{d-1}`. -/
def c57Box2 (i0 : Fin d) (u : Fin d → ℝ) (L : ℝ) : Set (Fin d → ℝ) :=
  {y | ∀ k, if k = i0 then u k + L / 64 ≤ y k ∧ y k ≤ u k + L / 2 - L / 64
    else u k + L / 64 ≤ y k ∧ y k ≤ u k + L - L / 64}

lemma coord_le_norm (y z : Fin d → ℝ) (k : Fin d) : |y k - z k| ≤ ‖y - z‖ := by
  have := norm_le_pi_norm (y - z) k
  simpa [Real.norm_eq_abs] using this

lemma norm_c57Dg {i0 i1 : Fin d} (_hne : i0 ≠ i1) {L η : ℝ} (hL : 0 < L) (hη0 : 0 ≤ η)
    (hη : η ≤ 3 * L / 16) : ‖c57Dg i0 i1 L η‖ = L / 2 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
    unfold c57Dg
    split_ifs
    · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · simp; positivity
  · have := norm_le_pi_norm (c57Dg i0 i1 L η) i0
    simp only [c57Dg, ite_true, Real.norm_eq_abs] at this
    rwa [neg_div, abs_neg, abs_of_pos (by positivity)] at this

/-- Points within `L/32` of a point of the segment from `p` to `g = p + Dg` lie in the first box. -/
lemma mem_box1 {i0 i1 : Fin d} (hne : i0 ≠ i1) {L η : ℝ} (hL : 0 < L) (hη0 : 0 ≤ η)
    (hη : η ≤ 3 * L / 16) (u : Fin d → ℝ) {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) {y : Fin d → ℝ}
    (hy : ‖y - (c57P i0 i1 u L η + c • c57Dg i0 i1 L η)‖ ≤ L / 32) : y ∈ c57Box1 i0 u L := by
  intro k
  have h := (abs_le.1 ((coord_le_norm y _ k).trans hy))
  simp only [c57P, c57Dg, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  split_ifs at h ⊢ with h1 h2
  · subst h1; constructor <;> nlinarith [hc.1, hc.2]
  · subst h2; constructor <;> nlinarith [hc.1, hc.2]
  · constructor <;> nlinarith [hc.1, hc.2]

/-- Points within `L/32` of `g = p + Dg` lie in the second box. -/
lemma mem_box2 {i0 i1 : Fin d} (_hne : i0 ≠ i1) {L η : ℝ} (hL : 0 < L) (_hη0 : 0 ≤ η)
    (_hη : η ≤ 3 * L / 16) (u : Fin d → ℝ) {y : Fin d → ℝ}
    (hy : ‖y - (c57P i0 i1 u L η + c57Dg i0 i1 L η)‖ ≤ L / 32) : y ∈ c57Box2 i0 u L := by
  intro k
  have h := (abs_le.1 ((coord_le_norm y _ k).trans hy))
  simp only [c57P, c57Dg, Pi.add_apply] at h
  split_ifs at h ⊢ with h1 h2
  · constructor <;> linarith [h.1, h.2]
  · constructor <;> linarith [h.1, h.2]
  · constructor <;> linarith [h.1, h.2]

/-- The time `T₂ = 4^j = L²` as a nonnegative real. -/
noncomputable def c57T2 (L : ℝ) : ℝ≥0 := (L ^ 2).toNNReal

/-- ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-. The path set `𝔖`, independent of `u` and of the
Brownian motion: `‖σ w(s) - φ(s)‖ ≤ L/32` for `s` in the countable dense subset of `[0, 4^j]`,
where `φ(s) = min(s/T₁, 1)(g - p)`, `T₁ = 4^{j-1} = L²/4`. -/
def c57Set (i0 i1 : Fin d) (σ L η : ℝ) : Set (PathSpace d) :=
  {w | ∀ s ∈ denseSub (Set.Icc (0 : ℝ≥0) (c57T2 L)),
    ‖σ • w s - min ((s : ℝ) / (L ^ 2 / 4)) 1 • c57Dg i0 i1 L η‖ ≤ L / 32}

section B

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-, the probability bound. -/
theorem c57_prob [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) {i0 i1 : Fin d}
    (hne : i0 ≠ i1) {σ L η : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hL : 0 < L) (hη0 : 0 ≤ η)
    (hη : η ≤ 3 * L / 16) :
    ENNReal.ofReal (c57 d) ≤ P {ω | pathMap B ω ∈ c57Set i0 i1 σ L η} := by
  have hρ : (0 : ℝ) < L / 32 := by positivity
  have hDg := norm_c57Dg hne hL hη0 hη
  have hres := segment_follow (K := 1024) hB (by norm_num) hσ1 hσ2 hρ (T₁ := L ^ 2 / 4)
    (T₂ := c57T2 L) (x := 0) (g := c57Dg i0 i1 L η) (by positivity) ?_ ?_ ?_ ?_
  · unfold c57
    refine le_trans hres (measure_mono ?_)
    intro ω hω s hs
    have hs2 : s ≤ c57T2 L := (denseSub_subset _ hs).2
    have := hω s hs2
    simpa [segPath, pathMap] using this
  · have : ((c57T2 L : ℝ≥0) : ℝ) = L ^ 2 := Real.coe_toNNReal _ (by positivity)
    rw [this]; nlinarith [sq_nonneg L]
  · rw [div_le_iff₀ (by norm_num)]
    nlinarith [sq_nonneg L]
  · have : ((c57T2 L : ℝ≥0) : ℝ) = L ^ 2 := Real.coe_toNNReal _ (by positivity)
    rw [this]; nlinarith [sq_nonneg L]
  · simp only [sub_zero]
    rw [hDg]; nlinarith

end B

/-- The box `u + [0, 7·2^{j-3}] × [2^{j-2}, 3·2^{j-2}]^{d-1}` of eq. (85). -/
def c57BigBox (i0 : Fin d) (u : Fin d → ℝ) (L : ℝ) : Set (Fin d → ℝ) :=
  {y | ∀ k, if k = i0 then u k ≤ y k ∧ y k ≤ u k + 7 * L / 8
    else u k + L / 4 ≤ y k ∧ y k ≤ u k + 3 * L / 4}

/-- The box `B^- = u + [0, 2^{j-1}) × [0, 2^j)^{d-1}`. -/
def c57Bminus (i0 : Fin d) (u : Fin d → ℝ) (L : ℝ) : Set (Fin d → ℝ) :=
  {y | ∀ k, if k = i0 then u k ≤ y k ∧ y k < u k + L / 2 else u k ≤ y k ∧ y k < u k + L}

/-- ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-, on the event `E = {B ∈ 𝔖}`: the Brownian path stays in the
first box up to time `4^j`, and is in the second box at time `4^{j-1}`. -/
theorem c57_on_event {i0 i1 : Fin d} (hne : i0 ≠ i1) {σ L η : ℝ} (hL : 0 < L) (hη0 : 0 ≤ η)
    (hη : η ≤ 3 * L / 16) {w : PathSpace d} (hw : Continuous w)
    (hmem : w ∈ c57Set i0 i1 σ L η) (u : Fin d → ℝ) :
    (∀ s : ℝ≥0, (s : ℝ) ≤ L ^ 2 → c57P i0 i1 u L η + σ • w s ∈ c57Box1 i0 u L) ∧
    c57P i0 i1 u L η + σ • w (L ^ 2 / 4).toNNReal ∈ c57Box2 i0 u L := by
  have hg : Continuous fun s : ℝ≥0 =>
      ‖σ • w s - min ((s : ℝ) / (L ^ 2 / 4)) 1 • c57Dg i0 i1 L η‖ := by
    have hc : Continuous fun s : ℝ≥0 => min ((s : ℝ) / (L ^ 2 / 4)) 1 :=
      (NNReal.continuous_coe.div_const _).min continuous_const
    exact ((hw.const_smul σ).sub (hc.smul continuous_const)).norm
  have hall := le_on_of_denseSub (J := Set.Icc (0 : ℝ≥0) (c57T2 L)) Set.ordConnected_Icc hg hmem
  have hT2 : ((c57T2 L : ℝ≥0) : ℝ) = L ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hT1 : (((L ^ 2 / 4).toNNReal : ℝ≥0) : ℝ) = L ^ 2 / 4 := Real.coe_toNNReal _ (by positivity)
  refine ⟨fun s hs => ?_, ?_⟩
  · have h1 := hall s ⟨zero_le, by rw [← NNReal.coe_le_coe, hT2]; exact hs⟩
    refine mem_box1 hne hL hη0 hη u (c := min ((s : ℝ) / (L ^ 2 / 4)) 1)
      ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩ ?_
    have e : c57P i0 i1 u L η + σ • w s - (c57P i0 i1 u L η +
        min ((s : ℝ) / (L ^ 2 / 4)) 1 • c57Dg i0 i1 L η) =
        σ • w s - min ((s : ℝ) / (L ^ 2 / 4)) 1 • c57Dg i0 i1 L η := by abel
    rw [e]; exact h1
  · have hle : (L ^ 2 / 4).toNNReal ≤ c57T2 L := by
      rw [← NNReal.coe_le_coe, hT1, hT2]; nlinarith [sq_nonneg L]
    have h1 := hall _ ⟨zero_le, hle⟩
    refine mem_box2 hne hL hη0 hη u ?_
    have hc : min (((L ^ 2 / 4).toNNReal : ℝ) / (L ^ 2 / 4)) 1 = 1 := by
      rw [hT1, div_self (by positivity)]; simp
    rw [hc, one_smul] at h1
    have e : c57P i0 i1 u L η + σ • w (L ^ 2 / 4).toNNReal - (c57P i0 i1 u L η + c57Dg i0 i1 L η) =
        σ • w (L ^ 2 / 4).toNNReal - c57Dg i0 i1 L η := by abel
    rw [e]; exact h1

/-- ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-, "Consequently": a path within `2^{j-6}` of the Brownian
path stays in the box of eq. (85) and is in `B^-` at time `4^{j-1}`. -/
theorem c57_consequence {i0 i1 : Fin d} (hne : i0 ≠ i1) {σ L η : ℝ} (hL : 0 < L) (hη0 : 0 ≤ η)
    (hη : η ≤ 3 * L / 16) {w : PathSpace d} (hw : Continuous w)
    (hmem : w ∈ c57Set i0 i1 σ L η) (u : Fin d → ℝ) {y : ℝ≥0 → Fin d → ℝ}
    (hy : ∀ s : ℝ≥0, (s : ℝ) ≤ L ^ 2 → ‖y s - (c57P i0 i1 u L η + σ • w s)‖ < L / 64) :
    (∀ s : ℝ≥0, (s : ℝ) ≤ L ^ 2 → y s ∈ c57BigBox i0 u L) ∧
      y (L ^ 2 / 4).toNNReal ∈ c57Bminus i0 u L := by
  obtain ⟨h1, h2⟩ := c57_on_event hne hL hη0 hη hw hmem u
  refine ⟨fun s hs k => ?_, fun k => ?_⟩
  · have hk := abs_lt.1 ((coord_le_norm _ _ k).trans_lt (hy s hs))
    have hb := h1 s hs k
    split_ifs at hb ⊢ <;> constructor <;> linarith [hb.1, hb.2, hk.1, hk.2]
  · have hs : (((L ^ 2 / 4).toNNReal : ℝ≥0) : ℝ) ≤ L ^ 2 := by
      rw [Real.coe_toNNReal _ (by positivity)]; nlinarith [sq_nonneg L]
    have hk := abs_lt.1 ((coord_le_norm _ _ k).trans_lt (hy _ hs))
    have hb := h2 k
    split_ifs at hb ⊢ <;> constructor <;> linarith [hb.1, hb.2, hk.1, hk.2]

end ElboimSly.Brownian
