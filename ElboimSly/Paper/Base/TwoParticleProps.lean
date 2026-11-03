/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.TwoParticle
public import Mathlib

/-!
# Two particles: deterministic properties

Two particles: deterministic properties (ES22 §8, ES22 §8).

Let `a ≠ b`, let `x₁ x₂` be driving paths without a common jump time, `p = a + x₁`,
`y = 𝔉_{a,b}(x₁, x₂)`, `D = y - p`, `Z = x₂ - x₁` and `E = y - b - x₂`.

* `twoParticle_ne` : (a) `D(s) ≠ 0`.
* `twoParticle_far` : (b) if `‖D(r-)‖₁ ≥ 2` then `y` moves as `x₂`.
* `twoParticle_E_zero`, `twoParticle_E_jump` : (c), the local form.
* `twoParticle_E_bound` : (c), the counting bound (in `TwoParticleCount`).

The left values `D(r-)` etc. are written with explicit `leftLim`s of `y`, `x₁`, `x₂`.
-/

@[expose] public section

open Set Filter Topology Function
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base

variable {d : ℕ}

/-- The `ℓ¹` norm on `ℤ^d`. -/
def l1 (v : Fin d → ℤ) : ℤ := ∑ i, |v i|

theorem l1_nonneg (v : Fin d → ℤ) : 0 ≤ l1 v := Finset.sum_nonneg fun _i _ => abs_nonneg _

theorem l1_neg (v : Fin d → ℤ) : l1 (-v) = l1 v := by simp [l1]

theorem l1_eq_zero_iff (v : Fin d → ℤ) : l1 v = 0 ↔ v = 0 := by
  unfold l1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _)]
  simp [funext_iff]

theorem l1_vec (v : SRW.Dir d) : l1 (SRW.Dir.vec v) = 1 := by
  unfold l1 SRW.Dir.vec
  rw [Finset.sum_eq_single v.1]
  · simp only [Pi.single_eq_same]; split_ifs <;> simp
  · intro j _ hj; simp [hj]
  · simp

theorem norm_le_l1 (v : Fin d → ℤ) : ‖v‖ ≤ (l1 v : ℝ) := by
  refine (pi_norm_le_iff_of_nonneg (by exact_mod_cast l1_nonneg v)).2 fun i => ?_
  have : |v i| ≤ l1 v := Finset.single_le_sum (f := fun j => |v j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  simpa [Int.norm_eq_abs] using (show ((|v i| : ℤ) : ℝ) ≤ (l1 v : ℝ) by exact_mod_cast this)

namespace IsDrivingPath

variable {x : ℝ≥0 → Fin d → ℤ}

theorem leftLim_of_notMem (hx : IsDrivingPath x) {r : ℝ≥0} (hr : 0 < r) (h : r ∉ CDisc x) :
    leftLim x r = x r := by
  by_contra hne
  exact h ((hx.step.mem_CDisc_iff hr).2 hne)

theorem leftLim_ne_of_mem (hx : IsDrivingPath x) {r : ℝ≥0} (h : r ∈ CDisc x) :
    leftLim x r ≠ x r := (hx.step.mem_CDisc_iff h.1).1 h

theorem l1_jump (hx : IsDrivingPath x) {r : ℝ≥0} (h : r ∈ CDisc x) :
    l1 (x r - leftLim x r) = 1 := by
  obtain ⟨v, hv⟩ := hx.jump r h
  rw [← hv]; exact l1_vec v

end IsDrivingPath

/-- The data of two particles: deterministic properties. -/
structure TwoParticleData (a b : Fin d → ℤ) (x₁ x₂ y : ℝ≥0 → Fin d → ℤ) : Prop where
  hx₁ : IsDrivingPath x₁
  hx₂ : IsDrivingPath x₂
  hnc : ∀ r, r ∈ CDisc x₁ → r ∉ CDisc x₂
  hy : IsTwoParticle a b x₁ x₂ y

variable {a b : Fin d → ℤ} {x₁ x₂ y : ℝ≥0 → Fin d → ℤ}

theorem twoStep_F1 (a : Fin d → ℤ) (x₁ x₂ : ℝ≥0 → Fin d → ℤ) (r : ℝ≥0) (w : Fin d → ℤ)
    (c : r ∈ CDisc x₁ ∧ (w = a + leftLim x₁ r ∨ w = a + x₁ r)) :
    twoStep a x₁ x₂ r w = if w = a + leftLim x₁ r then a + x₁ r else a + leftLim x₁ r := by
  classical
  unfold twoStep
  rw [ite_eq_left c]

theorem twoStep_F2 (a : Fin d → ℤ) (x₁ x₂ : ℝ≥0 → Fin d → ℤ) (r : ℝ≥0) (w : Fin d → ℤ)
    (c : ¬ (r ∈ CDisc x₁ ∧ (w = a + leftLim x₁ r ∨ w = a + x₁ r)))
    (c2 : r ∈ CDisc x₂ ∧ a + leftLim x₁ r ≠ w ∧ a + leftLim x₁ r ≠ w + (x₂ r - leftLim x₂ r)) :
    twoStep a x₁ x₂ r w = w + (x₂ r - leftLim x₂ r) := by
  classical
  unfold twoStep
  rw [ite_eq_right c, ite_eq_left c2]

theorem twoStep_F3 (a : Fin d → ℤ) (x₁ x₂ : ℝ≥0 → Fin d → ℤ) (r : ℝ≥0) (w : Fin d → ℤ)
    (c : ¬ (r ∈ CDisc x₁ ∧ (w = a + leftLim x₁ r ∨ w = a + x₁ r)))
    (c2 : ¬ (r ∈ CDisc x₂ ∧ a + leftLim x₁ r ≠ w ∧
      a + leftLim x₁ r ≠ w + (x₂ r - leftLim x₂ r))) :
    twoStep a x₁ x₂ r w = w := by
  classical
  unfold twoStep
  rw [ite_eq_right c, ite_eq_right c2]

theorem neBot_nhdsLT_of_pos {r : ℝ≥0} (hr : 0 < r) : (𝓝[<] r).NeBot :=
  nhdsLT_neBot_of_exists_lt ⟨0, hr⟩

/-- The left values: `y(r-) ≠ p(r-)` when `D` is nonzero just before `r`. -/
theorem TwoParticleData.leftLim_ne_of_ne (h : TwoParticleData a b x₁ x₂ y)
    {r : ℝ≥0} (hr : 0 < r) (hev : ∀ᶠ u in 𝓝[<] r, y u ≠ a + x₁ u) :
    leftLim y r ≠ a + leftLim x₁ r := by
  have := neBot_nhdsLT_of_pos hr
  obtain ⟨u, hu1, hu2, hu3⟩ := (hev.and ((h.hy.step.eventually_left_leftLim hr).and
    (h.hx₁.step.eventually_left_leftLim hr))).exists
  rw [← hu2, ← hu3]; exact hu1

/-- (a): `D(s) ≠ 0` for all `s`. -/
theorem TwoParticleData.ne (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b) (s : ℝ≥0) :
    y s ≠ a + x₁ s := by
  refine real_induction (Q := fun s => y s ≠ a + x₁ s) ?_ ?_ ?_ s
  · simp only [h.hy.zero, h.hx₁.zero, add_zero]; exact hab.symm
  · intro r hr hev
    have hw := h.leftLim_ne_of_ne hr hev
    rw [h.hy.rule r hr]
    by_cases c : r ∈ CDisc x₁ ∧ (leftLim y r = a + leftLim x₁ r ∨ leftLim y r = a + x₁ r)
    · rw [twoStep_F1 a x₁ x₂ r _ c, ite_eq_right hw]
      intro hh
      exact h.hx₁.leftLim_ne_of_mem c.1 (add_left_cancel hh)
    · by_cases c2 : r ∈ CDisc x₂ ∧ a + leftLim x₁ r ≠ leftLim y r ∧
          a + leftLim x₁ r ≠ leftLim y r + (x₂ r - leftLim x₂ r)
      · rw [twoStep_F2 a x₁ x₂ r _ c c2]
        have e := h.hx₁.leftLim_of_notMem hr (fun m => h.hnc r m c2.1)
        intro hh
        rw [e] at c2
        exact c2.2.2 hh.symm
      · rw [twoStep_F3 a x₁ x₂ r _ c c2]
        by_cases m : r ∈ CDisc x₁
        · intro hh
          exact c ⟨m, Or.inr hh⟩
        · intro hh
          rw [h.hx₁.leftLim_of_notMem hr m] at hw
          exact hw hh
  · intro r _
    filter_upwards [h.hy.step.rc r, h.hx₁.step.rc r] with u h1 h2
    rwa [h1, h2]

theorem TwoParticleData.leftLim_ne (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b)
    {r : ℝ≥0} (hr : 0 < r) : leftLim y r ≠ a + leftLim x₁ r :=
  h.leftLim_ne_of_ne hr (Filter.Eventually.of_forall fun u => h.ne hab u)

/-- (b), first half: away from contact, `y` moves as `x₂`. -/
theorem TwoParticleData.far_y (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b)
    {r : ℝ≥0} (hr : 0 < r) (hfar : 2 ≤ l1 (leftLim y r - (a + leftLim x₁ r))) :
    y r - leftLim y r = x₂ r - leftLim x₂ r := by
  have hw := h.leftLim_ne hab hr
  rw [h.hy.rule r hr]
  by_cases c : r ∈ CDisc x₁ ∧ (leftLim y r = a + leftLim x₁ r ∨ leftLim y r = a + x₁ r)
  · exfalso
    rcases c.2 with e | e
    · rw [e, sub_self] at hfar
      simp [l1] at hfar
    · rw [e] at hfar
      have : a + x₁ r - (a + leftLim x₁ r) = x₁ r - leftLim x₁ r := by abel
      rw [this, h.hx₁.l1_jump c.1] at hfar
      omega
  · by_cases c2 : r ∈ CDisc x₂ ∧ a + leftLim x₁ r ≠ leftLim y r ∧
        a + leftLim x₁ r ≠ leftLim y r + (x₂ r - leftLim x₂ r)
    · rw [twoStep_F2 a x₁ x₂ r _ c c2]; abel
    · rw [twoStep_F3 a x₁ x₂ r _ c c2]
      by_cases m : r ∈ CDisc x₂
      · exfalso
        have : a + leftLim x₁ r = leftLim y r ∨
            a + leftLim x₁ r = leftLim y r + (x₂ r - leftLim x₂ r) := by
          by_contra hh
          push Not at hh
          exact c2 ⟨m, hh.1, hh.2⟩
        rcases this with e | e
        · rw [← e, sub_self] at hfar
          simp [l1] at hfar
        · have e2 : leftLim y r - (a + leftLim x₁ r) = -(x₂ r - leftLim x₂ r) := by
            rw [e]; abel
          rw [e2, l1_neg, h.hx₂.l1_jump m] at hfar
          omega
      · rw [h.hx₂.leftLim_of_notMem hr m]; simp

/-- (b): away from contact, `y` and `D` move as `x₂` and `Z`. -/
theorem TwoParticleData.far (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b)
    {r : ℝ≥0} (hr : 0 < r) (hfar : 2 ≤ l1 (leftLim y r - (a + leftLim x₁ r))) :
    y r - leftLim y r = x₂ r - leftLim x₂ r ∧
      (y r - (a + x₁ r)) - (leftLim y r - (a + leftLim x₁ r)) =
        (x₂ r - x₁ r) - (leftLim x₂ r - leftLim x₁ r) := by
  have h1 := h.far_y hab hr hfar
  refine ⟨h1, ?_⟩
  linear_combination h1

/-- (c), local form: `E` changes only at contacts, by a unit vector. -/
theorem TwoParticleData.E_jump (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b)
    {r : ℝ≥0} (hr : 0 < r)
    (hne : y r - b - x₂ r ≠ leftLim y r - b - leftLim x₂ r) :
    l1 (leftLim y r - (a + leftLim x₁ r)) = 1 ∧ (r ∈ CDisc x₁ ∨ r ∈ CDisc x₂) ∧
      l1 ((y r - b - x₂ r) - (leftLim y r - b - leftLim x₂ r)) = 1 := by
  have hw := h.leftLim_ne hab hr
  rw [h.hy.rule r hr] at hne ⊢
  by_cases c : r ∈ CDisc x₁ ∧ (leftLim y r = a + leftLim x₁ r ∨ leftLim y r = a + x₁ r)
  · have hw2 : leftLim y r = a + x₁ r := c.2.resolve_left hw
    have e2 := h.hx₂.leftLim_of_notMem hr (fun m => h.hnc r c.1 m)
    rw [twoStep_F1 a x₁ x₂ r _ c, ite_eq_right hw]
    have e3 : leftLim y r - (a + leftLim x₁ r) = x₁ r - leftLim x₁ r := by rw [hw2]; abel
    refine ⟨by rw [e3]; exact h.hx₁.l1_jump c.1, Or.inl c.1, ?_⟩
    have e4 : (a + leftLim x₁ r - b - x₂ r) - (leftLim y r - b - leftLim x₂ r) =
        -(x₁ r - leftLim x₁ r) := by rw [hw2, e2]; abel
    rw [e4, l1_neg]; exact h.hx₁.l1_jump c.1
  · by_cases c2 : r ∈ CDisc x₂ ∧ a + leftLim x₁ r ≠ leftLim y r ∧
        a + leftLim x₁ r ≠ leftLim y r + (x₂ r - leftLim x₂ r)
    · rw [twoStep_F2 a x₁ x₂ r _ c c2] at hne
      exact absurd (by abel) hne
    · rw [twoStep_F3 a x₁ x₂ r _ c c2] at hne ⊢
      have hm : r ∈ CDisc x₂ := by
        by_contra m
        rw [h.hx₂.leftLim_of_notMem hr m] at hne
        exact hne (by abel)
      have : a + leftLim x₁ r = leftLim y r ∨
          a + leftLim x₁ r = leftLim y r + (x₂ r - leftLim x₂ r) := by
        by_contra hh
        push Not at hh
        exact c2 ⟨hm, hh.1, hh.2⟩
      rcases this with e | e
      · exact absurd e.symm hw
      · have e2 : leftLim y r - (a + leftLim x₁ r) = -(x₂ r - leftLim x₂ r) := by
          rw [e]; abel
        refine ⟨by rw [e2, l1_neg]; exact h.hx₂.l1_jump hm, Or.inr hm, ?_⟩
        have e4 : (leftLim y r - b - x₂ r) - (leftLim y r - b - leftLim x₂ r) =
            -(x₂ r - leftLim x₂ r) := by abel
        rw [e4, l1_neg]; exact h.hx₂.l1_jump hm

end ElboimSly.Paper
