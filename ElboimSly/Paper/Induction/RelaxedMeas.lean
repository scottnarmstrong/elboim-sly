/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsRelaxedTimeWrt
public import Mathlib

/-!
# Measurability of relaxed times: the abstract part

Measurability of relaxed times (Steps 1, 3, 4).

For a family of right-locally-constant lattice paths `w ω`, jointly measurable in `(ω, t)`, and a
jointly measurable start `a ω t`, the set `{(ω, t) | IsRelaxedTimeWrt β (w ω) (a ω t) t}` is
measurable (`measurableSet_isRelaxedTimeWrt`).
-/

@[expose] public section

open MeasureTheory Set

namespace ElboimSly.Paper

variable {d : ℕ}

/-- Countable description of the values of `w` on `[a, e]` (Step 1 of the written proof). -/
def RelaxedVmem (w : ℝ → Fin d → ℤ) (a e : ℝ) (y : Fin d → ℤ) : Prop :=
  a ≤ e ∧ (w a = y ∨ w e = y ∨ ∃ q : ℚ, a ≤ (q : ℝ) ∧ (q : ℝ) < e ∧ w q = y)

/-- Step 1: values on an interval are read off a countable set. -/
theorem mem_image_Icc_iff_vmem (w : ℝ → Fin d → ℤ)
    (hrc : ∀ s, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), w s' = w s) (a e : ℝ) (y : Fin d → ℤ) :
    y ∈ w '' Icc a e ↔ RelaxedVmem w a e y := by
  constructor
  · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
    refine ⟨h1.trans h2, ?_⟩
    rcases h2.eq_or_lt with h | h
    · exact Or.inr (Or.inl (by rw [h]))
    · obtain ⟨ε, hε, hc⟩ := hrc s
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right s hε) h)
      have hq3 : (q : ℝ) < s + ε := hq2.trans_le (min_le_left _ _)
      have hq4 : (q : ℝ) < e := hq2.trans_le (min_le_right _ _)
      exact Or.inr (Or.inr ⟨q, h1.trans hq1.le, hq4, hc q ⟨hq1.le, hq3⟩⟩)
  · rintro ⟨hae, h | h | ⟨q, hq1, hq2, h⟩⟩
    · exact ⟨a, ⟨le_rfl, hae⟩, h⟩
    · exact ⟨e, ⟨hae, le_rfl⟩, h⟩
    · exact ⟨q, ⟨hq1, hq2.le⟩, h⟩

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {w : Ω → ℝ → Fin d → ℤ}

theorem measurableSet_vmem (hw : Measurable fun p : Ω × ℝ => w p.1 p.2)
    {A E : Ω × ℝ → ℝ} {Y : Ω × ℝ → Fin d → ℤ} (hA : Measurable A) (hE : Measurable E)
    (hY : Measurable Y) :
    MeasurableSet {p : Ω × ℝ | RelaxedVmem (w p.1) (A p) (E p) (Y p)} := by
  have hwA : Measurable fun p : Ω × ℝ => w p.1 (A p) :=
    hw.comp (measurable_fst.prodMk hA)
  have hwE : Measurable fun p : Ω × ℝ => w p.1 (E p) :=
    hw.comp (measurable_fst.prodMk hE)
  have hwq : ∀ q : ℚ, Measurable fun p : Ω × ℝ => w p.1 (q : ℝ) := fun q =>
    hw.comp (measurable_fst.prodMk measurable_const)
  have : {p : Ω × ℝ | RelaxedVmem (w p.1) (A p) (E p) (Y p)} =
      {p | A p ≤ E p} ∩ ({p | w p.1 (A p) = Y p} ∪ {p | w p.1 (E p) = Y p} ∪
        ⋃ q : ℚ, ({p | A p ≤ (q : ℝ)} ∩ {p | (q : ℝ) < E p} ∩ {p | w p.1 (q : ℝ) = Y p})) := by
    ext p
    simp only [RelaxedVmem, mem_ofPred_eq, mem_inter_iff, mem_union, mem_iUnion]
    tauto
  rw [this]
  refine (measurableSet_le hA hE).inter ?_
  refine ((measurableSet_eq_fun hwA hY).union (measurableSet_eq_fun hwE hY)).union ?_
  exact MeasurableSet.iUnion fun q =>
    ((measurableSet_le hA measurable_const).inter (measurableSet_lt measurable_const hE)).inter
      (measurableSet_eq_fun (hwq q) hY)

end Meas

/-! ### The heavy test on integer radii -/

theorem abs_le_iff_floor (z : ℤ) {r : ℝ} (hr : 0 ≤ r) :
    |(z : ℝ)| ≤ r ↔ |(z : ℝ)| ≤ (⌊r⌋₊ : ℝ) := by
  have h1 : |(z : ℝ)| = (z.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h1, Nat.cast_le, ← Nat.le_floor_iff hr]

theorem norm_le_iff_floor (u : Fin d → ℤ) {r : ℝ} (hr : 0 ≤ r) :
    ‖u‖ ≤ r ↔ ‖u‖ ≤ (⌊r⌋₊ : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg hr, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
  refine forall_congr' fun i => ?_
  simpa [Int.norm_eq_abs] using abs_le_iff_floor (u i) hr

theorem ball_eq_floor (x : Fin d → ℤ) {r : ℝ} (hr : 0 ≤ r) :
    {v : Fin d → ℤ | ‖v - x‖ ≤ r} = {v | ‖v - x‖ ≤ (⌊r⌋₊ : ℝ)} := by
  ext v
  exact norm_le_iff_floor _ hr

/-- The box of integer radius `m`. -/
noncomputable def relaxedBox (d m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(m : ℤ)) m

theorem ncard_ball_inter (x : Fin d → ℤ) (m : ℕ) (V : Set (Fin d → ℤ)) :
    ({v : Fin d → ℤ | ‖v - x‖ ≤ (m : ℝ)} ∩ V).ncard =
      by classical exact ((relaxedBox d m).filter fun u => x + u ∈ V).card := by
  classical
  have : {v : Fin d → ℤ | ‖v - x‖ ≤ (m : ℝ)} ∩ V =
      (fun u => x + u) '' ↑((relaxedBox d m).filter fun u => x + u ∈ V) := by
    ext v
    simp only [mem_inter_iff, mem_ofPred_eq, mem_image, Finset.coe_filter, relaxedBox,
      Fintype.mem_piFinset, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨v - x, ⟨?_, by simpa using h2⟩, by simp⟩
      intro i
      have := (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg m)).1 h1 i
      rw [Int.norm_eq_abs] at this
      have h3 : |((v - x) i : ℤ)| ≤ m := by exact_mod_cast this
      exact abs_le.1 h3
    · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, h2⟩
      rw [add_sub_cancel_left]
      refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg m)).2 fun i => ?_
      rw [Int.norm_eq_abs]
      have : |u i| ≤ m := abs_le.2 (h1 i)
      exact_mod_cast this
  rw [this, Set.ncard_image_of_injective _ (add_right_injective x), Set.ncard_coe_finset]

/-- Radius reduction for (R1): the block test needs only the integer radii. -/
theorem forall_not_heavy_iff (x : Fin d → ℤ) (V : Set (Fin d → ℤ)) {b : ℝ} (hb : 0 < b) :
    (∀ r : ℝ, b ≤ r → ¬ (0 < r ∧
      r ^ (5 / 2 : ℝ) ≤ (({v : Fin d → ℤ | ‖v - x‖ ≤ r} ∩ V).ncard : ℝ))) ↔
    ∀ m : ℕ, b < (m : ℝ) + 1 → ¬ ((max (m : ℝ) b) ^ (5 / 2 : ℝ) ≤
      (({v : Fin d → ℤ | ‖v - x‖ ≤ (m : ℝ)} ∩ V).ncard : ℝ)) := by
  constructor
  · intro h m hm hle
    have hr : b ≤ max (m : ℝ) b := le_max_right _ _
    refine h _ hr ⟨lt_of_lt_of_le hb hr, ?_⟩
    have hfl : ⌊max (m : ℝ) b⌋₊ = m := by
      rw [Nat.floor_eq_iff (le_trans hb.le hr)]
      refine ⟨le_max_left _ _, max_lt (by linarith) hm⟩
    rw [ball_eq_floor x (le_trans hb.le hr), hfl]
    exact hle
  · intro h r hr ⟨hr0, hheavy⟩
    set m := ⌊r⌋₊ with hmdef
    have hrnn : 0 ≤ r := hr0.le
    have hm1 : r < (m : ℝ) + 1 := Nat.lt_floor_add_one r
    have hmr : (m : ℝ) ≤ r := Nat.floor_le hrnn
    refine h m (lt_of_le_of_lt hr hm1) ?_
    have hle : max (m : ℝ) b ≤ r := max_le hmr hr
    rw [ball_eq_floor x hrnn] at hheavy
    refine le_trans ?_ hheavy
    exact Real.rpow_le_rpow (le_trans hb.le (le_max_right _ _)) hle (by norm_num)

end ElboimSly.Paper

end
