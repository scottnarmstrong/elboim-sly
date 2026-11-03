/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.WalkPathAux
public import ElboimSly.Paper.Heavy.CyclicPath
public import Mathlib

/-!
# Oscillation of a right-continuous path is detected on rational times

Support for the event cH_1 (the event `Osc_1`). For a right-continuous `w` (as a cyclic path is)
and `T < T'`, a violation of `‖w s - w s'‖ ≤ r` for real `s, s' ∈ [0, T]` with `|s - s'| ≤ h`
yields a violation at rational times in `[0, T']` with `|q - q'| ≤ h`. This makes the violation
event a countable (hence measurable) union on the path space `[0, T'] → ℤ^d`.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal

namespace ElboimSly.Paper.Step

variable {d : ℕ}

/-- The rational times of `[0, T']`. -/
def h1RatTimes (T' : ℝ≥0) : Set (Set.Icc (0 : ℝ≥0) T') :=
  {q | ∃ r : ℚ, (((q : ℝ≥0)) : ℝ) = r}

theorem h1RatTimes_countable (T' : ℝ≥0) : (h1RatTimes T').Countable := by
  have : h1RatTimes T' = (fun q : Set.Icc (0 : ℝ≥0) T' => ((q : ℝ≥0) : ℝ)) ⁻¹'
      (Set.range ((↑) : ℚ → ℝ)) := by
    ext q; simp only [h1RatTimes, mem_ofPred_eq, mem_preimage, mem_range]
    exact ⟨fun ⟨r, hr⟩ => ⟨r, hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, hr.symm⟩⟩
  rw [this]
  exact (Set.countable_range _).preimage (NNReal.coe_injective.comp Subtype.val_injective)

/-- The pairs of rational times in `[0, c]` at distance at most `h`. -/
def h1RatPairs (T' c : ℝ≥0) (h : ℝ) :
    Set (Set.Icc (0 : ℝ≥0) T' × Set.Icc (0 : ℝ≥0) T') :=
  {x | x.1 ∈ h1RatTimes T' ∧ x.2 ∈ h1RatTimes T' ∧ |((x.1 : ℝ≥0) : ℝ) - ((x.2 : ℝ≥0) : ℝ)| ≤ h ∧
    (x.1 : ℝ≥0) ≤ c ∧ (x.2 : ℝ≥0) ≤ c}

theorem h1RatPairs_countable (T' c : ℝ≥0) (h : ℝ) : (h1RatPairs T' c h).Countable :=
  (((h1RatTimes_countable T').prod (h1RatTimes_countable T')).mono
    (fun x (hx : x ∈ h1RatPairs T' c h) =>
      (⟨hx.1, hx.2.1⟩ : x ∈ h1RatTimes T' ×ˢ h1RatTimes T')))

/-- The violation event on the path space, a countable union over rational pairs in `[0, c]`. -/
def h1OscBad (T' c : ℝ≥0) (h r : ℝ) : Set (Set.Icc (0 : ℝ≥0) T' → Fin d → ℤ) :=
  ⋃ x ∈ h1RatPairs T' c h, {p | r < ‖p x.1 - p x.2‖}

theorem measurableSet_h1OscBad (T' c : ℝ≥0) (h r : ℝ) :
    MeasurableSet (h1OscBad (d := d) T' c h r) := by
  refine MeasurableSet.biUnion (h1RatPairs_countable T' c h) fun x _ => ?_
  exact measurableSet_lt measurable_const
    ((measurable_of_countable (fun v : Fin d → ℤ => ‖v‖)).comp
      ((measurable_pi_apply x.1).sub (measurable_pi_apply x.2)))

/-- A rational point of `[0, T']` as an element of the subtype. -/
theorem exists_ratTime {T' : ℝ≥0} {q : ℚ} (h0 : (0 : ℝ) ≤ q) (h1 : (q : ℝ) ≤ T') :
    ∃ a : Set.Icc (0 : ℝ≥0) T', ((a : ℝ≥0) : ℝ) = q ∧ a ∈ h1RatTimes T' := by
  refine ⟨⟨Real.toNNReal q, zero_le, ?_⟩, ?_, ⟨q, ?_⟩⟩
  · have : ((Real.toNNReal q : ℝ≥0) : ℝ) ≤ T' := by
      rw [Real.coe_toNNReal _ h0]; exact h1
    exact_mod_cast this
  · simp [Real.coe_toNNReal _ h0]
  · simp [Real.coe_toNNReal _ h0]

/-- Real violations at times in `[0, T]`, `T < c ≤ T'`, give rational violations in `[0, c]`. -/
theorem exists_rat_approx {E : Type*} {w : ℝ → E} (hw : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s)
    {T c T' : ℝ≥0} (hT : T < c) (hcT : c ≤ T') {h : ℝ} (hh : 0 < h) {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s')
    (hs'T : s' ≤ T) (hd : s' - s ≤ h) :
    ∃ a b : Set.Icc (0 : ℝ≥0) T', a ∈ h1RatTimes T' ∧ b ∈ h1RatTimes T' ∧
      |((a : ℝ≥0) : ℝ) - ((b : ℝ≥0) : ℝ)| ≤ h ∧ (a : ℝ≥0) ≤ c ∧ (b : ℝ≥0) ≤ c ∧ w ((a : ℝ≥0) : ℝ) = w s ∧
      w ((b : ℝ≥0) : ℝ) = w s' := by
  have hs' : 0 ≤ s' := hs.trans hss
  obtain ⟨e1, he1, H1⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw s hs)
  obtain ⟨e2, he2, H2⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw s' hs')
  have hTT : (0 : ℝ) < (c : ℝ) - T := sub_pos.2 (by exact_mod_cast hT)
  set ε : ℝ := min (min (e1 - s) (e2 - s')) (min h ((c : ℝ) - T)) with hε
  have hε1 : 0 < ε := lt_min (lt_min (by simp at he1; linarith) (by simp at he2; linarith))
    (lt_min hh hTT)
  have hε_a : ε ≤ e1 - s := (min_le_left _ _).trans (min_le_left _ _)
  have hε_b : ε ≤ e2 - s' := (min_le_left _ _).trans (min_le_right _ _)
  have hε_h : ε ≤ h := (min_le_right _ _).trans (min_le_left _ _)
  have hε_T : ε ≤ (c : ℝ) - T := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (show s' < s' + ε by linarith)
  have hlt : max s ((q' : ℝ) - h) < s + ε := by
    refine max_lt (by linarith) ?_
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hq1a : s < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hq1b : (q' : ℝ) - h < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hcT' : (c : ℝ) ≤ T' := by exact_mod_cast hcT
  obtain ⟨a, ha1, ha2⟩ := exists_ratTime (T' := T') (q := q) (by linarith) (by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_ratTime (T' := T') (q := q') (by linarith) (by linarith)
  refine ⟨a, b, ha2, hb2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha1, hb1]
    rw [abs_le]
    constructor <;> linarith
  · have : ((a : ℝ≥0) : ℝ) ≤ c := by rw [ha1]; linarith
    exact_mod_cast this
  · have : ((b : ℝ≥0) : ℝ) ≤ c := by rw [hb1]; linarith
    exact_mod_cast this
  · rw [ha1]; exact H1 ⟨hq1a.le, by linarith⟩
  · rw [hb1]; exact H2 ⟨by linarith, by linarith⟩

end ElboimSly.Paper.Step

end
