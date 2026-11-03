/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.StepAux
public import Mathlib

/-!
# Riemann sums of indicators of step paths

Supports regular functionals of pairs of paths (b): for a step path `g` with `J` discontinuities in `(0, T]` and a
measurable set `B`, the left Riemann sums `h ∑_l 1{g(l h) ∈ B}` over the dyadic mesh `h = T 2^{-m}`
differ from `Leb{x ∈ [0, T] : g(x) ∈ B}` by at most `J h`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Base

open ElboimSly.Cyclic

variable {V : Type*}

/-- The mesh points. -/
noncomputable def meshPt (T : ℝ≥0) (m l : ℕ) : ℝ≥0 := (l : ℝ≥0) * T / 2 ^ m

theorem coe_meshPt (T : ℝ≥0) (m l : ℕ) :
    (meshPt T m l : ℝ) = (l : ℝ) * ((T : ℝ) / 2 ^ m) := by
  unfold meshPt; push_cast; ring

/-- A cell of the dyadic mesh. -/
def meshCell (h : ℝ) (l : ℕ) : Set ℝ := Ico ((l : ℝ) * h) (((l : ℝ) + 1) * h)

/-- A cell is bad if it contains a discontinuity of `g` in its interior. -/
def BadCell (g : ℝ≥0 → V) (T : ℝ≥0) (h : ℝ) (l : ℕ) : Prop :=
  ∃ p ∈ CDisc g ∩ Iic T, (l : ℝ) * h < p ∧ (p : ℝ) < ((l : ℝ) + 1) * h

theorem const_on_good_cell {g : ℝ≥0 → V} (hg : IsStepPath g) {T : ℝ≥0} {m l : ℕ}
    (hl : l < 2 ^ m) (hgood : ¬ BadCell g T ((T : ℝ) / 2 ^ m) l) {x : ℝ}
    (hx : x ∈ meshCell ((T : ℝ) / 2 ^ m) l) : g x.toNNReal = g (meshPt T m l) := by
  have hN : (0 : ℝ) < 2 ^ m := by positivity
  have hTle : (((l : ℝ) + 1) * ((T : ℝ) / 2 ^ m)) ≤ T := by
    have : ((l : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast hl
    calc ((l : ℝ) + 1) * ((T : ℝ) / 2 ^ m) ≤ 2 ^ m * ((T : ℝ) / 2 ^ m) := by
          gcongr
      _ = T := by field_simp
  have hx0 : 0 ≤ x := le_trans (by rw [← coe_meshPt]; exact (meshPt T m l).2) hx.1
  have hsu : meshPt T m l ≤ x.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0, coe_meshPt]; exact hx.1
  refine const_of_no_disc hg.rc hsu (fun r hr hd => hgood ⟨r, ⟨hd, ?_⟩, ?_, ?_⟩) _
    ⟨hsu, le_rfl⟩
  · show r ≤ T
    rw [← NNReal.coe_le_coe]
    have h1 : (r : ℝ) ≤ x := by
      have := hr.2
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0] at this
      exact this
    exact h1.trans (hx.2.le.trans hTle)
  · have := hr.1
    rw [← NNReal.coe_lt_coe, coe_meshPt] at this
    exact this
  · have h1 : (r : ℝ) ≤ x := by
      have := hr.2
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0] at this
      exact this
    exact h1.trans_lt hx.2

theorem volume_meshCell (h : ℝ) (_hh : 0 ≤ h) (l : ℕ) :
    volume (meshCell h l) = ENNReal.ofReal h := by
  unfold meshCell
  rw [Real.volume_Ico]
  congr 1; ring

theorem pairwise_disjoint_meshCell {h : ℝ} (hh : 0 < h) :
    Pairwise (Function.onFun Disjoint (meshCell h)) := by
  intro l l' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  have h1 : (l : ℝ) < l' + 1 := by
    have : (l : ℝ) * h < (l' + 1) * h := hx.1.trans_lt hx'.2
    exact lt_of_mul_lt_mul_right this hh.le
  have h2 : (l' : ℝ) < l + 1 := by
    have : (l' : ℝ) * h < (l + 1) * h := hx'.1.trans_lt hx.2
    exact lt_of_mul_lt_mul_right this hh.le
  have h1' : l < l' + 1 := by exact_mod_cast h1
  have h2' : l' < l + 1 := by exact_mod_cast h2
  omega

open Classical in
theorem card_bad_le {g : ℝ≥0 → V} (hg : IsStepPath g) (T : ℝ≥0) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    ((Finset.range N).filter (fun l => BadCell g T h l)).card ≤ discCount g T := by
  classical
  have hfin := hg.fin T
  rw [discCount, Set.ncard_eq_toFinset_card _ hfin]
  refine Finset.card_le_card_of_injOn (fun l => if hl : BadCell g T h l then hl.choose else 0) ?_ ?_
  · intro l hl
    have hb : BadCell g T h l := (Finset.mem_filter.1 hl).2
    simp only [dite_eq_left hb, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hb.choose_spec.1
  · intro l hl l' hl' heq
    have hb : BadCell g T h l := (Finset.mem_filter.1 hl).2
    have hb' : BadCell g T h l' := (Finset.mem_filter.1 hl').2
    simp only [dite_eq_left hb, dite_eq_left hb'] at heq
    obtain ⟨_, a1, a2⟩ := hb.choose_spec
    obtain ⟨_, b1, b2⟩ := hb'.choose_spec
    rw [heq] at a1 a2
    have h1 : (l : ℝ) < l' + 1 := lt_of_mul_lt_mul_right (a1.trans b2) hh.le
    have h2 : (l' : ℝ) < l + 1 := lt_of_mul_lt_mul_right (b1.trans a2) hh.le
    have h1' : l < l' + 1 := by exact_mod_cast h1
    have h2' : l' < l + 1 := by exact_mod_cast h2
    omega

/-- The indicator `1{g(s) ∈ B}`. -/
noncomputable def indVal (g : ℝ≥0 → V) (B : Set V) (s : ℝ≥0) : ℝ :=
  open Classical in if g s ∈ B then 1 else 0

/-- The set `{x ∈ [0, T] : g(x) ∈ B}` (real time). -/
def levelSet (g : ℝ≥0 → V) (B : Set V) (T : ℝ≥0) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ x ≤ T ∧ g x.toNNReal ∈ B}

theorem measurableSet_levelSet [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    {g : ℝ≥0 → V} (hg : IsStepPath g) (B : Set V) (T : ℝ≥0) : MeasurableSet (levelSet g B T) := by
  have hgm := measurable_of_rc hg.rc
  have : levelSet g B T = Ici 0 ∩ Iic (T : ℝ) ∩ (fun x : ℝ => g x.toNNReal) ⁻¹' B := by
    ext x; simp [levelSet, and_assoc]
  rw [this]
  exact (measurableSet_Ici.inter measurableSet_Iic).inter
    ((hgm.comp measurable_real_toNNReal) (B.to_countable.measurableSet))

theorem riemann_error [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    {g : ℝ≥0 → V} (hg : IsStepPath g) (B : Set V) {T : ℝ≥0} (hT : 0 < T) (m : ℕ) :
    |(T : ℝ) / 2 ^ m * ∑ l ∈ Finset.range (2 ^ m), indVal g B (meshPt T m l) -
        (volume (levelSet g B T)).toReal| ≤ discCount g T * ((T : ℝ) / 2 ^ m) := by
  classical
  set N : ℕ := 2 ^ m with hN
  set h : ℝ := (T : ℝ) / 2 ^ m with hhdef
  have hNpos : (0 : ℝ) < 2 ^ m := by positivity
  have hh : 0 < h := div_pos (by exact_mod_cast hT) hNpos
  set E := levelSet g B T with hE
  have hEm : MeasurableSet E := measurableSet_levelSet hg B T
  have hcellm : ∀ l, MeasurableSet (meshCell h l) := fun l => measurableSet_Ico
  have hUm : MeasurableSet (⋃ l ∈ Finset.range N, meshCell h l) :=
    Finset.measurableSet_biUnion _ fun l _ => hcellm l
  have hNh : (N : ℝ) * h = T := by
    rw [hN, hhdef]; push_cast; field_simp
  -- the part of `E` outside the cells is null
  have hnull : volume (E \ ⋃ l ∈ Finset.range N, meshCell h l) = 0 := by
    refine measure_mono_null (t := {(T : ℝ)}) ?_ (Real.volume_singleton)
    intro x hx
    obtain ⟨⟨hx0, hxT, _⟩, hxU⟩ := hx
    by_contra hne
    have hxlt : x < T := lt_of_le_of_ne hxT hne
    apply hxU
    simp only [mem_iUnion, Finset.mem_range]
    refine ⟨⌊x / h⌋₊, ?_, ?_, ?_⟩
    · have : x / h < N := by
        rw [div_lt_iff₀ hh, hNh]; exact hxlt
      exact (Nat.floor_lt (div_nonneg hx0 hh.le)).2 this
    · have := Nat.floor_le (div_nonneg hx0 hh.le)
      calc (⌊x / h⌋₊ : ℝ) * h ≤ x / h * h := by gcongr
        _ = x := by field_simp
    · have := Nat.lt_floor_add_one (x / h)
      calc x = x / h * h := by field_simp
        _ < ((⌊x / h⌋₊ : ℝ) + 1) * h := by gcongr
  have hvol : volume E = ∑ l ∈ Finset.range N, volume (E ∩ meshCell h l) := by
    have h1 := measure_inter_add_sdiff E hUm (μ := volume)
    rw [hnull, add_zero] at h1
    rw [← h1, Set.inter_iUnion₂]
    refine measure_biUnion_finset ?_ fun l _ => hEm.inter (hcellm l)
    intro l _ l' _ hne
    exact ((pairwise_disjoint_meshCell hh) hne).mono inter_subset_right inter_subset_right
  have hcfin : ∀ l, volume (E ∩ meshCell h l) ≠ ⊤ := fun l =>
    ne_top_of_le_ne_top (by rw [volume_meshCell h hh.le]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hV : (volume E).toReal = ∑ l ∈ Finset.range N, (volume (E ∩ meshCell h l)).toReal := by
    rw [hvol, ENNReal.toReal_sum (fun l _ => hcfin l)]
  -- the cellwise estimate
  have hcell : ∀ l ∈ Finset.range N,
      |h * indVal g B (meshPt T m l) - (volume (E ∩ meshCell h l)).toReal| ≤
        if BadCell g T h l then h else 0 := by
    intro l hl
    have hlN : l < 2 ^ m := Finset.mem_range.1 hl
    have hc0 : 0 ≤ (volume (E ∩ meshCell h l)).toReal := ENNReal.toReal_nonneg
    have hcle : (volume (E ∩ meshCell h l)).toReal ≤ h := by
      have : volume (E ∩ meshCell h l) ≤ ENNReal.ofReal h := by
        rw [← volume_meshCell h hh.le l]; exact measure_mono inter_subset_right
      exact (ENNReal.toReal_le_of_le_ofReal hh.le this)
    have hi0 : 0 ≤ indVal g B (meshPt T m l) := by unfold indVal; split_ifs <;> norm_num
    have hi1 : indVal g B (meshPt T m l) ≤ 1 := by unfold indVal; split_ifs <;> norm_num
    by_cases hb : BadCell g T h l
    · rw [ite_eq_left hb, abs_le]
      constructor <;> nlinarith
    · rw [ite_eq_right hb]
      have hconst := fun x (hx : x ∈ meshCell h l) => const_on_good_cell hg hlN hb hx
      have hTle : ((l : ℝ) + 1) * h ≤ T := by
        have : ((l : ℝ) + 1) ≤ N := by exact_mod_cast hlN
        calc ((l : ℝ) + 1) * h ≤ N * h := by gcongr
          _ = T := hNh
      have hmem : ∀ x ∈ meshCell h l, 0 ≤ x ∧ x ≤ T := by
        intro x hx
        refine ⟨le_trans (by rw [← coe_meshPt]; exact (meshPt T m l).2) hx.1, hx.2.le.trans hTle⟩
      by_cases hB : g (meshPt T m l) ∈ B
      · have : E ∩ meshCell h l = meshCell h l := by
          ext x
          simp only [mem_inter_iff, hE, levelSet, mem_ofPred_eq]
          constructor
          · exact fun hx => hx.2
          · intro hx
            exact ⟨⟨(hmem x hx).1, (hmem x hx).2, by rw [hconst x hx]; exact hB⟩, hx⟩
        rw [this, volume_meshCell h hh.le, ENNReal.toReal_ofReal hh.le]
        simp [indVal, hB]
      · have : E ∩ meshCell h l = ∅ := by
          ext x
          simp only [mem_inter_iff, hE, levelSet, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          rintro ⟨⟨_, _, hx3⟩, hx⟩
          rw [hconst x hx] at hx3
          exact hB hx3
        rw [this]
        simp [indVal, hB]
  -- sum up
  have hsum : (T : ℝ) / 2 ^ m * ∑ l ∈ Finset.range N, indVal g B (meshPt T m l) -
      (volume E).toReal = ∑ l ∈ Finset.range N,
        (h * indVal g B (meshPt T m l) - (volume (E ∩ meshCell h l)).toReal) := by
    rw [hV, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hcell).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have := card_bad_le hg T hh N
  calc ((Finset.filter (fun l => BadCell g T h l) (Finset.range N)).card : ℝ) * h
      ≤ (discCount g T : ℝ) * h := by
        gcongr
    _ = _ := rfl

end ElboimSly.Paper.Base
