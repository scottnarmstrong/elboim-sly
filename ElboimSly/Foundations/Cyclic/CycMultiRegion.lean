/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncTrunc
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvRegLim
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import ElboimSly.Foundations.Cyclic.CycTruncRC
public import Mathlib

/-!
# Several walks explored one after another (a), Step 3: the regions of the truncations

Several walks explored one after another (a), Step 3. The region of `Trunc_s(ρ)` is the set of points
explored at global times `Λ_j + r ≤ s` (`mem_region_trunc_iff`); it is monotone in `s`
(`region_trunc_mono`) and right-continuous: `⋂_{s > s₀} R(Trunc_s ρ) = R(Trunc_{s₀} ρ)`
(`mem_region_trunc_of_forall_gt`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [MeasurableSpace I] in
/-- Two global times at which the clock of `δ` shows the same time differ by a multiple of `β`, so
the clock hits a given value at a discrete set of local times. -/
theorem exists_clock_gap (δ : CycData I d) (θ : AddCircle β) (t0 : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ r : ℝ≥0, δ.clock β r = θ → ¬ (t0 < r ∧ r < t0 + ε) := by
  have hβ : 0 < β := Fact.out
  have key : ∀ r1 r2 : ℝ≥0, δ.clock β r1 = θ → δ.clock β r2 = θ → t0 < r1 → r1 < t0 + β.toNNReal →
      t0 < r2 → r2 < t0 + β.toNNReal → r1 = r2 := by
    intro r1 r2 h1 h2 a1 b1 a2 b2
    rw [clock_eq_iff] at h1 h2
    have h3 : (((r1 : ℝ≥0) : ℝ) : AddCircle β) - (((r2 : ℝ≥0) : ℝ) : AddCircle β) = 0 := by
      rw [h1, h2]; exact sub_self _
    rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h3
    obtain ⟨n, hn⟩ := h3
    have hb : ((β.toNNReal : ℝ≥0) : ℝ) = β := Real.coe_toNNReal _ hβ.le
    have e1 : (t0 : ℝ) < r1 := by exact_mod_cast a1
    have e2 : (t0 : ℝ) < r2 := by exact_mod_cast a2
    have f1 : (r1 : ℝ) < t0 + β := by
      have := (NNReal.coe_lt_coe.2 b1); push_cast [hb] at this; exact this
    have f2 : (r2 : ℝ) < t0 + β := by
      have := (NNReal.coe_lt_coe.2 b2); push_cast [hb] at this; exact this
    have hn0 : n = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
        rw [zsmul_eq_mul] at hn
        nlinarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
        rw [zsmul_eq_mul] at hn
        nlinarith
    subst hn0
    simp only [zero_smul] at hn
    exact NNReal.coe_injective (by linarith)
  by_cases hex : ∃ r : ℝ≥0, δ.clock β r = θ ∧ t0 < r ∧ r < t0 + β.toNNReal
  · obtain ⟨r0, h0, a0, b0⟩ := hex
    refine ⟨r0 - t0, tsub_pos_of_lt a0, fun r hr ⟨a, b⟩ => ?_⟩
    have hle : r0 - t0 ≤ β.toNNReal := by
      have : r0 - t0 < β.toNNReal := by
        have := b0; rw [← tsub_lt_iff_left a0.le] at this; exact this
      exact this.le
    have b' : r < t0 + β.toNNReal := b.trans_le (add_le_add le_rfl hle)
    have := key r r0 hr h0 a b' a0 b0
    rw [this] at b
    rw [add_tsub_cancel_of_le a0.le] at b
    exact lt_irrefl _ b
  · refine ⟨β.toNNReal, Real.toNNReal_pos.2 hβ, fun r hr ⟨a, b⟩ => hex ⟨r, hr, a, b⟩⟩

namespace CycRec

variable [Countable I] [MeasurableSingletonClass I]

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
theorem multi_cum_succ (junk : CycEntry I d) (ρ : CycRec I d) {k : ℕ} (hk : (k : ℕ∞) < ρ.num) :
    ρ.cum (k + 1) = ρ.cum k + (ρ.coord junk k).len := by
  unfold CycRec.cum
  rw [Finset.sum_range_succ, CycRec.lenAt_eq junk, ite_eq_left hk]

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
omit [MeasurableSpace I] in
/-- The region of `Trunc_s(ρ)`: the points explored at global times `Λ_j + r ≤ s`. -/
theorem mem_region_trunc_iff (junk : CycEntry I d) (s : ℝ≥0) (ρ : CycRec I d)
    (x : I × RingSpace d β) :
    x ∈ (CycRec.trunc s ρ).region β ↔ ∃ j : ℕ, (j : ℕ∞) < ρ.num ∧ ∃ r : ℝ≥0, 0 < r ∧
      (r : ℝ≥0∞) ≤ (ρ.coord junk j).len ∧ ρ.cum j + r ≤ s ∧
      x.1 = (ρ.coord junk j).data.copy ∧ x.2.2 = (ρ.coord junk j).data.clock β r ∧
      Edge.Mem ((ρ.coord junk j).path.left r) x.2.1 := by
  classical
  constructor
  · rintro ⟨e, ⟨k, hk⟩, hx⟩
    rw [CycRec.trunc_nth junk] at hk
    split_ifs at hk with hks
    obtain rfl : CycRec.truncEntry s ρ k (ρ.coord junk k) = e := Option.some.inj hk
    have hc1 := multi_cum_succ junk ρ hks.1
    by_cases hc : ρ.cum (k + 1) ≤ s
    · unfold CycRec.truncEntry at hx
      rw [ite_eq_left hc] at hx
      obtain ⟨r, hr0, hrl, h1, h2, h3⟩ := hx
      refine ⟨k, hks.1, r, hr0, hrl, ?_, h1, h2, h3⟩
      calc ρ.cum k + r ≤ ρ.cum k + (ρ.coord junk k).len := add_le_add le_rfl hrl
        _ = ρ.cum (k + 1) := hc1.symm
        _ ≤ s := hc
    · unfold CycRec.truncEntry at hx
      rw [ite_eq_right hc] at hx
      obtain ⟨r, hr0, hrl, h1, h2, h3⟩ :=
        (CycSchemeEnv.mem_region_cut_iff (ρ.coord junk k).1 (ρ.coord junk k).2
          ((s : ℝ≥0∞) - ρ.cum k) x).1 hx
      refine ⟨k, hks.1, r, hr0, ?_, add_le_of_le_tsub_left_of_le hks.2 hrl, h1, h2, h3⟩
      refine hrl.trans (tsub_le_iff_right.2 ?_)
      rw [add_comm, ← hc1]; exact (not_le.1 hc).le
  · rintro ⟨j, hj, r, hr0, hrl, hcum, h1, h2, h3⟩
    have hjs : j ∈ ρ.surv s := ⟨hj, (le_self_add).trans hcum⟩
    have hc1 := multi_cum_succ junk ρ hj
    refine ⟨CycRec.truncEntry s ρ j (ρ.coord junk j), ⟨j, ?_⟩, ?_⟩
    · rw [CycRec.trunc_nth junk, ite_eq_left hjs]
    · unfold CycRec.truncEntry
      by_cases hc : ρ.cum (j + 1) ≤ s
      · rw [ite_eq_left hc]; exact ⟨r, hr0, hrl, h1, h2, h3⟩
      · rw [ite_eq_right hc]
        exact (CycSchemeEnv.mem_region_cut_iff (ρ.coord junk j).1 (ρ.coord junk j).2
          ((s : ℝ≥0∞) - ρ.cum j) x).2 ⟨r, hr0, ENNReal.le_sub_of_add_le_left
          (ne_top_of_le_ne_top ENNReal.coe_ne_top ((le_self_add).trans hcum)) hcum, h1, h2, h3⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
omit [MeasurableSpace I] in
theorem region_trunc_mono (junk : CycEntry I d) {s s' : ℝ≥0} (h : s ≤ s') (ρ : CycRec I d) :
    (CycRec.trunc s ρ).region β ⊆ (CycRec.trunc s' ρ).region β := by
  intro x hx
  rw [mem_region_trunc_iff junk] at hx ⊢
  obtain ⟨j, hj, r, hr0, hrl, hcum, rest⟩ := hx
  exact ⟨j, hj, r, hr0, hrl, hcum.trans (by exact_mod_cast h), rest⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
/-- Right-continuity of the region: `⋂_{s > s₀} R(Trunc_s ρ) ⊆ R(Trunc_{s₀} ρ)`. -/
theorem mem_region_trunc_of_forall_gt (junk : CycEntry I d) (ρ : CycRec I d) (s0 : ℝ≥0)
    (x : I × RingSpace d β) (h : ∀ s : ℝ≥0, s0 < s → x ∈ (CycRec.trunc s ρ).region β) :
    x ∈ (CycRec.trunc s0 ρ).region β := by
  classical
  rw [mem_region_trunc_iff junk]
  by_cases hall : ∃ j : ℕ, (j : ℕ∞) < ρ.num ∧ (s0 : ℝ≥0∞) < ρ.cum (j + 1)
  · obtain ⟨ε1, hε1, hgap⟩ := ρ.exists_cum_gap s0
    set j0 := Nat.find hall with hj0
    obtain ⟨hj0num, hj0gt⟩ := Nat.find_spec hall
    have hcj0 : ρ.cum j0 ≤ s0 := by
      rcases Nat.eq_zero_or_pos j0 with h0 | hpos
      · rw [h0]; simp [CycRec.cum]
      · have := Nat.find_min hall (Nat.sub_lt hpos one_pos)
        have hlt : ((j0 - 1 : ℕ) : ℕ∞) < ρ.num :=
          lt_of_le_of_lt (by exact_mod_cast Nat.sub_le j0 1) hj0num
        have h' : ρ.cum (j0 - 1 + 1) ≤ s0 := by
          by_contra hh; exact this ⟨hlt, not_le.1 hh⟩
        rwa [Nat.sub_add_cancel hpos] at h'
    have hcfin : ρ.cum j0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hcj0
    set t0 : ℝ≥0 := s0 - (ρ.cum j0).toNNReal with ht0
    obtain ⟨ε2, hε2, hdisc⟩ := exists_clock_gap (β := β) (ρ.coord junk j0).data x.2.2 t0
    have hpos : 0 < min ε1 ε2 / 2 := by positivity
    obtain ⟨j, hj, r, hr0, hrl, hcum, h1, h2, h3⟩ :=
      (mem_region_trunc_iff junk (s0 + min ε1 ε2 / 2) ρ x).1 (h _ (lt_add_of_pos_right _ hpos))
    have hsup : ((s0 + min ε1 ε2 / 2 : ℝ≥0) : ℝ≥0∞) < s0 + ε1 := by
      rw [← ENNReal.coe_add]
      exact_mod_cast add_lt_add_of_le_of_lt le_rfl (lt_of_lt_of_le (half_lt_self (by positivity))
        (min_le_left _ _))
    rcases lt_trichotomy j j0 with hlt | heq | hgt
    · refine ⟨j, hj, r, hr0, hrl, ?_, h1, h2, h3⟩
      have hc1 := multi_cum_succ junk ρ hj
      calc ρ.cum j + r ≤ ρ.cum j + (ρ.coord junk j).len := add_le_add le_rfl hrl
        _ = ρ.cum (j + 1) := hc1.symm
        _ ≤ ρ.cum j0 := ρ.cum_mono (Nat.succ_le_of_lt hlt)
        _ ≤ s0 := hcj0
    · subst heq
      refine ⟨j0, hj, r, hr0, hrl, ?_, h1, h2, h3⟩
      by_contra hne
      refine hdisc r h2.symm ⟨?_, ?_⟩
      · by_contra hle
        push Not at hle
        apply hne
        have : (ρ.cum j0 + r : ℝ≥0∞) ≤ ρ.cum j0 + (t0 : ℝ≥0∞) := by
          exact add_le_add le_rfl (by exact_mod_cast hle)
        refine this.trans ?_
        rw [ht0, ENNReal.coe_sub, ENNReal.coe_toNNReal hcfin]
        exact (add_tsub_cancel_of_le hcj0).le
      · -- r < t0 + ε2
        have hcr : (ρ.cum j0 + r : ℝ≥0∞) ≤ (s0 + min ε1 ε2 / 2 : ℝ≥0) := hcum
        rw [← ENNReal.coe_toNNReal hcfin] at hcr
        rw [← ENNReal.coe_add, ENNReal.coe_le_coe] at hcr
        have : r ≤ t0 + min ε1 ε2 / 2 := by
          rw [ht0]
          have hle : (ρ.cum j0).toNNReal ≤ s0 := by
            have := hcj0; rwa [← ENNReal.coe_toNNReal hcfin, ENNReal.coe_le_coe] at this
          have : r ≤ s0 + min ε1 ε2 / 2 - (ρ.cum j0).toNNReal := by
            rw [le_tsub_iff_left (hle.trans (le_self_add))]; exact hcr
          refine this.trans ?_
          rw [tsub_add_eq_add_tsub hle]
        exact lt_of_le_of_lt this (add_lt_add_of_le_of_lt le_rfl
          (lt_of_lt_of_le (half_lt_self (by positivity)) (min_le_right _ _)))
    · exfalso
      have h5 : ρ.cum (j0 + 1) ≤ ρ.cum j := ρ.cum_mono (Nat.succ_le_of_lt hgt)
      refine hgap j ⟨hj0gt.trans_le h5, ?_⟩
      exact lt_of_le_of_lt ((le_self_add).trans hcum) hsup
  · push Not at hall
    obtain ⟨j, hj, r, hr0, hrl, hcum, rest⟩ :=
      (mem_region_trunc_iff junk (s0 + 1) ρ x).1 (h _ (lt_add_one _))
    refine ⟨j, hj, r, hr0, hrl, ?_, rest⟩
    have hc1 := multi_cum_succ junk ρ hj
    calc ρ.cum j + r ≤ ρ.cum j + (ρ.coord junk j).len := add_le_add le_rfl hrl
      _ = ρ.cum (j + 1) := hc1.symm
      _ ≤ s0 := hall j hj

end CycRec

end ElboimSly.Cyclic

end
