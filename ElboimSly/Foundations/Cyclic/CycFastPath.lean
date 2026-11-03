/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFar
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Foundations.Cyclic.CycRegenEnvGlue
public import Mathlib

/-!
# ES22 Claim 2.3, Step 2: path facts

ES22 Claim 2.3, Step 2. Covering of a pair of times at distance `≤ 1` by a unit
window with an increment half as large (`cover_unit`), right-continuity of the cyclic walk of a
slice (`cycWalk_slice_rc`), the periodicity of the cyclic walk after `treg`
(`exists_lt_treg_eq`), and the identification of the regenerated walk with the first piece before
`treg` (`regenWalk_of_lt_treg`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ}

/-- A pair of times at distance `≤ 1` inside `[a₀, a₀ + B]` with a large increment gives a unit
window `[a₀ + i, a₀ + i + 2]` with a large deviation from its left end point. -/
theorem cover_unit {w : ℝ≥0 → Fin d → ℤ} {a₀ B T : ℝ≥0} {L : ℝ} {u u' : ℝ≥0} (huu' : u ≤ u')
    (h1 : u' - u ≤ 1) (hu : a₀ ≤ u) (hu' : u' ≤ a₀ + B) (huT : u ≤ a₀ + T)
    (hnorm : L ≤ ‖w u' - w u‖) :
    ∃ i : ℕ, i ≤ ⌊B⌋₊ ∧ i ≤ ⌊T⌋₊ ∧ ∃ x : ℝ≥0, x ≤ 2 ∧
      L / 2 ≤ ‖w (a₀ + i + x) - w (a₀ + i)‖ := by
  set i : ℕ := ⌊u - a₀⌋₊ with hi
  have hi1 : (i : ℝ≥0) ≤ u - a₀ := Nat.floor_le zero_le
  have hi2 : u - a₀ < i + 1 := Nat.lt_floor_add_one _
  have hiB : i ≤ ⌊B⌋₊ := Nat.floor_le_floor (by
    refine tsub_le_iff_left.2 ?_
    exact (huu'.trans hu') )
  have hiT : i ≤ ⌊T⌋₊ := Nat.floor_le_floor (tsub_le_iff_left.2 huT)
  have hc : a₀ + i ≤ u := (le_tsub_iff_left hu).1 hi1
  have hcu : u < a₀ + i + 1 := by
    have := (tsub_lt_iff_left hu).1 hi2
    rwa [← add_assoc] at this
  have hu'c : u' < a₀ + i + 2 := by
    calc u' ≤ u + 1 := tsub_le_iff_left.1 h1
      _ < a₀ + i + 1 + 1 := by rw [add_comm u 1, add_comm (a₀ + i + 1) 1]; exact add_lt_add_right hcu 1
      _ = _ := by ring
  set c := a₀ + (i : ℝ≥0) with hcdef
  have hx1 : c + (u - c) = u := add_tsub_cancel_of_le hc
  have hx2 : c + (u' - c) = u' := add_tsub_cancel_of_le (hc.trans huu')
  have htri : ‖w u' - w u‖ ≤ ‖w (c + (u' - c)) - w c‖ + ‖w (c + (u - c)) - w c‖ := by
    rw [hx1, hx2]
    have := norm_sub_le_norm_sub_add_norm_sub (w u') (w c) (w u)
    rwa [norm_sub_rev (w c) (w u)] at this
  have hx1' : u - c ≤ 2 := by
    refine tsub_le_iff_left.2 ?_
    have h12 : c + 1 ≤ c + 2 := add_le_add_right (by norm_num) c
    exact hcu.le.trans h12
  have hx2' : u' - c ≤ 2 := tsub_le_iff_left.2 hu'c.le
  by_cases h : L / 2 ≤ ‖w (c + (u' - c)) - w c‖
  · exact ⟨i, hiB, hiT, u' - c, hx2', h⟩
  · refine ⟨i, hiB, hiT, u - c, hx1', ?_⟩
    rw [not_le] at h
    linarith

variable {β : ℝ} [Fact (0 < β)]

/-- The cyclic walk of a slice of a good environment is right-continuous. -/
theorem cycWalk_slice_rc {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (k : ℕ) (s : ℝ≥0) :
    ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, ElboimSly.cycWalk (cycSlice k ν) 0 0 (u : ℝ) =
      ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ) := by
  have hlen := envPath_len (δ := regionData d k) (ν := ν) (hν k)
  have hfn : ∀ u : ℝ≥0, ElboimSly.cycWalk (cycSlice k ν) 0 0 (u : ℝ) =
      (envPath ν (regionData d k)).1.fn u := fun u => by
    rw [hlen.2]; exact (envFn_regionData' ν k u).symm
  simp only [hfn]
  exact (envPath ν (regionData d k)).1.rc s

/-- Periodicity: a value of the cyclic walk at time `q` is attained at a time `u ≤ q` before
`treg`. -/
theorem exists_lt_treg_eq {ν : Measure (RingSpace d β)} (hν : Good ν) (q : ℝ≥0) :
    ∃ u : ℝ≥0, u ≤ q ∧ (u : ℝ≥0∞) < ElboimSly.cycTreg ν ∧
      ElboimSly.cycWalk ν 0 0 (u : ℝ) = ElboimSly.cycWalk ν 0 0 (q : ℝ) := by
  have hβ : 0 < β := Fact.out
  by_cases htop : ElboimSly.cycTreg ν = ⊤
  · exact ⟨q, le_rfl, by rw [htop]; exact ENNReal.coe_lt_top, rfl⟩
  have hlt : ElboimSly.cycTreg ν < ⊤ := lt_top_iff_ne_top.2 htop
  set T : ℝ := (ElboimSly.cycTreg ν).toReal with hT
  have hTpos : 0 < T := by
    have h1 := regPlan_tau_ge ν
    have hb : (0 : ℝ≥0∞) < β.toNNReal := by exact_mod_cast Real.toNNReal_pos.2 hβ
    exact ENNReal.toReal_pos (hb.trans_le h1).ne' htop
  have hper : ∀ (s : ℝ) (n : ℕ), ElboimSly.cycWalk ν 0 0 (s + n * T) = ElboimSly.cycWalk ν 0 0 s := by
    intro s n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show s + ((n + 1 : ℕ) : ℝ) * T = (s + n * T) + T by push_cast; ring]
      rw [hT, cycWalk_add_treg hν hlt, ← hT, ih]
  set n : ℕ := ⌊(q : ℝ) / T⌋₊ with hn
  have hn1 : (n : ℝ) ≤ q / T := Nat.floor_le (by positivity)
  have hn2 : (q : ℝ) / T < n + 1 := Nat.lt_floor_add_one _
  have hu0 : 0 ≤ (q : ℝ) - n * T := by
    have := (le_div_iff₀ hTpos).1 hn1
    linarith
  have hu1 : (q : ℝ) - n * T < T := by
    have := (div_lt_iff₀ hTpos).1 hn2
    linarith
  refine ⟨((q : ℝ) - n * T).toNNReal, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]
    have : 0 ≤ (n : ℝ) * T := by positivity
    linarith
  · rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hu0]
    conv_rhs => rw [← ENNReal.ofReal_toReal htop]
    exact (ENNReal.ofReal_lt_ofReal_iff hTpos).2 hu1
  · rw [Real.coe_toNNReal _ hu0]
    have := hper ((q : ℝ) - n * T) n
    rw [sub_add_cancel] at this
    exact this.symm

omit [Fact (0 < β)] in
/-- Before `treg` of the first slice, the regenerated walk is the cyclic walk of the first slice. -/
theorem regenWalk_of_lt_treg (ν : ℕ → Measure (RingSpace d β)) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < ElboimSly.cycTreg (ν 0)) :
    ElboimSly.regenWalk ν (u : ℝ) = ElboimSly.cycWalk (ν 0) 0 0 (u : ℝ) := by
  rw [← gluedWalk_eq_regenWalk]
  have hm : Monotone (partialSums fun k => ElboimSly.cycTreg (ν k)) :=
    monotone_nat_of_le_succ fun n => by rw [partialSums_succ]; exact le_self_add
  have hcnt : gluedCount (partialSums fun k => ElboimSly.cycTreg (ν k)) u = 0 :=
    gluedCount_eq hm (by simp [partialSums]) (by simpa [partialSums] using hu)
  unfold gluedWalk
  rw [hcnt]
  simp [partialSums]

end ElboimSly.Cyclic

end
