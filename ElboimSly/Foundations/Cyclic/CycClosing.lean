/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycWalkPi
public import ElboimSly.Frozen.Defs.CycTreg
public import ElboimSly.Foundations.Interchange.TargetEvents
import Mathlib

/-!
# Closing of the cyclic walk

Closing (a), (b), (c).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem exists_int_add (s : ℝ) : ∃ (j : ℤ) (r : ℝ), 0 ≤ r ∧ r < β ∧ s = j * β + r := by
  have hβ : 0 < β := Fact.out
  refine ⟨⌊s / β⌋, s - ⌊s / β⌋ * β, ?_, ?_, by ring⟩
  · have := Int.floor_le (s / β)
    rw [le_div_iff₀ hβ] at this; linarith
  · have := Int.lt_floor_add_one (s / β)
    rw [div_lt_iff₀ hβ] at this; linarith

theorem cycWalk_nat_mul (hν : Good ν) (n : ℕ) :
    cycWalk ν 0 0 ((n : ℝ) * β) = ((piBeta hν) ^ (n : ℤ)) 0 := by
  have := cycWalk_int_mul hν (n : ℤ)
  simpa using this

omit [Fact (0 < β)] in
theorem cycTreg_le {n : ℕ} (hn : 1 ≤ n) (h : cycWalk ν 0 0 ((n : ℝ) * β) = 0) :
    cycTreg ν ≤ ENNReal.ofReal ((n : ℝ) * β) :=
  iInf_le (fun k : {k : ℕ // 1 ≤ k ∧ cycWalk ν 0 0 ((k : ℝ) * β) = 0} =>
    ENNReal.ofReal ((k.1 : ℝ) * β)) ⟨n, hn, h⟩

omit [Fact (0 < β)] in
theorem cycTreg_lt_top_iff : cycTreg ν < ⊤ ↔ ∃ n : ℕ, 1 ≤ n ∧ cycWalk ν 0 0 ((n : ℝ) * β) = 0 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have : IsEmpty {k : ℕ // 1 ≤ k ∧ cycWalk ν 0 0 ((k : ℝ) * β) = 0} :=
      ⟨fun ⟨k, hk, h0⟩ => hcon k hk h0⟩
    simp [cycTreg] at h
  · rintro ⟨n, hn, h0⟩
    exact lt_of_le_of_lt (cycTreg_le hn h0) ENNReal.ofReal_lt_top

/-- Closing (a). -/
theorem cycTreg_lt_top_iff_isFiniteCycle (hν : Good ν) : cycTreg ν < ⊤ ↔ IsFiniteCycle ν 0 := by
  rw [cycTreg_lt_top_iff]
  constructor
  · rintro ⟨n, hn, h0⟩
    refine ⟨n, hn, ?_⟩
    rw [← piBeta_pow_natCast hν, ← cycWalk_nat_mul hν, h0]
  · rintro ⟨n, hn, h0⟩
    refine ⟨n, hn, ?_⟩
    rw [cycWalk_nat_mul hν, piBeta_pow_natCast hν, h0]

/-- Closing (a): `{t_reg < ∞} = Fin₀` on `Good`. -/
theorem cycTreg_lt_top_iff_mem_finZeroEvent (hν : Good ν) :
    cycTreg ν < ⊤ ↔ ν ∈ finZeroEvent d β := by
  rw [mem_finZeroEvent_iff, cycTreg_lt_top_iff_isFiniteCycle hν]
  exact ⟨fun h => ⟨hν, h⟩, fun h => h.2⟩

/-- When finite, `t_reg = k₀ β` for the least `k₀ ≥ 1` with `W(k₀ β) = 0`. -/
theorem exists_cycTreg_eq (h : cycTreg ν < ⊤) :
    ∃ n : ℕ, 1 ≤ n ∧ cycWalk ν 0 0 ((n : ℝ) * β) = 0 ∧ cycTreg ν = ENNReal.ofReal ((n : ℝ) * β) := by
  classical
  have hex := cycTreg_lt_top_iff.mp h
  have hβ : 0 < β := Fact.out
  obtain ⟨hn, h0⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hn, h0, le_antisymm (cycTreg_le hn h0) ?_⟩
  refine le_iInf fun k => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.find_min' hex ⟨k.2.1, k.2.2⟩) hβ.le

/-- Closing (b). -/
theorem cycWalk_add_treg (hν : Good ν) (h : cycTreg ν < ⊤) (s : ℝ) :
    cycWalk ν 0 0 (s + (cycTreg ν).toReal) = cycWalk ν 0 0 s := by
  have hβ : 0 < β := Fact.out
  obtain ⟨n, hn, h0, he⟩ := exists_cycTreg_eq h
  rw [he, ENNReal.toReal_ofReal (by positivity)]
  have hper : ((piBeta hν) ^ (n : ℤ)) 0 = 0 := by rw [← cycWalk_nat_mul hν, h0]
  obtain ⟨j, r, hr0, hrβ, rfl⟩ := exists_int_add (β := β) s
  have e : (j : ℝ) * β + r + n * β = ((j + n : ℤ) : ℝ) * β + r := by push_cast; ring
  rw [e, cycWalk_eq_pi hν _ hr0 hrβ, cycWalk_eq_pi hν _ hr0 hrβ, zpow_add,
    Equiv.Perm.mul_apply, hper]

/-- Closing (c): a coincidence at times differing by a multiple of `β`
forces `t_reg ≤ s - s'`. -/
theorem cycTreg_le_of_eq (hν : Good ν) {s s' : ℝ} (hlt : s' < s) {k : ℤ}
    (hk : s - s' = k * β) (hW : cycWalk ν 0 0 s = cycWalk ν 0 0 s') :
    cycTreg ν ≤ ENNReal.ofReal (s - s') := by
  have hβ : 0 < β := Fact.out
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := by
      by_contra hc; push Not at hc; nlinarith
    exact_mod_cast this
  obtain ⟨j, r, hr0, hrβ, rfl⟩ := exists_int_add (β := β) s'
  have e : s = ((j + k : ℤ) : ℝ) * β + r := by push_cast; linarith
  rw [e, cycWalk_eq_pi hν _ hr0 hrβ, cycWalk_eq_pi hν _ hr0 hrβ] at hW
  have hinj := (interchangePi_bijective hν r.toNNReal).injective hW
  rw [zpow_add, Equiv.Perm.mul_apply] at hinj
  have h0 : ((piBeta hν) ^ k) 0 = 0 := (piBeta hν ^ j).injective hinj
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
  have hn : cycWalk ν 0 0 ((n : ℝ) * β) = 0 := by rw [cycWalk_nat_mul hν]; exact h0
  rw [hk]
  simpa using cycTreg_le (by omega) hn

/-- Closing (c), second sentence. -/
theorem cycWalk_ne_of_lt_treg (hν : Good ν) {s s' : ℝ} (hs' : 0 ≤ s') {k : ℤ}
    (hk1 : 1 ≤ k) (hk : s - s' = k * β) (hs : ENNReal.ofReal s < cycTreg ν) :
    cycWalk ν 0 0 s ≠ cycWalk ν 0 0 s' := by
  have hβ : 0 < β := Fact.out
  intro hW
  have hlt : s' < s := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  have := cycTreg_le_of_eq hν hlt hk hW
  have h2 : ENNReal.ofReal (s - s') ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal (by linarith)
  exact absurd (lt_of_le_of_lt (this.trans h2) hs) (lt_irrefl _)

end ElboimSly.Cyclic

end
