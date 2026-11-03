/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Claim69Aux
public import ElboimSly.Paper.Heavy.BadFinite
public import ElboimSly.Frozen.Defs.CycOmega
public import ElboimSly.Frozen.Defs.CycClosesBy
public import ElboimSly.Frozen.Defs.Good

/-!
# Good blocks and the blocks near the origin

Good blocks; Definition 6.5 (ES22 Definition 6.5, ES22 §6; deviations F09, F55) and blocks near the origin.

* `HeavyBlockGood d β t₀ n ν ι`: the block `ℬ_k(ι)` is good for the environment `ν`, conditions
  (GB1)-(GB3) for all `u₁, u₂ ∈ N(B, 2^{k+2})` and all integers `q₁, q₂ ∈ [0, β]`.
* `HeavyBlockBad`: `ν` is good and the block is not good for `ν`.
* `heavyBstar`: the blocks of `ℬ_k` within distance `2·5^n` of the origin;
  `ncard_heavyBstar_le`: there are at most `5^{d(n+1)}` of them.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Good blocks; Definition 6.5. The block `ℬ_k(ι)` is good for `ν`. -/
def HeavyBlockGood (d : ℕ) (β t₀ : ℝ) [Fact (0 < β)] (n : ℕ)
    (ν : Measure (RingSpace d β)) (ι : Fin d → ℤ) : Prop :=
  let k := heavyLevel d n
  let tk := heavyTkPrime d t₀ n
  ∀ u₁ ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2)),
  ∀ u₂ ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2)),
  ∀ q₁ q₂ : ℤ, (0 : ℝ) ≤ q₁ → (q₁ : ℝ) ≤ β → (0 : ℝ) ≤ q₂ → (q₂ : ℝ) ≤ β →
    -- (GB1)
    (cycClosesBy ν u₁ q₁ tk ∨
      ENNReal.ofReal ((9 / 10 + 1 / (heavyLevelPrime d t₀ n : ℝ)) * tk) ≤
        volume {s : ℝ | s ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β (fun r => cycWalk ν u₁ q₁ r) 0 s}) ∧
    -- (GB2)
    (∀ s ∈ Icc (0 : ℝ) tk, ‖cycWalk ν u₁ q₁ s - u₁‖ ≤ (2 : ℝ) ^ (k - 1)) ∧
    -- (GB3)
    (cycOmega ν u₁ u₂ q₁ q₂ tk →
      volume {s₂ : ℝ | s₂ ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
        ‖cycWalk ν u₁ q₁ s₁ - cycWalk ν u₂ q₂ s₂‖ ≤ (1.9 : ℝ) ^ k} <
        ENNReal.ofReal ((3.9 : ℝ) ^ k))

/-- A block is bad for `ν` if `ν` is a good configuration and the block is not good for `ν`. -/
def HeavyBlockBad (d : ℕ) (β t₀ : ℝ) [Fact (0 < β)] (n : ℕ)
    (ν : Measure (RingSpace d β)) (ι : Fin d → ℤ) : Prop :=
  Good ν ∧ ¬ HeavyBlockGood d β t₀ n ν ι

/-- Blocks near the origin. The blocks of `ℬ_k` within distance `2·5^n` of the origin. -/
def heavyBstar (d n : ℕ) : Set (Fin d → ℤ) :=
  {ι | latDist (0 : Fin d → ℤ) (heavyBlock (heavyLevel d n) ι) ≤ ((2 * 5 ^ n : ℕ) : ℝ)}

theorem heavyBstar_subset (d n : ℕ) :
    heavyBstar d n ⊆ ↑(Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-((2 * 5 ^ n : ℕ) : ℤ)) ((2 * 5 ^ n : ℕ) : ℤ)) := by
  intro ι hι
  obtain ⟨a, haB, ha⟩ := exists_le_of_latDist_le (heavyBlock_nonempty (heavyLevel d n) ι) hι
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro c
  have h1 : ((|a c| : ℤ) : ℝ) ≤ ((2 * 5 ^ n : ℕ) : ℝ) := by
    have h2 : ‖(0 - a) c‖ ≤ ‖0 - a‖ := norm_le_pi_norm (0 - a) c
    rw [Int.cast_abs]
    simpa [Int.norm_eq_abs] using h2.trans ha
  have h4 : |a c| ≤ ((2 * 5 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
  have hbl : a c / 2 ^ heavyLevel d n = ι c := haB c
  have h5 : |ι c| ≤ |a c| := by rw [← hbl]; exact Int.abs_ediv_le_abs _ _
  have := abs_le.1 (h5.trans h4)
  exact ⟨this.1, this.2⟩

theorem ncard_heavyBstar_le (d n : ℕ) (hn : 1 ≤ n) : (heavyBstar d n).ncard ≤ 5 ^ (d * (n + 1)) := by
  refine (Set.ncard_le_ncard (heavyBstar_subset d n) (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : ((((2 * 5 ^ n : ℕ) : ℤ) + 1 - -((2 * 5 ^ n : ℕ) : ℤ)).toNat) ≤ 5 ^ (n + 1) := by
    have h5 : 3 ≤ 5 ^ n := by
      calc 3 ≤ 5 ^ 1 := by norm_num
        _ ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  calc _ ≤ (5 ^ (n + 1)) ^ d := Nat.pow_le_pow_left this d
    _ = _ := by rw [← pow_mul, mul_comm]

end ElboimSly.Paper.Heavy
