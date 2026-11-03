/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Lemma82B
public import ElboimSly.Paper.Base.ConstantsBeta4
public import ElboimSly.Foundations.SRW.Lemma82B
public import Mathlib

/-!
# Lemma 8.2: the union bound and the modular reduction

ES22 Lemma 8.2, "Bound in Cases A and C" and "Setup".

* `farBox c n`: the box of lattice points at distance `< 4ⁿ` of `c` (at most `(2·4ⁿ)^d` points).
* `union_bound`: a union bound over a finite set of lattice points plus an exceptional event.
* `exists_mod`: `q₂ = q₁ + q + kβ` with `q ∈ [0, β)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The box of lattice points at sup-distance `< 4ⁿ` of `c`. -/
def farBox (c : Fin d → ℤ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Ioo (c i - 4 ^ n) (c i + 4 ^ n)

theorem mem_farBox {c b : Fin d → ℤ} {n : ℕ} (h : ‖b - c‖ < (4 : ℝ) ^ n) : b ∈ farBox c n := by
  rw [farBox, Fintype.mem_piFinset]
  intro i
  have h1 : ‖(b - c) i‖ ≤ ‖b - c‖ := norm_le_pi_norm (b - c) i
  have h2 : |((b i - c i : ℤ) : ℝ)| < (4 : ℝ) ^ n := by
    rw [← Int.norm_eq_abs]
    exact lt_of_le_of_lt h1 h
  have h3 : |b i - c i| < 4 ^ n := by exact_mod_cast h2
  rw [Finset.mem_Ioo]
  rw [abs_lt] at h3
  constructor <;> linarith [h3.1, h3.2]

theorem card_farBox (c : Fin d → ℤ) (n : ℕ) :
    (((farBox c n).card : ℕ) : ℝ) ≤ (2 * 4 ^ n : ℝ) ^ d := by
  rw [farBox, Fintype.card_piFinset]
  simp only [Int.card_Ioo]
  have h : ∏ x : Fin d, (c x + 4 ^ n - (c x - 4 ^ n) - 1).toNat ≤ ∏ _x : Fin d, (2 * 4 ^ n) :=
    Finset.prod_le_prod fun x _ => Int.toNat_le.2 (by push_cast; linarith)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have h' : ((∏ x : Fin d, (c x + 4 ^ n - (c x - 4 ^ n) - 1).toNat : ℕ) : ℝ) ≤
      (((2 * 4 ^ n) ^ d : ℕ) : ℝ) := by exact_mod_cast h
  have e : (((2 * 4 ^ n) ^ d : ℕ) : ℝ) = (2 * 4 ^ n : ℝ) ^ d := by push_cast; ring
  rw [e] at h'
  exact h'

theorem union_bound {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω} {ι : Type*}
    (F : Finset ι) {S bad : Set Ω} {E : ι → Set Ω} {B e : ℝ} (hB : 0 ≤ B) (he : 0 ≤ e)
    (hS : S ≤ᵐ[Pe] bad ∪ ⋃ x ∈ F, E x) (hbad : Pe bad ≤ ENNReal.ofReal B)
    (hE : ∀ x ∈ F, Pe (E x) ≤ ENNReal.ofReal e) :
    Pe S ≤ ENNReal.ofReal (B + F.card * e) := by
  calc Pe S ≤ Pe (bad ∪ ⋃ x ∈ F, E x) := measure_mono_ae hS
    _ ≤ Pe bad + Pe (⋃ x ∈ F, E x) := measure_union_le _ _
    _ ≤ ENNReal.ofReal B + ∑ x ∈ F, Pe (E x) :=
        add_le_add hbad (measure_biUnion_finset_le F E)
    _ ≤ ENNReal.ofReal B + ∑ _x ∈ F, ENNReal.ofReal e :=
        add_le_add le_rfl (Finset.sum_le_sum hE)
    _ = ENNReal.ofReal (B + F.card * e) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_add hB (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem exists_mod (q₁ q₂ : ℝ) :
    ∃ (q : ℝ) (k : ℤ), 0 ≤ q ∧ q < β ∧ q₂ = q₁ + q + k * β := by
  have hβ : 0 < β := Fact.out
  refine ⟨q₂ - q₁ - ⌊(q₂ - q₁) / β⌋ * β, ⌊(q₂ - q₁) / β⌋, ?_, ?_, by ring⟩
  · have := Int.floor_le ((q₂ - q₁) / β)
    rw [le_div_iff₀ hβ] at this
    linarith
  · have := Int.lt_floor_add_one ((q₂ - q₁) / β)
    rw [div_lt_iff₀ hβ] at this
    linarith

theorem es8Eps_ge (d n : ℕ) :
    Real.exp (-(n : ℝ) ^ 4) + ((2 : ℝ) ^ (n ^ 4))⁻¹ ≤ es8Eps d n := by
  unfold es8Eps
  have h1 : 0 ≤ (1 - es8C1 d) ^ es8K n := pow_nonneg (sub_nonneg.2 (es8C1_lt_one d).le) _
  have h2 : 0 ≤ 2 * (2 * 4 ^ (n + 1) / (n : ℝ) ^ 4 + 1) *
      Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5) := by positivity
  linarith

end ElboimSly.Paper

end
