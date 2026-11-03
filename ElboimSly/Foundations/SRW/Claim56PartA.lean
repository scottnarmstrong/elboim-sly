/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56Ctx
public import Mathlib

/-!
# Claim 5.6, event `𝓑_0`, Part A (`[0, τ/2]`)
-/

@[expose] public section

open Set
open scoped NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- `ℓ_A = ⌈√τ⌉ + 2`. -/
noncomputable def ellA (s₀ : ℝ) : ℕ := ⌈s₀⌉₊ + 2

/-- Lower corner of the one-sided box of Part A. -/
noncomputable def mA (j : ℕ) (u : Fin d → ℤ) (s₀ : ℝ) (v : Fin d → ℤ) : Fin d → ℤ := fun i =>
  if (v i : ℝ) ≤ claimQ j u i then v i else v i - ellA s₀ + 1

/-- The box of Part A. -/
noncomputable def QA (j : ℕ) (u : Fin d → ℤ) (s₀ : ℝ) (v : Fin d → ℤ) : Set (Fin d → ℤ) :=
  boxSet (mA j u s₀ v) (fun _ => ellA s₀)

variable {j m : ℕ} {t s₀ P N : ℝ}

theorem ellA_bounds (hs : 288 ≤ s₀) : s₀ + 2 ≤ (ellA s₀ : ℝ) ∧ (ellA s₀ : ℝ) ≤ s₀ + 3 := by
  unfold ellA
  have h1 := Nat.le_ceil s₀
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ s₀ by linarith)
  push_cast
  constructor <;> linarith

theorem v_mem_QA (u v : Fin d → ℤ) (s₀ : ℝ) (hs : 288 ≤ s₀) : v ∈ QA j u s₀ v := by
  intro i
  have h := ellA_bounds hs
  have hl : (1 : ℤ) ≤ ellA s₀ := by
    have : (1 : ℝ) ≤ ellA s₀ := by linarith [h.1]
    exact_mod_cast this
  simp only [mA, mem_Icc]
  split_ifs <;> constructor <;> omega

theorem Ctx.QA_sub (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j) (hj : 1 ≤ j) :
    QA j u s₀ v ⊆ claimBox u j := by
  intro z hz i
  have hz' := hz i
  obtain ⟨he0, he1⟩ := claimBox_coord hj hv i
  have hb := ellA_bounds c.s288
  have hL1 : N / 2 ≤ claimL j i := by
    have := claimL_ge (j := j) i
    rw [c.hN]; exact this
  have hsl := sideLen_cast (d := d) j hj i
  have hLeq : ((sideLen d j i : ℕ) : ℝ) = claimL j i := by
    unfold claimL; rw [hsl]
  have hP := c.P0
  have hN4 : 2 * s₀ ≤ claimL j i / 2 := by
    have : P * s₀ ≤ N := c.N1
    nlinarith [c.P8, c.s288]
  rw [mem_Icc] at hz' ⊢
  unfold mA at hz'
  simp only at hz'
  have hq := claimQ_eq j u i
  have hs288 := c.s288
  by_cases hvq : (v i : ℝ) ≤ claimQ j u i
  · have hvq' : (v i : ℝ) ≤ u i + claimL j i / 2 := by rw [← hq]; exact hvq
    rw [ite_eq_left hvq] at hz'
    obtain ⟨a, b⟩ := hz'
    constructor
    · have : (u i : ℝ) ≤ v i := he0
      have : u i ≤ v i := by exact_mod_cast this
      omega
    · have : (v i : ℝ) + ellA s₀ ≤ u i + claimL j i := by linarith
      have : v i + (ellA s₀ : ℤ) ≤ u i + (sideLen d j i : ℤ) := by
        have : ((v i + (ellA s₀ : ℤ) : ℤ) : ℝ) ≤ ((u i + (sideLen d j i : ℤ) : ℤ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast this
      omega
  · have hvq' : (u i : ℝ) + claimL j i / 2 < v i := by rw [← hq]; exact not_le.1 hvq
    rw [ite_eq_right hvq] at hz'
    obtain ⟨a, b⟩ := hz'
    constructor
    · have h1 : (u i : ℝ) < v i - ellA s₀ + 1 := by
        rw [not_le] at hvq; linarith
      have : u i < v i - (ellA s₀ : ℤ) + 1 := by
        have : ((u i : ℤ) : ℝ) < (((v i - (ellA s₀ : ℤ) + 1 : ℤ)) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      omega
    · have : v i ≤ u i + (sideLen d j i : ℤ) - 1 := by
        have : ((v i : ℤ) : ℝ) ≤ ((u i + (sideLen d j i : ℤ) - 1 : ℤ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast this
      omega

theorem Ctx.lam_A (c : Ctx j m t s₀ P N) :
    √(2 * (sT s₀ 0 : ℝ) / t) = 1 / P := by
  have hP := c.P0
  have hs0 := c.s0
  rw [coe_sT, c.ht]
  have : 2 * (s₀ ^ 2 / 2 + ((0 : ℕ) : ℝ) * (s₀ ^ 2 / 2000)) / (P ^ 2 * s₀ ^ 2) = (1 / P) ^ 2 := by
    push_cast; field_simp; norm_num
  rw [this, Real.sqrt_sq (by positivity)]

theorem Ctx.pt0_mem_QA (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j)
    (hj : 1 ≤ j) : pt j u t s₀ v 0 ∈ QA j u s₀ v := by
  intro i
  have hb := ellA_bounds c.s288
  have hP := c.P0
  have hs0 := c.s0
  obtain ⟨he0, he1⟩ := claimBox_coord hj hv i
  have hLN : claimL j i ≤ N := by rw [c.hN]; exact claimL_le i
  have hq := claimQ_eq j u i
  have hlam := c.lam_A
  have hf : claimFv j u t v (sT s₀ 0) i = v i + (1 / P) * (claimQ j u i - v i) := by
    rw [claimFv_eq, hlam]
  have hfl := Int.floor_le (claimFv j u t v (sT s₀ 0) i + 1 / 2)
  have hfl2 := Int.lt_floor_add_one (claimFv j u t v (sT s₀ 0) i + 1 / 2)
  set p := pt j u t s₀ v 0 i with hp
  have hp' : p = ⌊claimFv j u t v (sT s₀ 0) i + 1 / 2⌋ := rfl
  rw [← hp'] at hfl hfl2
  rw [hf] at hfl hfl2
  simp only [mA]
  rw [mem_Icc]
  have hLP : claimL j i / 2 ≤ P * s₀ := by nlinarith [c.N2]
  by_cases hvq : (v i : ℝ) ≤ claimQ j u i
  · rw [ite_eq_left hvq]
    have hd0 : 0 ≤ (1 / P) * (claimQ j u i - v i) := by
      apply mul_nonneg (by positivity); linarith
    have hd1 : (1 / P) * (claimQ j u i - v i) ≤ s₀ := by
      rw [hq]
      have : (u i : ℝ) + claimL j i / 2 - v i ≤ claimL j i / 2 := by linarith
      calc (1 / P) * ((u i : ℝ) + claimL j i / 2 - v i) ≤ (1 / P) * (P * s₀) := by
            gcongr
            linarith
        _ = s₀ := by field_simp
    have := partA_up (v := v i) (p := p) (δ := (1 / P) * (claimQ j u i - v i)) (s₀ := s₀)
      (ℓ := ellA s₀) hb.1 hd0 hd1 (by linarith) (by linarith)
    exact this
  · rw [ite_eq_right hvq]
    rw [not_le] at hvq
    have hd0 : (1 / P) * (claimQ j u i - v i) < 0 := by
      apply mul_neg_of_pos_of_neg (by positivity); linarith
    have hd1 : -s₀ ≤ (1 / P) * (claimQ j u i - v i) := by
      rw [hq]
      have : -(claimL j i / 2) ≤ (u i : ℝ) + claimL j i / 2 - v i := by linarith
      calc -s₀ = (1 / P) * (-(P * s₀)) := by field_simp
        _ ≤ (1 / P) * ((u i : ℝ) + claimL j i / 2 - v i) := by
            gcongr
            linarith
    have := partA_down (v := v i) (p := p) (δ := (1 / P) * (claimQ j u i - v i)) (s₀ := s₀)
      (ℓ := ellA s₀) hb.1 hd0 hd1 (by linarith) (by linarith)
    exact ⟨this.1, by omega⟩

end SRW
end ElboimSly
