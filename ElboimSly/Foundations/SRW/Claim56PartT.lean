/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56PartA
public import Mathlib

/-!
# Claim 5.6, event `𝓑_0`, Part T (`[τ/2, 0.6 τ]`)
-/

@[expose] public section

open Set
open scoped NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {j m : ℕ} {t s₀ P N : ℝ}

/-- `ℓ_T = ⌊r₀ / 4⌋ = ⌊√τ / 128⌋`. -/
noncomputable def ellT (s₀ : ℝ) : ℕ := ⌊s₀ / 128⌋₊

/-- The box of step `k`: a cube around `p_k`. -/
noncomputable def QT (j : ℕ) (u : Fin d → ℤ) (t s₀ : ℝ) (v : Fin d → ℤ) (k : ℕ) :
    Set (Fin d → ℤ) :=
  boxSet (fun i => pt j u t s₀ v k i - ellT s₀) (fun _ => 2 * ellT s₀ + 1)

theorem ellT_bounds (hs : 288 ≤ s₀) : s₀ / 128 - 1 < (ellT s₀ : ℝ) ∧ (ellT s₀ : ℝ) ≤ s₀ / 128 := by
  unfold ellT
  have h1 := Nat.floor_le (show 0 ≤ s₀ / 128 by linarith)
  have h2 := Nat.lt_floor_add_one (s₀ / 128)
  constructor <;> linarith

theorem sT_le (c : Ctx j m t s₀ P N) {k : ℕ} (hk : k ≤ 200) : (sT s₀ k : ℝ) ≤ t / 2 := by
  rw [coe_sT, c.ht]
  have hk' : (k : ℝ) ≤ 200 := by exact_mod_cast hk
  have hP8 := c.P8
  have hP2 : 64 ≤ P ^ 2 := by nlinarith
  have h1 : (k : ℝ) * (s₀ ^ 2 / 2000) ≤ 200 * (s₀ ^ 2 / 2000) := by gcongr
  have h2 : 0 ≤ s₀ ^ 2 * (P ^ 2 - 64) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

theorem sT_ge (s₀ : ℝ) (k : ℕ) : s₀ ^ 2 / 2 ≤ (sT s₀ k : ℝ) := by
  rw [coe_sT]
  have : (0 : ℝ) ≤ k * (s₀ ^ 2 / 2000) := by positivity
  linarith

theorem Ctx.pt_step (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j) (hj : 1 ≤ j)
    {k : ℕ} (hk : k + 1 ≤ 200) (i : Fin d) :
    |(pt j u t s₀ v (k + 1) i : ℝ) - pt j u t s₀ v k i| ≤ ellT s₀ := by
  have hs0 := c.s0
  have hlip := c.fv_lip u v hv hj (s := sT s₀ (k + 1)) (s' := sT s₀ k) (sT_ge s₀ k)
    (by rw [sT_succ]; exact le_self_add) (sT_le c hk) i
  have e : ((sT s₀ (k + 1) : ℝ≥0) : ℝ) - (sT s₀ k : ℝ≥0) = s₀ ^ 2 / 2000 := by
    rw [sT_succ]; push_cast; rw [coe_dlt]; ring
  rw [e] at hlip
  have e2 : s₀ ^ 2 / 2000 / s₀ = s₀ / 2000 := by field_simp
  rw [e2] at hlip
  have c1 := pt_close j u t s₀ v (k + 1) i
  have c2 := pt_close j u t s₀ v k i
  have hb := ellT_bounds c.s288
  rw [abs_le] at *
  have := c.s288
  constructor <;> linarith [hlip.1, hlip.2, c1.1, c1.2, c2.1, c2.2, hb.1]

theorem mem_cube_iff (z p : ℤ) (ℓ : ℕ) :
    z ∈ Icc (p - ℓ) (p - ℓ + ((2 * ℓ + 1 : ℕ) : ℤ) - 1) ↔ |z - p| ≤ ℓ := by
  rw [mem_Icc, abs_le]
  push_cast
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> omega

theorem mem_QT_iff (j : ℕ) (u : Fin d → ℤ) (t s₀ : ℝ) (v : Fin d → ℤ) (k : ℕ)
    (z : Fin d → ℤ) : z ∈ QT j u t s₀ v k ↔ ∀ i, |z i - pt j u t s₀ v k i| ≤ ellT s₀ := by
  unfold QT boxSet
  simp only [mem_ofPred_eq]
  exact forall_congr' fun i => mem_cube_iff _ _ _

theorem Ctx.pt_mem_QT (u v : Fin d → ℤ) (k : ℕ) (_hs : 288 ≤ s₀) :
    pt j u t s₀ v k ∈ QT j u t s₀ v k := by
  rw [mem_QT_iff]; intro i; simp

theorem Ctx.pt_succ_mem_QT (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j)
    (hj : 1 ≤ j) {k : ℕ} (hk : k + 1 ≤ 200) : pt j u t s₀ v (k + 1) ∈ QT j u t s₀ v k := by
  rw [mem_QT_iff]
  intro i
  have := c.pt_step u v hv hj hk i
  have h3 : |pt j u t s₀ v (k + 1) i - pt j u t s₀ v k i| ≤ (ellT s₀ : ℤ) := by
    have : ((|pt j u t s₀ v (k + 1) i - pt j u t s₀ v k i| : ℤ) : ℝ) ≤ ((ellT s₀ : ℤ) : ℝ) := by
      rw [Int.cast_abs]; push_cast; exact this
    exact_mod_cast this
  exact h3

theorem Ctx.QT_sub (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j) (hj : 1 ≤ j)
    {k : ℕ} (hk : k ≤ 200) : QT j u t s₀ v k ⊆ claimBox u j := by
  intro z hz i
  rw [mem_QT_iff] at hz
  have hzi := hz i
  have hmar := c.fv_margin u v hv hj (s := sT s₀ k) (sT_ge s₀ k) (sT_le c hk) i
  have hcl := pt_close j u t s₀ v k i
  have hb := ellT_bounds c.s288
  have hs := c.s288
  have hsl := sideLen_cast (d := d) j hj i
  have hLeq : ((sideLen d j i : ℕ) : ℝ) = claimL j i := by unfold claimL; rw [hsl]
  have hzr : |(z i : ℝ) - pt j u t s₀ v k i| ≤ ellT s₀ := by
    have : ((|z i - pt j u t s₀ v k i| : ℤ) : ℝ) ≤ ((ellT s₀ : ℤ) : ℝ) := by exact_mod_cast hzi
    rw [Int.cast_abs] at this; push_cast at this; exact this
  rw [abs_le] at hzr hcl
  rw [mem_Icc]
  constructor
  · have : (u i : ℝ) < z i := by linarith [hzr.1, hcl.1, hcl.2, hmar.1, hb.2]
    have : u i < z i := by exact_mod_cast this
    omega
  · have : (z i : ℝ) < u i + claimL j i := by linarith [hzr.2, hcl.1, hcl.2, hmar.2, hb.2]
    have : z i < u i + (sideLen d j i : ℤ) := by
      have : (z i : ℝ) < ((u i + (sideLen d j i : ℤ) : ℤ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this
    omega

theorem Ctx.time_T (c : Ctx j m t s₀ P N) :
    ((2 * ellT s₀ + 1 : ℕ) : ℝ) ^ 2 / 16 ≤ (dlt s₀ : ℝ) ∧
      (dlt s₀ : ℝ) ≤ 16 * ((2 * ellT s₀ + 1 : ℕ) : ℝ) ^ 2 := by
  have hb := ellT_bounds c.s288
  have hs := c.s288
  rw [coe_dlt]
  push_cast
  constructor <;> nlinarith [hb.1, hb.2]

theorem Ctx.time_A (c : Ctx j m t s₀ P N) :
    (ellA s₀ : ℝ) ^ 2 / 16 ≤ (rhoA s₀ : ℝ) ∧ (rhoA s₀ : ℝ) ≤ 16 * (ellA s₀ : ℝ) ^ 2 := by
  have hb := ellA_bounds c.s288
  have hs := c.s288
  rw [coe_rhoA]
  constructor <;> nlinarith [hb.1, hb.2]

theorem Ctx.close_T (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j) (hj : 1 ≤ j)
    {k : ℕ} (hk : k + 1 ≤ 200) {z : Fin d → ℤ} (hz : z ∈ QT j u t s₀ v k) {s : ℝ≥0}
    (hs1 : sT s₀ k ≤ s) (hs2 : s ≤ sT s₀ (k + 1)) (i : Fin d) :
    |(z i : ℝ) - claimFv j u t v s i| ≤ s₀ / 32 := by
  rw [mem_QT_iff] at hz
  have hzi := hz i
  have hzr : |(z i : ℝ) - pt j u t s₀ v k i| ≤ ellT s₀ := by
    have : ((|z i - pt j u t s₀ v k i| : ℤ) : ℝ) ≤ ((ellT s₀ : ℤ) : ℝ) := by exact_mod_cast hzi
    rw [Int.cast_abs] at this; push_cast at this; exact this
  have hcl := pt_close j u t s₀ v k i
  have hlip := c.fv_lip u v hv hj (s := s) (s' := sT s₀ k) (sT_ge s₀ k) hs1
    ((by exact_mod_cast hs2 : (s : ℝ) ≤ sT s₀ (k + 1)).trans (sT_le c hk)) i
  have hs0 := c.s0
  have hdiff : (s : ℝ) - (sT s₀ k : ℝ≥0) ≤ s₀ ^ 2 / 2000 := by
    have : ((sT s₀ (k + 1) : ℝ≥0) : ℝ) - (sT s₀ k : ℝ≥0) = s₀ ^ 2 / 2000 := by
      rw [sT_succ]; push_cast; rw [coe_dlt]; ring
    have h2 : (s : ℝ) ≤ sT s₀ (k + 1) := by exact_mod_cast hs2
    linarith
  have hlip2 : |claimFv j u t v s i - claimFv j u t v (sT s₀ k) i| ≤ s₀ / 2000 := by
    refine hlip.trans ?_
    rw [div_le_iff₀ hs0]
    have : s₀ / 2000 * s₀ = s₀ ^ 2 / 2000 := by ring
    linarith
  have hb := ellT_bounds c.s288
  have hs := c.s288
  rw [abs_le] at *
  constructor <;> linarith [hzr.1, hzr.2, hcl.1, hcl.2, hlip2.1, hlip2.2, hb.2]

end SRW
end ElboimSly
