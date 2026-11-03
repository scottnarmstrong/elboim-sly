/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56Coord
public import ElboimSly.Foundations.SRW.Claim56Real
public import Mathlib

/-!
# Context and basic estimates for Claim 5.6, event `𝓑_0`
-/

@[expose] public section

open Set
open scoped NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The numerical context: `s₀ = √τ`, `P = 2^m`, `N = 2^j`, `t = P² s₀²`. -/
structure Ctx (j m : ℕ) (t s₀ P N : ℝ) : Prop where
  s288 : 288 ≤ s₀
  P8 : 8 ≤ P
  ht : t = P ^ 2 * s₀ ^ 2
  N1 : P * s₀ ≤ N
  N2 : N ≤ 2 * P * s₀
  hP : P = 2 ^ m
  hN : N = 2 ^ j
  hs : s₀ = √(claimTau m t)

theorem Claim56Geom.ctx {j m : ℕ} {t : ℝ} (G : Claim56Geom d j t m) :
    ∃ s₀ P N : ℝ, Ctx j m t s₀ P N := by
  obtain ⟨s, P, N, hs, hP, hN, h288, hP8, hts, hN1, hN2, hτ⟩ := G.facts
  exact ⟨s, P, N, ⟨h288, hP8, hts, hN1, hN2, hP, hN, hs⟩⟩

/-- Start times, window lengths, rounded points. -/
noncomputable def rhoA (s₀ : ℝ) : ℝ≥0 := (s₀ ^ 2 / 2).toNNReal

noncomputable def dlt (s₀ : ℝ) : ℝ≥0 := (s₀ ^ 2 / 2000).toNNReal

noncomputable def sT (s₀ : ℝ) (k : ℕ) : ℝ≥0 := rhoA s₀ + k * dlt s₀

theorem coe_rhoA {s₀ : ℝ} : (rhoA s₀ : ℝ) = s₀ ^ 2 / 2 := Real.coe_toNNReal _ (by positivity)

theorem coe_dlt {s₀ : ℝ} : (dlt s₀ : ℝ) = s₀ ^ 2 / 2000 := Real.coe_toNNReal _ (by positivity)

theorem coe_sT (s₀ : ℝ) (k : ℕ) : (sT s₀ k : ℝ) = s₀ ^ 2 / 2 + k * (s₀ ^ 2 / 2000) := by
  unfold sT; push_cast; rw [coe_rhoA, coe_dlt]

theorem sT_succ (s₀ : ℝ) (k : ℕ) : sT s₀ (k + 1) = sT s₀ k + dlt s₀ := by
  unfold sT; push_cast; ring

theorem sT_zero (s₀ : ℝ) : sT s₀ 0 = rhoA s₀ := by simp [sT]

/-- The rounded point `p_k = round f_v(s_k)`. -/
noncomputable def pt (j : ℕ) (u : Fin d → ℤ) (t s₀ : ℝ) (v : Fin d → ℤ) (k : ℕ) : Fin d → ℤ :=
  fun i => ⌊claimFv j u t v (sT s₀ k) i + 1 / 2⌋

theorem pt_close (j : ℕ) (u : Fin d → ℤ) (t s₀ : ℝ) (v : Fin d → ℤ) (k : ℕ) (i : Fin d) :
    |(pt j u t s₀ v k i : ℝ) - claimFv j u t v (sT s₀ k) i| ≤ 1 / 2 := by
  unfold pt
  have h1 := Int.floor_le (claimFv j u t v (sT s₀ k) i + 1 / 2)
  have h2 := Int.lt_floor_add_one (claimFv j u t v (sT s₀ k) i + 1 / 2)
  rw [abs_le]; constructor <;> linarith

variable {j m : ℕ} {t s₀ P N : ℝ}

theorem Ctx.P0 (c : Ctx j m t s₀ P N) : 0 < P := by linarith [c.P8]

theorem Ctx.s0 (c : Ctx j m t s₀ P N) : 0 < s₀ := by linarith [c.s288]

/-- The Lipschitz bound for `f_v` between two times in `[τ/2, ∞)` within the range. -/
theorem Ctx.fv_lip (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j)
    (hj : 1 ≤ j) {s s' : ℝ≥0} (hs' : s₀ ^ 2 / 2 ≤ s') (hss : s' ≤ s)
    (_hsupp : (s : ℝ) ≤ t / 2) (i : Fin d) :
    |claimFv j u t v s i - claimFv j u t v s' i| ≤ ((s : ℝ) - s') / s₀ := by
  have hP := c.P0
  have hs0 := c.s0
  have ht := c.ht
  rw [claimFv_eq, claimFv_eq, claimQ_eq]
  obtain ⟨he0, he1⟩ := claimBox_coord hj hv i
  have hLN := claimL_le (j := j) i
  have hLN' : claimL j i ≤ N := by rw [c.hN]; exact hLN
  have hlip := lam_lip hP hs0 hs' (by exact_mod_cast hss : (s' : ℝ) ≤ s)
  rw [← ht] at hlip
  have hle : √(2 * (s' : ℝ) / t) ≤ √(2 * (s : ℝ) / t) := by
    apply Real.sqrt_le_sqrt
    have : 0 < t := by rw [ht]; positivity
    gcongr
  have hf := f_lip (P := P) (s₀ := s₀) (N := N) (L := claimL j i) (e := v i - u i)
    (lam := √(2 * (s : ℝ) / t)) (lam' := √(2 * (s' : ℝ) / t)) (s := s) (s' := s') hP hs0 c.N2
    hLN' (by linarith) (by linarith) hlip hle (by exact_mod_cast hss)
  have e : v i + √(2 * (s : ℝ) / t) * ((u i : ℝ) + claimL j i / 2 - v i) -
      (v i + √(2 * (s' : ℝ) / t) * ((u i : ℝ) + claimL j i / 2 - v i)) =
      √(2 * (s : ℝ) / t) * (claimL j i / 2 - (v i - u i)) -
        √(2 * (s' : ℝ) / t) * (claimL j i / 2 - (v i - u i)) := by ring
  rw [e]
  exact hf

theorem Ctx.fv_margin (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j)
    (hj : 1 ≤ j) {s : ℝ≥0} (hs : s₀ ^ 2 / 2 ≤ s) (hsupp : (s : ℝ) ≤ t / 2) (i : Fin d) :
    (u i : ℝ) + s₀ / 4 ≤ claimFv j u t v s i ∧
      claimFv j u t v s i ≤ (u i : ℝ) + claimL j i - s₀ / 4 := by
  have hP := c.P0
  have hs0 := c.s0
  have ht := c.ht
  rw [claimFv_eq, claimQ_eq]
  obtain ⟨he0, he1⟩ := claimBox_coord hj hv i
  have hL1 : N / 2 ≤ claimL j i := by
    have := claimL_ge (j := j) i
    rw [c.hN]; exact this
  have hlam0 := lam_ge hP hs0 hs
  have hlam1 := lam_le_one hP hs0 (s := s) (by rw [← ht]; exact hsupp)
  rw [← ht] at hlam0 hlam1
  have := margin_coord (P := P) (s₀ := s₀) (N := N) (L := claimL j i) (e := v i - u i)
    (lam := √(2 * (s : ℝ) / t)) c.P8 c.s288 c.N1 hL1 (by linarith) (by linarith) hlam0 hlam1
  constructor <;> nlinarith [this.1, this.2]

end SRW
end ElboimSly
