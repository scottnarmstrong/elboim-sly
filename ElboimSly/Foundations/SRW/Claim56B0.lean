/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56B0Path
public import Mathlib

/-!
# Claim 5.6, event `𝓑_0`

ES22 Claim 5.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {j m : ℕ} {t s₀ P N : ℝ}

theorem prod_ge_const {L s₀ : ℝ} (hL : 1 ≤ L) (hL2 : L ≤ 2 * s₀) :
    cBox ^ d / (2 * s₀) ^ (d * CBox) ≤ ∏ _i : Fin d, cBox / L ^ CBox := by
  have hc := cBox_pos
  have h1 : cBox / (2 * s₀) ^ CBox ≤ cBox / L ^ CBox :=
    div_le_div_of_nonneg_left hc.le (pow_pos (by linarith) _)
      (pow_le_pow_left₀ (by linarith) hL2 _)
  calc cBox ^ d / (2 * s₀) ^ (d * CBox) = (cBox / (2 * s₀) ^ CBox) ^ d := by
        rw [div_pow, ← pow_mul, mul_comm CBox d]
    _ ≤ (cBox / L ^ CBox) ^ d := pow_le_pow_left₀ (div_nonneg hc.le (pow_nonneg (by linarith) _)) h1 d
    _ = ∏ _i : Fin d, cBox / L ^ CBox := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem Ctx.kernel_lb (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j)
    (hj : 1 ≤ j) {k : ℕ} (hk : k ≤ 200) :
    cBox ^ d / (2 * s₀) ^ (d * CBox) ≤
      kernel (Qww j u t s₀ v k) (rww s₀ k) (xww j u t s₀ v k) (zww j u t s₀ v k) := by
  have hs := c.s288
  cases k with
  | zero =>
    have hb := ellA_bounds hs
    have hL1 : 1 ≤ ellA s₀ := by
      have : (1 : ℝ) ≤ ellA s₀ := by linarith [hb.1]
      exact_mod_cast this
    have ht := c.time_A
    have := box_d (mA j u s₀ v) (fun _ => ellA s₀) (fun _ => hL1) (y := v) (z := pt j u t s₀ v 0)
      (v_mem_QA u v s₀ hs) (c.pt0_mem_QA u v hv hj) (r := rhoA s₀) (fun _ => ht.1) (fun _ => ht.2)
    refine le_trans ?_ this
    exact prod_ge_const (by exact_mod_cast hL1) (by linarith [hb.2])
  | succ k =>
    have hb := ellT_bounds hs
    have hL1 : 1 ≤ 2 * ellT s₀ + 1 := by omega
    have ht := c.time_T
    have := box_d (fun i => pt j u t s₀ v k i - ellT s₀) (fun _ => 2 * ellT s₀ + 1)
      (fun _ => hL1) (y := pt j u t s₀ v k) (z := pt j u t s₀ v (k + 1))
      (Ctx.pt_mem_QT u v k hs) (c.pt_succ_mem_QT u v hv hj hk) (r := dlt s₀) (fun _ => ht.1)
      (fun _ => ht.2)
    refine le_trans ?_ this
    refine prod_ge_const (by exact_mod_cast hL1) ?_
    push_cast
    linarith [hb.2]

/-- ES22 Claim 5.6. -/
theorem claim56_B0 {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω} {Z : Ω → PathSpace d}
    (hZ : IsSRW P' Z) (G : Claim56Geom d j t m) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j) :
    ENNReal.ofReal (cBox ^ (201 * d) / (2 * √(claimTau m t)) ^ (201 * d * CBox)) ≤
      P' {ω | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + Z ω s ∈ claimBox u j) ∧
        ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
          ‖(fun i => (((v + Z ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} := by
  obtain ⟨s₀, P, N, c⟩ := G.ctx
  have hj := G.j_pos
  have := hZ.isProbabilityMeasure
  have hs : s₀ = √(claimTau m t) := c.hs
  have hτ0 : 0 ≤ claimTau m t := by
    unfold claimTau
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    exact div_nonneg (h4.trans G.four_m) h4
  have hτ : claimTau m t = s₀ ^ 2 := by rw [hs, Real.sq_sqrt hτ0]
  have hr0 : claimR0 m t = s₀ / 32 := by unfold claimR0; rw [← hs]
  have hc0 : 0 ≤ cBox ^ d / (2 * s₀) ^ (d * CBox) := by
    have := c.s288; have := cBox_pos; positivity
  set c0 := cBox ^ d / (2 * s₀) ^ (d * CBox) with hc0def
  have hchain := hZ.real_chain (Qww j u t s₀ v) (rww s₀) (xww j u t s₀ v) (zww j u t s₀ v) 201
    (fun k => if k ≤ 200 then c0 else 0) (fun k => by split_ifs <;> positivity)
    (fun k => by
      split_ifs with hk
      · exact c.kernel_lb u v hv hj hk
      · exact kernel_nonneg _ _ _ _)
  have hprod : ∏ k ∈ Finset.range 201, (if k ≤ 200 then c0 else 0) = c0 ^ 201 := by
    rw [Finset.prod_congr rfl (fun k hk => ite_eq_left (by have := Finset.mem_range.1 hk; omega))]
    simp
  rw [hprod] at hchain
  have hsub : {ω | Z ω ∈ Gfrom (rww s₀) (kerV (Qww j u t s₀ v) (rww s₀) (xww j u t s₀ v)
      (zww j u t s₀ v)) 0 201} ⊆
      {ω | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + Z ω s ∈ claimBox u j) ∧
        ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
          ‖(fun i => (((v + Z ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} := by
    intro ω hω
    obtain ⟨hA, hB⟩ := c.path_B0 u v hv hj (hZ.2.1 ω) hω
    have e1 : (sT s₀ 200 : ℝ) = 0.6 * claimTau m t := by
      rw [coe_sT, hτ]; push_cast; ring
    have e2 : (rhoA s₀ : ℝ) = 0.5 * claimTau m t := by rw [coe_rhoA, hτ]; ring
    refine ⟨fun s hs' => hA s (by rw [← NNReal.coe_le_coe, e1]; exact hs'), fun s hs1 hs2 => ?_⟩
    rw [hr0]
    refine (pi_norm_le_iff_of_nonneg (by have := c.s288; positivity)).2 fun i => ?_
    have := hB s (by rw [← NNReal.coe_le_coe, e2]; exact hs1)
      (by rw [← NNReal.coe_le_coe, e1]; exact hs2) i
    simpa [Real.norm_eq_abs] using this
  have h1 : c0 ^ 201 ≤ P'.real {ω | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t →
        v + Z ω s ∈ claimBox u j) ∧
        ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
          ‖(fun i => (((v + Z ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} :=
    hchain.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
  have e3 : c0 ^ 201 = cBox ^ (201 * d) / (2 * √(claimTau m t)) ^ (201 * d * CBox) := by
    rw [hc0def, ← hs, div_pow, ← pow_mul, ← pow_mul, show d * 201 = 201 * d by ring,
      show d * CBox * 201 = 201 * d * CBox by ring]
  rw [← e3]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P' _)]
  exact ENNReal.ofReal_le_ofReal h1

end SRW
end ElboimSly
