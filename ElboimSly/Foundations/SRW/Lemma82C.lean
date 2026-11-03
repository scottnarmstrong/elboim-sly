/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Lemma82Pair
public import ElboimSly.Foundations.SRW.Modulus
public import ElboimSly.Foundations.SRW.StoppedPosition
public import Mathlib

/-!
# The SRW content of Lemma 8.2: part (c)

SRW content of Lemma 8.2 (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- Exponential growth beats polynomials. -/
theorem exists_poly_le_pow {r : ℝ} (hr : 1 < r) (C : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, 64 * ((n : ℝ) ^ 4 + n + C) ≤ r ^ n := by
  have h4 := tendsto_pow_const_div_const_pow_of_one_lt 4 hr
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have hinf : Tendsto (fun n : ℕ => r ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hr
  have h0 : Tendsto (fun n : ℕ => C / r ^ n) atTop (𝓝 0) := hinf.const_div_atTop C
  have hs := (h4.add h1).add h0
  simp only [add_zero, pow_one] at hs
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hs).2 (1 / 64) (by norm_num))
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  have hrn : 0 < r ^ n := pow_pos (by linarith) n
  have e : (n : ℝ) ^ 4 / r ^ n + (n : ℝ) / r ^ n + C / r ^ n = ((n : ℝ) ^ 4 + n + C) / r ^ n := by
    ring
  rw [e, div_lt_iff₀ hrn] at this
  linarith

/-- The threshold `n_C(d)`. -/
noncomputable def lem82nC (d : ℕ) : ℕ :=
  max 4 (Classical.choose (exists_poly_le_pow (r := 361 / 360) (by norm_num) (36 * d)))

theorem four_le_lem82nC (d : ℕ) : 4 ≤ lem82nC d := le_max_left _ _

theorem lem82nC_spec (d : ℕ) {n : ℕ} (hn : lem82nC d ≤ n) :
    64 * ((n : ℝ) ^ 4 + n + 36 * d) ≤ (361 / 360 : ℝ) ^ n :=
  Classical.choose_spec (exists_poly_le_pow (r := 361 / 360) (by norm_num) (36 * (d : ℝ))) n
    (le_trans (le_max_right _ _) hn)

theorem modulus_bound_num {d : ℕ} (hd : 1 ≤ d) {n : ℕ} (hn : lem82nC d ≤ n) {t₀ : ℝ}
    (_ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) :
    (lem82T n t₀ / (3.6 : ℝ) ^ n + 1) *
      (4 * d * Real.exp (-min (((1.9 : ℝ) ^ n) ^ 2 / (64 * (3.6 : ℝ) ^ n)) ((1.9 : ℝ) ^ n / 4))) ≤
      Real.exp (-(n : ℝ) ^ 4) := by
  have hn4 : 4 ≤ n := le_trans (four_le_lem82nC d) hn
  have hspec := lem82nC_spec d hn
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  set r : ℝ := 361 / 360 with hr
  have hr1 : 1 < r := by rw [hr]; norm_num
  have h36 : (0 : ℝ) < (3.6 : ℝ) ^ n := by positivity
  -- T bound
  have hT : lem82T n t₀ ≤ 8 * 4 ^ n / 256 := by
    unfold lem82T
    have hn4' : (256 : ℝ) ≤ (n : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 16), sq_nonneg (n : ℝ)]
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    rw [show 2 * (4 ^ n * t₀ / (n : ℝ) ^ 4) = 2 * t₀ * 4 ^ n / (n : ℝ) ^ 4 by ring,
      div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hratio : (4 : ℝ) ^ n / 3.6 ^ n = (10 / 9) ^ n := by
    rw [← div_pow]; congr 1; norm_num
  have h109 : (1 : ℝ) ≤ (10 / 9) ^ n := one_le_pow₀ (by norm_num)
  have hM : lem82T n t₀ / (3.6 : ℝ) ^ n + 1 ≤ 2 * (10 / 9) ^ n := by
    have : lem82T n t₀ / (3.6 : ℝ) ^ n ≤ 8 * (10 / 9) ^ n / 256 := by
      rw [div_le_iff₀ h36]
      calc lem82T n t₀ ≤ 8 * 4 ^ n / 256 := hT
        _ = 8 * ((4 : ℝ) ^ n / 3.6 ^ n) / 256 * 3.6 ^ n := by field_simp
        _ = _ := by rw [hratio]
    linarith
  -- the minimum
  have hmin : r ^ n / 64 ≤ min (((1.9 : ℝ) ^ n) ^ 2 / (64 * (3.6 : ℝ) ^ n)) ((1.9 : ℝ) ^ n / 4) := by
    refine le_min ?_ ?_
    · have : ((1.9 : ℝ) ^ n) ^ 2 / (64 * (3.6 : ℝ) ^ n) = r ^ n / 64 := by
        have e1 : ((1.9 : ℝ) ^ n) ^ 2 = (3.61 : ℝ) ^ n := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have e2 : r ^ n = (3.61 : ℝ) ^ n / 3.6 ^ n := by
          rw [hr, ← div_pow]; norm_num
        rw [e1, e2]; field_simp
      rw [this]
    · have h1 : r ^ n ≤ (1.9 : ℝ) ^ n := pow_le_pow_left₀ (by linarith) (by rw [hr]; norm_num) n
      have h2 : (0 : ℝ) < (1.9 : ℝ) ^ n := by positivity
      linarith
  have hexp : Real.exp (-min (((1.9 : ℝ) ^ n) ^ 2 / (64 * (3.6 : ℝ) ^ n)) ((1.9 : ℝ) ^ n / 4)) ≤
      Real.exp (-(r ^ n / 64)) := Real.exp_le_exp.2 (by linarith)
  have hd' : (0 : ℝ) ≤ 4 * d := by positivity
  have h109e : (10 / 9 : ℝ) ^ n ≤ Real.exp ((n : ℝ) / 9) := by
    have : (10 / 9 : ℝ) ≤ Real.exp (1 / 9) := by
      have := Real.add_one_le_exp (1 / 9 : ℝ); linarith
    calc (10 / 9 : ℝ) ^ n ≤ (Real.exp (1 / 9)) ^ n := pow_le_pow_left₀ (by norm_num) this n
      _ = Real.exp ((n : ℝ) / 9) := by rw [← Real.exp_nat_mul]; ring_nf
  have hdd : (4 * (d : ℝ)) * 2 ≤ Real.exp (36 * d) := by
    have := Real.add_one_le_exp (36 * (d : ℝ))
    have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  calc (lem82T n t₀ / (3.6 : ℝ) ^ n + 1) *
        (4 * d * Real.exp (-min (((1.9 : ℝ) ^ n) ^ 2 / (64 * (3.6 : ℝ) ^ n)) ((1.9 : ℝ) ^ n / 4)))
      ≤ (2 * (10 / 9) ^ n) * (4 * d * Real.exp (-(r ^ n / 64))) := by gcongr
    _ = ((4 * (d : ℝ)) * 2) * (10 / 9) ^ n * Real.exp (-(r ^ n / 64)) := by ring
    _ ≤ Real.exp (36 * d) * Real.exp ((n : ℝ) / 9) * Real.exp (-(r ^ n / 64)) := by gcongr
    _ = Real.exp (36 * d + (n : ℝ) / 9 + -(r ^ n / 64)) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-(n : ℝ) ^ 4) := by
        apply Real.exp_le_exp.2
        nlinarith

/-- SRW content of Lemma 8.2 (c). -/
theorem lemma82_c [NeZero d] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → PathSpace d} (hX : IsSRW P X) {n : ℕ} (hn : lem82nC d ≤ n) {t₀ : ℝ}
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (Y : Ω → PathSpace d)
    (hYm : Measurable fun ω s => Y ω (min s (lem82T n t₀).toNNReal))
    (hYr : ∀ ω, IsRegularPath fun s => Y ω (min s (lem82T n t₀).toNNReal))
    (hlaw : P.map (fun ω s => Y ω (min s (lem82T n t₀).toNNReal)) =
      P.map (fun ω s => X ω (min s (lem82T n t₀).toNNReal))) :
    P.real {ω | ∃ s s' : ℝ≥0, s ≤ s' ∧ s' ≤ (lem82T n t₀).toNNReal ∧ s' - s ≤ lem82h n ∧
        (1.9 : ℝ) ^ n < ‖Y ω s' - Y ω s‖} ≤ Real.exp (-(n : ℝ) ^ 4) := by
  have := hX.isProbabilityMeasure
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  set Tn : ℝ≥0 := (lem82T n t₀).toNNReal with hTn
  have hn4 : 4 ≤ n := le_trans (four_le_lem82nC d) hn
  have hTpos := lem82T_pos hn4 ht1
  have hTc : (Tn : ℝ) = lem82T n t₀ := Real.coe_toNNReal _ hTpos.le
  obtain ⟨V, hVm, hV⟩ := isRegSet_pair (d := d)
    (fun u v => (1.9 : ℝ) ^ n < ‖v - u‖) Tn (lem82h n)
  -- the event for any stopped regular process
  have key : ∀ {W : Ω → PathSpace d}, (∀ ω, IsRegularPath fun s => W ω (min s Tn)) →
      {ω | ∃ s s' : ℝ≥0, s ≤ s' ∧ s' ≤ Tn ∧ s' - s ≤ lem82h n ∧
        (1.9 : ℝ) ^ n < ‖W ω s' - W ω s‖} =
      (fun ω s => W ω (min s Tn)) ⁻¹' V := by
    intro W hW
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← hV _ (hW ω)]
    constructor
    · rintro ⟨s, s', h1, h2, h3, h4⟩
      refine ⟨s, s', bot_le, h1, h2, h3, ?_⟩
      simpa [min_eq_left (h1.trans h2), min_eq_left h2] using h4
    · rintro ⟨s, s', -, h1, h2, h3, h4⟩
      refine ⟨s, s', h1, h2, h3, ?_⟩
      simpa [min_eq_left (h1.trans h2), min_eq_left h2] using h4
  have hXs : ∀ ω, IsRegularPath fun s => X ω (min s Tn) := fun ω => (hX.2.1 ω).stop Tn
  have hXm : Measurable fun ω s => X ω (min s Tn) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply (min s Tn)).comp hX.1
  have e1 := key hYr
  have e2 := key hXs
  have hP : P {ω | ∃ s s' : ℝ≥0, s ≤ s' ∧ s' ≤ Tn ∧ s' - s ≤ lem82h n ∧
        (1.9 : ℝ) ^ n < ‖Y ω s' - Y ω s‖} =
      P {ω | ∃ s s' : ℝ≥0, s ≤ s' ∧ s' ≤ Tn ∧ s' - s ≤ lem82h n ∧
        (1.9 : ℝ) ^ n < ‖X ω s' - X ω s‖} := by
    rw [e1, e2, ← Measure.map_apply hYm hVm, ← Measure.map_apply hXm hVm, hlaw]
  rw [measureReal_def, hP, ← measureReal_def]
  have hmod := hX.modulus Tn (lem82h n) (by rw [← NNReal.coe_pos, coe_lem82h]; positivity)
    (a := (1.9 : ℝ) ^ n) (by positivity)
  refine le_trans (measureReal_mono ?_) (hmod.trans ?_)
  · rintro ω ⟨s, s', h1, h2, h3, h4⟩
    refine ⟨s, s', h1, h2, h3, ?_⟩
    have : ‖X ω s' - X ω s‖ = ‖X ω s' - X ω s‖ := rfl
    exact h4.le
  · have hnum := modulus_bound_num hd1 hn ht1 ht4
    rw [coe_lem82h, hTc]
    have h64 : (64 : ℝ) * (3.6 : ℝ) ^ n = 64 * (lem82h n : ℝ) := by rw [coe_lem82h]
    simpa [coe_lem82h] using hnum

end SRW
end ElboimSly
