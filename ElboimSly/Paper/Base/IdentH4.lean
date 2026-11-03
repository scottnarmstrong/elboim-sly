/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.IdentH3
public import ElboimSly.Paper.Base.BaseH4
public import ElboimSly.Frozen.Defs.IndH4
public import Mathlib

/-!
# (H4) at the base

(8.1)--(8.3) and (H2)--(H4) at the base (f).

* `regen_restrict_law`: for `T ≤ β`, the law of the regenerated walk on `[0,T]` is the law of an
  SRW on `[0,T]`.
* `base_H4_coupling`: `admitsBMCoupling` for the law of the regenerated walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Restriction from `[0,b]` to `[0,T]`. -/
def restrictSub (b T : ℝ≥0) (hT : T ≤ b) (g : Set.Iic b → Fin d → ℤ) :
    Set.Icc (0 : ℝ≥0) T → Fin d → ℤ := fun t => g ⟨t, t.2.2.trans hT⟩

theorem measurable_restrictSub (b T : ℝ≥0) (hT : T ≤ b) : Measurable (restrictSub (d := d) b T hT) :=
  measurable_pi_iff.2 fun _t => measurable_pi_apply _

/-- For `T ≤ β`, the law of the regenerated walk on `[0,T]` is the law of an SRW on `[0,T]`. -/
theorem regen_restrict_law {Ω Ω₀ : Type} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {P : Measure Ω} {P₀ : Measure Ω₀} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {T : ℝ≥0} (hT : (T : ℝ) ≤ β) {Z₀ : Ω₀ → PathSpace d} (hZ₀ : IsSRW P₀ Z₀) :
    P.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) =
      P₀.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) => Z₀ ω t) := by
  obtain ⟨Ωd, mΩd, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir d)
  have hcan := canonical_isSRW hN₀
  have hTb : T ≤ β.toNNReal := by
    rw [← NNReal.coe_le_coe]; simpa [Real.coe_toNNReal _ (Fact.out : 0 < β).le] using hT
  set b := β.toNNReal with hb
  have hν := Roots.isPoissonPointProcess_copyEnv hN 0
  have hgood : ∀ᵐ ω ∂P, Good (copyEnv (N ω) 0) := ae_good hν
  have hlaw := cyc_srw_short_law hν hN₀ 0 0
  have hR : Measurable fun ω => restrictIic b (cycPath (copyEnv (N ω) 0)) :=
    (measurable_restrictIic b).comp (measurable_cycPath hν.measurable)
  have hlaw' : P.map (fun ω => restrictIic b (cycPath (copyEnv (N ω) 0))) =
      Pd.map (fun ω => restrictIic b (canonical d N₀ ω)) := by
    rw [← hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    funext s
    simp only [sub_zero]
    exact (cycWalk_eq_cycPath hω s.1).symm
  have hR' : Measurable fun ω => restrictIic b (canonical d N₀ ω) :=
    (measurable_restrictIic b).comp (measurable_canonical hN₀.measurable)
  have hE := measurable_restrictSub (d := d) b T hTb
  have step1 : P.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) =
      P.map (fun ω => restrictSub b T hTb (restrictIic b (cycPath (copyEnv (N ω) 0)))) := by
    refine Measure.map_congr ?_
    filter_upwards [hgood, ae_good_copyEnv hN 1] with ω h0 h1
    funext t
    exact regenWalk_eq_cycPath h0 h1 (t.2.2.trans_eq' rfl |> fun h => (NNReal.coe_le_coe.2 h).trans hT)
  have step2 : P.map (fun ω => restrictSub b T hTb (restrictIic b (cycPath (copyEnv (N ω) 0)))) =
      Pd.map (fun ω => restrictSub b T hTb (restrictIic b (canonical d N₀ ω))) := by
    rw [show (fun ω => restrictSub b T hTb (restrictIic b (cycPath (copyEnv (N ω) 0)))) =
        restrictSub b T hTb ∘ (fun ω => restrictIic b (cycPath (copyEnv (N ω) 0))) from rfl,
      show (fun ω => restrictSub b T hTb (restrictIic b (canonical d N₀ ω))) =
        restrictSub b T hTb ∘ (fun ω => restrictIic b (canonical d N₀ ω)) from rfl,
      ← Measure.map_map hE hR, ← Measure.map_map hE hR', hlaw']
  have step3 : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} {Z₁ : Ω₁ → PathSpace d},
      IsSRW P₁ Z₁ → P₁.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) => Z₁ ω t) =
        (((srwP d).map (srwZ d)).map (restrictSub b T hTb ∘ restrictIic b)) := by
    intro Ω₁ _ P₁ Z₁ hZ₁
    have hm : Measurable (restrictSub (d := d) b T hTb ∘ restrictIic b) :=
      hE.comp (measurable_restrictIic b)
    rw [← hZ₁.map_eq_model, Measure.map_map hm hZ₁.1]
    rfl
  rw [step1, step2, step3 hZ₀, ← step3 hcan]
  rfl

theorem AdmitsBMCoupling.mono_param {T : ℝ≥0} {lawW : Measure (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ)}
    {σ ε ε' η η' : ℝ} (h : AdmitsBMCoupling d T lawW σ ε η) (hε : ε ≤ ε') (hη : η ≤ η') :
    AdmitsBMCoupling d T lawW σ ε' η' := by
  obtain ⟨Q, hQ, h1, h2, h3⟩ := h
  refine ⟨Q, hQ, h1, h2, le_trans (measure_mono ?_) (h3.trans (ENNReal.ofReal_le_ofReal hη))⟩
  intro p hp
  exact (ENNReal.ofReal_le_ofReal hε).trans hp

theorem pow_1000 (a : ℕ) : a ^ 1000 = (a ^ 50) ^ 20 := by rw [← pow_mul]

theorem gen_pow (a b : ℕ) : (a ^ 2 * b ^ 50) ^ 20 = a ^ 40 * b ^ 1000 := by
  rw [mul_pow, ← pow_mul, ← pow_mul]

theorem gen3 (x y c : ℕ) (hc : 1 ≤ c) (a : x ^ 50 ≤ c ^ 2 * y ^ 50) :
    x ^ 1000 ≤ c ^ 41 * y ^ 1000 :=
  calc x ^ 1000 = (x ^ 50) ^ 20 := pow_1000 x
    _ ≤ (c ^ 2 * y ^ 50) ^ 20 := Nat.pow_le_pow_left a _
    _ = c ^ 40 * y ^ 1000 := gen_pow c y
    _ ≤ c ^ 41 * y ^ 1000 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hc (Nat.le_succ 40))

theorem gen2 (x c : ℕ) (a : x ^ 50 ≤ c ^ 157) : x ^ 1000 ≤ c ^ 3140 :=
  calc x ^ 1000 = (x ^ 50) ^ 20 := pow_1000 x
    _ ≤ (c ^ 157) ^ 20 := Nat.pow_le_pow_left a _
    _ = c ^ 3140 := by rw [← pow_mul]

theorem gen4 (x c k : ℕ) (hc : 1 ≤ c) (a : x ^ 50 ≤ c ^ 157) (hk : 3140 ≤ k) :
    x ^ 1000 ≤ c ^ k :=
  (gen2 x c a).trans (pow_le_pow_right₀ hc hk)

theorem pow_thousand_le (n : ℕ) (hn : 77 ≤ n) : n ^ 1000 ≤ 4 ^ (41 * n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have a : (77 : ℕ) ^ 50 ≤ 4 ^ 157 := by norm_num
    exact gen4 77 4 (41 * 77) (by norm_num) a (by norm_num)
  | succ n hn ih =>
    have h1 : (n + 1) * 77 ≤ 78 * n := by omega
    have h2 : ((n + 1) * 77) ^ 1000 ≤ (78 * n) ^ 1000 := pow_le_pow_left₀ (Nat.zero_le _) h1 _
    have h3 : (78 : ℕ) ^ 1000 ≤ 4 ^ 41 * 77 ^ 1000 := by
      have a : (78 : ℕ) ^ 50 ≤ 4 ^ 2 * 77 ^ 50 := by norm_num
      exact gen3 78 77 4 (by norm_num) a
    have h4 : (n + 1) ^ 1000 * 77 ^ 1000 ≤ 4 ^ 41 * n ^ 1000 * 77 ^ 1000 := by
      calc (n + 1) ^ 1000 * 77 ^ 1000 = ((n + 1) * 77) ^ 1000 := (mul_pow _ _ _).symm
        _ ≤ (78 * n) ^ 1000 := h2
        _ = 78 ^ 1000 * n ^ 1000 := by rw [mul_pow]
        _ ≤ 4 ^ 41 * 77 ^ 1000 * n ^ 1000 := mul_le_mul_of_nonneg_right h3 (Nat.zero_le _)
        _ = 4 ^ 41 * n ^ 1000 * 77 ^ 1000 := mul_right_comm _ _ _
    have h5 := Nat.le_of_mul_le_mul_right h4 (by positivity)
    calc (n + 1) ^ 1000 ≤ 4 ^ 41 * n ^ 1000 := h5
      _ ≤ 4 ^ 41 * 4 ^ (41 * n) := Nat.mul_le_mul_left _ ih
      _ = 4 ^ (41 * (n + 1)) := by rw [← pow_add]; ring_nf

theorem pow_ten_le_scale {n : ℕ} (hn : 77 ≤ n) {t₀ : ℝ} (ht : 1 ≤ t₀) :
    (n : ℝ) ^ 10 ≤ (4 ^ n * t₀) ^ (41 / 100 : ℝ) := by
  have h1 : ((n : ℝ) ^ 10) ^ 100 ≤ (((4 : ℝ) ^ n) ^ (41 / 100 : ℝ)) ^ 100 := by
    have e : (((4 : ℝ) ^ n) ^ (41 / 100 : ℝ)) ^ 100 = 4 ^ (41 * n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast]
      congr 1
      push_cast; ring
    rw [e, ← pow_mul]
    have hc : (((n ^ 1000 : ℕ)) : ℝ) ≤ (((4 ^ (41 * n) : ℕ)) : ℝ) :=
      Nat.cast_le.2 (pow_thousand_le n hn)
    rwa [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at hc
  have h2 := le_of_pow_le_pow_left₀ (by norm_num : (100 : ℕ) ≠ 0) (by positivity) h1
  refine h2.trans (Real.rpow_le_rpow (by positivity) ?_ (by norm_num))
  nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) n]

theorem indFailBound_ge {β t₀ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(n : ℝ) ^ 4) ≤ indFailBound β t₀ n := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  unfold indFailBound
  split_ifs
  · exact Real.exp_le_exp.2 (by nlinarith [pow_pos hn0 3])
  · exact Real.exp_le_exp.2 (by nlinarith [pow_pos hn0 2, pow_pos hn0 3])

/-- **(H4) at the base**, (8.1)--(8.3) and (H2)--(H4) at the base (f). -/
theorem base_H4 (d : ℕ) (hd : 1 ≤ d) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → 77 ≤ n → ∀ (β : ℝ) [Fact (0 < β)] (t₀ : ℝ), 1 < t₀ → t₀ ≤ 4 →
      indScale t₀ n ≤ β → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (N : Ω → Measure (ℕ × RingSpace d β)),
        IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P →
          IndH4 P N n t₀ := by
  obtain ⟨n₁, hn₁⟩ := admitsBMCoupling_of_srw_law d hd
  refine ⟨n₁, fun n hn hn77 β _ t₀ ht1 ht4 htβ Ω _ P N hN => ?_⟩
  obtain ⟨Ω₀, mΩ₀, P₀, Z₀, hZ₀⟩ := exists_srw d
  have hscale0 : 0 ≤ indScale t₀ n := by unfold indScale; positivity
  have hscale4 : indScale t₀ n ≤ 4 ^ (n + 1) := by
    unfold indScale; rw [pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) n]
  refine ⟨Real.sqrt 2, by simp, ?_⟩
  have h := hn₁ n hn _ hscale0 hscale4 P₀ Z₀ hZ₀
  have hlaw := regen_restrict_law hN (T := (indScale t₀ n).toNNReal)
    (by rw [Real.coe_toNNReal _ hscale0]; exact htβ) hZ₀
  rw [hlaw]
  refine AdmitsBMCoupling.mono_param h ?_ (indFailBound_ge (by omega))
  have : (n : ℝ) ^ 10 ≤ indScale t₀ n ^ (41 / 100 : ℝ) := by
    unfold indScale; exact pow_ten_le_scale hn77 ht1.le
  simpa [indThetaH] using this

end ElboimSly.Paper

end
