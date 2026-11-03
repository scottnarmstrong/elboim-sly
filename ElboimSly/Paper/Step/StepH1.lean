/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StepH234
public import ElboimSly.Paper.Step.WindowCover
public import ElboimSly.Paper.Heavy.Es4Canon
public import ElboimSly.Paper.Heavy.ThrFinite
public import ElboimSly.Paper.Heavy.ThrE
public import ElboimSly.Paper.Base.H1Arith
public import Mathlib

/-!
# (H1) at level `n` from Theorem 6.1

The induction step, item (H1).

On the event of Theorem 6.1 (`es6_one_of_params`, conditional on `HeavyEscInterface`, the
conclusion of interface with S6), cover `[0, t_n]` by windows of length `t_n^ε`; the
relaxed times then have measure `≥ (0.9 + 1/n) t_n`, i.e. `W|[0,t_n]` is a relaxed path.
`step_H1_of_interface` is a conditional helper (distinct name; the hypothesis `hI` is the §5
interface).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Cyclic

theorem lin_le_two_pow : ∀ n : ℕ, 3 ≤ n → (9 / 10 : ℝ) * n + 2 ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    push_cast
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith

theorem eps_window_le {T ε : ℝ} {n : ℕ} (hn : 3 ≤ n) (hT : (4 : ℝ) ^ n ≤ T) (_hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) : T ^ ε * ((9 / 10) * n + 2) ≤ T := by
  have hT1 : 1 ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT
  have hT0 : 0 ≤ T := by linarith
  have h2 : (2 : ℝ) ^ n ≤ Real.sqrt T := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ T := hT
  have h3 : T ^ ε ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hT1 hε
  calc T ^ ε * ((9 / 10) * n + 2) ≤ Real.sqrt T * Real.sqrt T :=
        mul_le_mul h3 ((lin_le_two_pow n hn).trans h2) (by positivity) (Real.sqrt_nonneg _)
    _ = T := Real.mul_self_sqrt hT0

theorem heavyEps_le {d : ℕ} (hd : 5 ≤ d) : heavyEps d ≤ 1 / 2 := by
  unfold heavyEps
  have : (5 : ℝ) ≤ d := by exact_mod_cast hd
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem heavyEps_nonneg {d : ℕ} : 0 ≤ heavyEps d := by
  unfold heavyEps; positivity

/-- (H1) at level `n`, from Theorem 6.1 (`es6_one_of_params`), conditional on `HeavyEscInterface`. -/
theorem step_H1_of_interface {d : ℕ} {β : ℝ} [Fact (0 < β)] {E : HeavyEscConsts} (hd : 5 ≤ d)
    {n₁ n : ℕ} {t₀ : ℝ} (hn₁ : 8 * d ≤ n₁) (h : StepRegime d n₁ β n t₀)
    (hβ2 : (4 : ℝ) ^ (n₁ + 2) ≤ β) (hβ14 : (10 : ℝ) ^ 14 ≤ β) (hβ5 : E.beta5 ≤ β)
    (hI : HeavyEscInterface d β E n₁ n t₀) (hN6 : heavyN6 d n₁ E ≤ n) (hn3 : 3 ≤ n)
    (hc : 1 / heavyC6 d E ≤ n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    IndH1 P N n t₀ := by
  have := hN.isProbabilityMeasure
  have hlt : n₁ < n := by have := stepRegime_level_le h hβ2; omega
  have hp : Es4Params d β n₁ n t₀ :=
    ⟨hd, hn₁, hlt, hβ14, h.2.2.2.1.1, h.2.2.2.1.2, h.2.2.2.2.1,
      fun n' a b t' h1 h2 => h.2.2.2.2.2 n' a b t' ⟨h1, h2⟩⟩
  have hT : HeavyT d n₁ E n := HeavyT.of_ge_N6 (by omega) hN6
  have key := es6_one_of_params hI hN hp hT hβ5
  have hC6 : 0 < heavyC6 d E := by
    unfold heavyC6; have := heavyc_pos (d := d) (E := E) (by omega); linarith
  set G := {ω | ∀ t : ℝ, 0 ≤ t → t + indScale t₀ n ^ heavyEps d ≤ indScale t₀ n →
        ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * indScale t₀ n ^ heavyEps d) ≤
          volume ({s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s} ∩
            Icc t (t + indScale t₀ n ^ heavyEps d))} with hG
  have hpn := step_pn_eq h
  have hexp : Real.exp (-(heavyC6 d E * (n : ℝ) ^ 3)) ≤ indFailBound β t₀ n := by
    rw [hpn]; exact exp_neg_mul_cube_le hC6 hc
  have hcompl : P {ω | ¬ ω ∈ G} ≤ ENNReal.ofReal (indFailBound β t₀ n) :=
    key.trans (ENNReal.ofReal_le_ofReal hexp)
  have hGsub : G ⊆ {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) (indScale t₀ n)} := by
    intro ω hω
    have hgeo : geoSlices N ω = fun k => copyEnv (N ω) k := by
      funext k; exact (congrFun (avoidEnv_eq_cycSlice N ω) k).symm
    have hT1 := step_one_le_scale h
    have hTn : (4 : ℝ) ^ n ≤ indScale t₀ n := by
      unfold indScale
      have := h.2.2.2.1.1
      have hp : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
      nlinarith
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hL : 0 < indScale t₀ n ^ heavyEps d := Real.rpow_pos_of_pos (by linarith) _
    have hLle := eps_window_le hn3 hTn heavyEps_nonneg (heavyEps_le hd)
    have hcov := window_cover {s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s} hL
      (a := 9 / 10 + 2 / (n : ℝ)) (T := indScale t₀ n) (by positivity) (by linarith)
      (fun t ht1 ht2 => hω t ht1 ht2)
    unfold IsRelaxedPath
    rw [scaleIndex_indScale h.2.2.2.1.1 h.2.2.2.1.2 n]
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hcov.trans (le_of_eq ?_))
    · have e : (9 / 10 + 2 / (n : ℝ)) * (indScale t₀ n - indScale t₀ n ^ heavyEps d) -
          (9 / 10 + 1 / (n : ℝ)) * indScale t₀ n =
          (indScale t₀ n - indScale t₀ n ^ heavyEps d * ((9 / 10) * n + 2)) / n := by
        field_simp; ring
      have : 0 ≤ (indScale t₀ n - indScale t₀ n ^ heavyEps d * ((9 / 10) * n + 2)) / n :=
        div_nonneg (by linarith) hnpos.le
      linarith
    · rw [hgeo]
      congr 1
      ext s
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc]
      tauto
  have hone : (1 : ℝ≥0∞) ≤ P {ω | ω ∈ G} + P {ω | ¬ ω ∈ G} := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P ({ω | ω ∈ G} ∪ {ω | ¬ ω ∈ G}) :=
          measure_mono fun ω _ => by by_cases hh : ω ∈ G <;> simp [hh]
      _ ≤ _ := measure_union_le _ _
  have hp1 : indFailBound β t₀ n ≤ 1 := by
    rw [hpn]; exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (n : ℝ)])
  have hp0 : 0 ≤ indFailBound β t₀ n := by rw [hpn]; exact (Real.exp_pos _).le
  have e : ENNReal.ofReal (1 - indFailBound β t₀ n) + ENNReal.ofReal (indFailBound β t₀ n) = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hp0]; simp
  unfold IndH1
  refine le_trans ?_ (measure_mono hGsub)
  rw [← e] at hone
  have := hone.trans (add_le_add le_rfl hcompl)
  exact (ENNReal.add_le_add_iff_right (ENNReal.ofReal_ne_top (r := indFailBound β t₀ n))).1 this

end ElboimSly.Paper.Step

end
