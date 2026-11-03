/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.PairLemmaAux
public import Mathlib

/-!
# One pair of walks from a common cyclic time

One pair of walks from a common cyclic time (ES22 Lemma 8.2 for fixed `v`, ES22 §8).

`es8_pair`: for `a ≠ b`, `r ∈ ℝ`, and `T = 2 t'_n < β`, the set `𝔓^r_{a,b}` of times at which the
walk `W_{b,r}` is within `1.9ⁿ` of the range of `W_{a,r}` has Lebesgue measure `< 3.9ⁿ`, except
with probability `ε(n)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem lem82T_le_four (n : ℕ) {t₀ : ℝ} (ht4 : t₀ ≤ 4) :
    lem82T n t₀ ≤ 2 * 4 ^ (n + 1) / (n : ℝ) ^ 4 := by
  unfold lem82T
  rw [mul_div_assoc 2 ((4 : ℝ) ^ (n + 1)) ((n : ℝ) ^ 4)]
  gcongr
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left ht4 (by positivity)

theorem lem82T_lt_beta {n : ℕ} (hn : 4 ≤ n) {t₀ : ℝ} {β : ℝ} (hβ : 0 < β)
    (htβ : indScale t₀ n ≤ β) : lem82T n t₀ < β := by
  have hn4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) this 4]
  have hpos : (0 : ℝ) < (n : ℝ) ^ 4 := by linarith
  unfold lem82T
  unfold indScale at htβ
  rw [← mul_div_assoc, div_lt_iff₀ hpos]
  nlinarith

theorem cycContactSet_eq_lebSet {ν : Measure (RingSpace d β)} (hν : Good ν) (a b : Fin d → ℤ)
    (r : ℝ) (T : ℝ≥0) (ρ : ℝ) :
    cycContactSet ν a b r T ρ =
      lebSet T T ρ 0 1 (pairOn T (trajProc ν a r) (trajProc ν b r)) := by
  ext x
  simp only [cycContactSet, lebSet, mem_ofPred_eq, mem_Icc]
  constructor
  · rintro ⟨⟨hx0, hxT⟩, y, ⟨hy0, hyT⟩, h⟩
    refine ⟨hx0, hxT, y, hy0, hyT, ?_⟩
    have hx' : x.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hxT
    have hy' : y.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hyT
    show ‖trajProc ν b r (min x.toNNReal T) - trajProc ν a r (min y.toNNReal T)‖ ≤ ρ
    rw [min_eq_left hx', min_eq_left hy', ← cycWalk_eq_trajProc hν, ← cycWalk_eq_trajProc hν,
      Real.coe_toNNReal _ hx0, Real.coe_toNNReal _ hy0]
    exact h
  · rintro ⟨hx0, hxT, y, hy0, hyT, h⟩
    refine ⟨⟨hx0, hxT⟩, y, ⟨hy0, hyT⟩, ?_⟩
    have hx' : x.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hxT
    have hy' : y.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hyT
    have h' : ‖trajProc ν b r (min x.toNNReal T) - trajProc ν a r (min y.toNNReal T)‖ ≤ ρ := h
    rw [min_eq_left hx', min_eq_left hy', ← cycWalk_eq_trajProc hν, ← cycWalk_eq_trajProc hν,
      Real.coe_toNNReal _ hx0, Real.coe_toNNReal _ hy0] at h'
    exact h'

omit [Fact (0 < β)] in
theorem volume_cycContactSet_ne_top (ν : Measure (RingSpace d β)) (a b : Fin d → ℤ) (r T ρ : ℝ) :
    volume (cycContactSet ν a b r T ρ) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (measure_mono (fun x hx => hx.1 : cycContactSet ν a b r T ρ ⊆
    Icc 0 T))

theorem es8K_bound (n : ℕ) (hn : 1 ≤ n) :
    ((2 * n ^ 5 * es8K n : ℕ) : ℝ) ≤ (19 / 10 : ℝ) ^ n / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h5 : (0 : ℝ) < 4 * (n : ℝ) ^ 5 := by positivity
  have hfl : (es8K n : ℝ) ≤ (1.9 : ℝ) ^ n / (4 * (n : ℝ) ^ 5) := Nat.floor_le (by positivity)
  have e : (1.9 : ℝ) = 19 / 10 := by norm_num
  rw [e] at hfl
  push_cast
  rw [le_div_iff₀ h5] at hfl
  nlinarith

/-- **one pair of walks from a common cyclic time**: the set `𝔓^r_{a,b}` has measure `≥ 3.9ⁿ` with probability at most `ε(n)`. -/
theorem es8_pair {Ω : Type} [MeasurableSpace Ω] {Pe : Measure Ω}
    {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (hd : 5 ≤ d) {n : ℕ} (hn4 : 4 ≤ n)
    (hnC : lem82nC d ≤ n) (hn2 : lem82n2 d ≤ n) (hn39 : 14980 ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀)
    (ht4 : t₀ ≤ 4) (htβ : indScale t₀ n ≤ β) (a b : Fin d → ℤ) (hab : a ≠ b) (r : ℝ) :
    AEMeasurable (fun ω => volume
      (cycContactSet (ν ω) a b r (lem82T n t₀) ((19 / 10 : ℝ) ^ n))) Pe ∧
    Pe {ω | ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
        volume (cycContactSet (ν ω) a b r (lem82T n t₀) ((19 / 10 : ℝ) ^ n))} ≤
      ENNReal.ofReal (es8Eps d n) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Ω', mΩ', Pd, Ñ, hPd, hÑ, -⟩ :=
    exists_isPoissonPointProcess_clockIntensity (Dir d × Fin 2)
  have hβ : 0 < β := Fact.out
  have hTpos : 0 < lem82T n t₀ := lem82T_pos hn4 ht1
  set T : ℝ≥0 := (lem82T n t₀).toNNReal with hT
  have hTc : (T : ℝ) = lem82T n t₀ := Real.coe_toNNReal _ hTpos.le
  have hTβ : (T : ℝ) < β := by rw [hTc]; exact lem82T_lt_beta hn4 hβ htβ
  set ρ : ℝ := (19 / 10 : ℝ) ^ n with hρ
  set Z : Ω → PathsOn d 2 T := fun ω =>
    pairOn T (trajProc (ν ω) a r) (trajProc (ν ω) b r) with hZ
  set Z' : Ω' → PathsOn d 2 T := twoPaths Ñ a b T with hZ'
  have hlaw : Pe.map Z = Pd.map Z' := one_lap_b hν hÑ a b r hTβ
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  have hZm : Measurable Z := pairOn_measurable
    (fun s => (measurable_pi_apply s).comp ((measurable_trajProc a r).comp hν.measurable))
    (fun s => (measurable_pi_apply s).comp ((measurable_trajProc b r).comp hν.measurable))
  have hZ'm : Measurable Z' := measurable_twoPaths hÑ a b T
  have hreg : ∀ᵐ ω ∂Pe, IsRegularPaths T (Z ω) := hgood.mono fun ω hω =>
    isRegularPaths_pairOn (isStepPath_trajProc hω a r) (isStepPath_trajProc hω b r)
  have hreg' : ∀ᵐ ω ∂Pd, IsRegularPaths T (Z' ω) :=
    Filter.Eventually.of_forall fun ω => isRegularPaths_twoPaths a b T ω
  obtain ⟨h1, h2, h3, h4⟩ := es8_regular_law (d := d) (k := 2) (T := T) (L := T) ρ 0 1 hZm hZ'm
    hreg hreg' hlaw
  have hΦ : Measurable fun ω => Phi T T ρ 0 1 (Z ω) :=
    (measurable_Phi (d := d) (k := 2) T T ρ 0 1).comp hZm
  have hΦ' : Measurable fun ω => Phi T T ρ 0 1 (Z' ω) :=
    (measurable_Phi (d := d) (k := 2) T T ρ 0 1).comp hZ'm
  have hcs : ∀ ω, Good (ν ω) →
      cycContactSet (ν ω) a b r (lem82T n t₀) ρ = lebSet T T ρ 0 1 (Z ω) := fun ω hω => by
    rw [← hTc]; exact cycContactSet_eq_lebSet hω a b r T ρ
  have hvol : ∀ ω, Good (ν ω) → volume (cycContactSet (ν ω) a b r (lem82T n t₀) ρ) =
      ENNReal.ofReal (lebMeas T T ρ 0 1 (Z ω)) := fun ω hω => by
    rw [hcs ω hω]
    have : volume (lebSet T T ρ 0 1 (Z ω)) ≠ ⊤ := by
      rw [← hcs ω hω]; exact volume_cycContactSet_ne_top _ _ _ _ _ _
    exact (ENNReal.ofReal_toReal this).symm
  refine ⟨?_, ?_⟩
  · refine (ENNReal.measurable_ofReal.comp hΦ).aemeasurable.congr ?_
    filter_upwards [hgood, h1] with ω hω h1ω
    simp only [Function.comp_apply]
    rw [hvol ω hω, h1ω]
  -- the cyclic side
  have hcyc : Pe {ω | ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
      volume (cycContactSet (ν ω) a b r (lem82T n t₀) ρ)} =
      Pe {ω | (39 / 10 : ℝ) ^ n ≤ Phi T T ρ 0 1 (Z ω)} := by
    refine measure_congr ?_
    filter_upwards [hgood, h1] with ω hω h1ω
    refine propext ?_
    show (ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
      volume (cycContactSet (ν ω) a b r (lem82T n t₀) ρ)) ↔ (39 / 10 : ℝ) ^ n ≤ Phi T T ρ 0 1 (Z ω)
    rw [hvol ω hω, ← h1ω]
    exact ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg
  rw [hcyc]
  set c : ℝ := (39 / 10 : ℝ) ^ n with hc
  have hP1 : Pe {ω | c ≤ Phi T T ρ 0 1 (Z ω)} = Pd {ω | c ≤ Phi T T ρ 0 1 (Z' ω)} := by
    have e1 : Pe.map (fun ω => Phi T T ρ 0 1 (Z ω)) (Ici c) =
        Pd.map (fun ω => Phi T T ρ 0 1 (Z' ω)) (Ici c) := by rw [h3]
    rwa [Measure.map_apply hΦ measurableSet_Ici, Measure.map_apply hΦ' measurableSet_Ici] at e1
  have hP2 : Pd {ω | c ≤ Phi T T ρ 0 1 (Z' ω)} = Pd {ω | c ≤ lebMeas T T ρ 0 1 (Z' ω)} := by
    refine measure_congr ?_
    filter_upwards [h2] with ω hω
    refine propext ?_
    show c ≤ Phi T T ρ 0 1 (Z' ω) ↔ c ≤ lebMeas T T ρ 0 1 (Z' ω)
    rw [hω]
  rw [hP1, hP2]
  -- the driven side
  set k : ℕ := es8K n with hk
  have hkb := es8K_bound n (by omega)
  have hρ' : (19 / 10 : ℝ) ^ n + ((2 * n ^ 5 * k : ℕ) : ℝ) ≤ (1.9 : ℝ) ^ (n + 1) := by
    have e : (1.9 : ℝ) = 19 / 10 := by norm_num
    rw [e, pow_succ (19 / 10 : ℝ) n]
    have : (0 : ℝ) < (19 / 10 : ℝ) ^ n := by positivity
    nlinarith
  have hthr := es8_threshold n hn39
  have hsub : {ω | c ≤ lebMeas T T ρ 0 1 (Z' ω)} ⊆ decoupBad Ñ a b T n k ∪
      {ω | (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n <
        (volume (baseProxSet Ñ a b T T ((1.9 : ℝ) ^ (n + 1)) ω)).toReal} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
    obtain ⟨hnb, hbd⟩ := hnot
    have hsubset := lebSet_twoPaths_subset a b n k ((1.9 : ℝ) ^ (n + 1)) hρ' hnb
    have hfin : volume (baseProxSet Ñ a b T T ((1.9 : ℝ) ^ (n + 1)) ω) ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_Icc_lt_top (a := (0 : ℝ)) (b := (T : ℝ))).ne
        (measure_mono (fun x hx => ⟨hx.1, hx.2.1⟩ :
        baseProxSet Ñ a b T T ((1.9 : ℝ) ^ (n + 1)) ω ⊆ Icc 0 (T : ℝ)))
    have h5 : lebMeas T T ρ 0 1 (Z' ω) ≤
        (volume (baseProxSet Ñ a b T T ((1.9 : ℝ) ^ (n + 1)) ω)).toReal :=
      ENNReal.toReal_mono hfin (measure_mono hsubset)
    have e : (39 / 10 : ℝ) ^ n = (3.9 : ℝ) ^ n := by norm_num
    have hω' : (3.9 : ℝ) ^ n ≤ lebMeas T T ρ 0 1 (Z' ω) := by rw [← e]; exact hω
    linarith
  have hdec := (es8_decoupling hÑ (by omega : 3 ≤ d) a b hab T n k).2.2
  have hprox := es8_proximity hÑ hd hnC hn2 ht1 ht4 a b (L := T) (le_refl T)
  calc Pd {ω | c ≤ lebMeas T T ρ 0 1 (Z' ω)}
      ≤ Pd (decoupBad Ñ a b T n k ∪ {ω | (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n <
          (volume (baseProxSet Ñ a b T T ((1.9 : ℝ) ^ (n + 1)) ω)).toReal}) := measure_mono hsub
    _ ≤ Pd (decoupBad Ñ a b T n k) + Pd {ω | (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n <
          (volume (baseProxSet Ñ a b T T ((1.9 : ℝ) ^ (n + 1)) ω)).toReal} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((1 - es8C1 d) ^ k + 2 * ((T : ℝ) + 1) *
          Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)) +
        (ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ (n ^ 4))) :=
        add_le_add hdec hprox
    _ ≤ ENNReal.ofReal (es8Eps d n) := by
        have hE : 0 < Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5) := Real.exp_pos _
        have hc1 : 0 ≤ (1 - es8C1 d) ^ k := pow_nonneg (sub_nonneg.2 (es8C1_lt_one d).le) _
        have hTle : (T : ℝ) ≤ 2 * 4 ^ (n + 1) / (n : ℝ) ^ 4 := by
          rw [hTc]; exact lem82T_le_four n ht4
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        unfold es8Eps
        have e2 : ((1 / 2 : ℝ) ^ (n ^ 4)) = ((2 : ℝ) ^ (n ^ 4))⁻¹ := by
          rw [one_div, inv_pow]
        rw [e2]
        have : 2 * ((T : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5) ≤
            2 * (2 * 4 ^ (n + 1) / (n : ℝ) ^ 4 + 1) *
              Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5) := by
          gcongr
        linarith

end ElboimSly.Paper

end
