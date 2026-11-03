/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Lemma82Cases
public import ElboimSly.Paper.Base.PairLemma
public import ElboimSly.Frozen.Defs.IndScaleReduced
public import ElboimSly.Frozen.Defs.IndScale
public import Mathlib

/-!
# Lemma 8.2: Case B

ES22 Lemma 8.2, "Case B".

If the two windows `[r_a, r_a + t']` and `[r_b, r_b + t']` are disjoint modulo `β`, the pair of
walks has the law of an independent pair (cyclic walks within one lap (c)), and
Proximity times of an independent walk bounds the measure of the contact set.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem lemPairSet_eq_lebSet {ν : Measure (RingSpace d β)} (hν : Good ν) (u₁ u₂ : Fin d → ℤ)
    (ra rb : ℝ) (L : ℝ≥0) (ρ : ℝ) :
    lemPairSet ν u₁ u₂ ra rb L ρ =
      lebSet L L ρ 0 1 (pairOn L (trajProc ν u₁ ra) (trajProc ν u₂ rb)) := by
  ext x
  simp only [lemPairSet, lebSet, mem_ofPred_eq, mem_Icc]
  constructor
  · rintro ⟨⟨hx0, hxT⟩, y, ⟨hy0, hyT⟩, h⟩
    refine ⟨hx0, hxT, y, hy0, hyT, ?_⟩
    have hx' : x.toNNReal ≤ L := Real.toNNReal_le_iff_le_coe.2 hxT
    have hy' : y.toNNReal ≤ L := Real.toNNReal_le_iff_le_coe.2 hyT
    show ‖trajProc ν u₂ rb (min x.toNNReal L) - trajProc ν u₁ ra (min y.toNNReal L)‖ ≤ ρ
    rw [min_eq_left hx', min_eq_left hy', norm_sub_rev, ← cycWalk_eq_trajProc hν,
      ← cycWalk_eq_trajProc hν, Real.coe_toNNReal _ hx0, Real.coe_toNNReal _ hy0]
    exact h
  · rintro ⟨hx0, hxT, y, hy0, hyT, h⟩
    refine ⟨⟨hx0, hxT⟩, y, ⟨hy0, hyT⟩, ?_⟩
    have hx' : x.toNNReal ≤ L := Real.toNNReal_le_iff_le_coe.2 hxT
    have hy' : y.toNNReal ≤ L := Real.toNNReal_le_iff_le_coe.2 hyT
    have h' : ‖trajProc ν u₂ rb (min x.toNNReal L) - trajProc ν u₁ ra (min y.toNNReal L)‖ ≤ ρ := h
    rw [min_eq_left hx', min_eq_left hy', ← cycWalk_eq_trajProc hν, ← cycWalk_eq_trajProc hν,
      Real.coe_toNNReal _ hx0, Real.coe_toNNReal _ hy0, norm_sub_rev] at h'
    exact h'

theorem lem82T_eq_two_mul (n : ℕ) (t₀ : ℝ) : lem82T n t₀ = 2 * indScaleReduced t₀ n := by
  unfold lem82T indScaleReduced indScale
  ring

theorem indScaleReduced_pos {n : ℕ} (hn : 1 ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀) :
    0 < indScaleReduced t₀ n := by
  unfold indScaleReduced indScale
  have : (0 : ℝ) < n := by exact_mod_cast hn
  have : (0 : ℝ) < t₀ := by linarith
  positivity

/-- **Case B**. -/
theorem caseB_prob {Ω : Type} [MeasurableSpace Ω] {Pe : Measure Ω}
    {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (hd : 5 ≤ d) {n : ℕ} (_hn4 : 4 ≤ n)
    (hnC : lem82nC d ≤ n) (hn2 : lem82n2 d ≤ n) (hn39 : 14980 ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀)
    (ht4 : t₀ ≤ 4) (u₁ u₂ : Fin d → ℤ) {ra rb : ℝ}
    (h1 : ra + indScaleReduced t₀ n < rb) (h2 : rb + indScaleReduced t₀ n < ra + β) :
    Pe {ω | ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
        volume (lemPairSet (ν ω) u₁ u₂ ra rb (indScaleReduced t₀ n) ((19 / 10 : ℝ) ^ n))} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ (n ^ 4)) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Ω', mΩ', Pd, Ñ, hPd, hÑ, -⟩ :=
    exists_isPoissonPointProcess_clockIntensity (Dir d × Fin 2)
  have hpos : 0 < indScaleReduced t₀ n := indScaleReduced_pos (by omega) ht1
  set L : ℝ≥0 := (indScaleReduced t₀ n).toNNReal with hL
  have hLc : (L : ℝ) = indScaleReduced t₀ n := Real.coe_toNNReal _ hpos.le
  set T' : ℝ≥0 := (lem82T n t₀).toNNReal with hT'
  have hLT : L ≤ T' := by
    rw [hL, hT']
    exact Real.toNNReal_le_toNNReal (by rw [lem82T_eq_two_mul]; linarith)
  set ρ : ℝ := (19 / 10 : ℝ) ^ n with hρ
  set Z : Ω → PathsOn d 2 L := fun ω =>
    pairOn L (trajProc (ν ω) u₁ ra) (trajProc (ν ω) u₂ rb) with hZ
  set Z' : Ω' → PathsOn d 2 L := proxPaths Ñ u₁ u₂ L with hZ'
  have hlaw : Pe.map Z = Pd.map Z' := by
    refine one_lap_c hν hÑ u₁ u₂ ra rb (L := L) (by rw [hLc]; exact h1) (by rw [hLc]; exact h2)
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  have hZm : Measurable Z := pairOn_measurable
    (fun s => (measurable_pi_apply s).comp ((measurable_trajProc u₁ ra).comp hν.measurable))
    (fun s => (measurable_pi_apply s).comp ((measurable_trajProc u₂ rb).comp hν.measurable))
  have hZ'm : Measurable Z' := measurable_proxPaths hÑ u₁ u₂ L
  have hreg : ∀ᵐ ω ∂Pe, IsRegularPaths L (Z ω) := hgood.mono fun ω hω =>
    isRegularPaths_pairOn (isStepPath_trajProc hω u₁ ra) (isStepPath_trajProc hω u₂ rb)
  have hreg' : ∀ᵐ ω ∂Pd, IsRegularPaths L (Z' ω) :=
    Filter.Eventually.of_forall fun ω => isRegularPaths_proxPaths u₁ u₂ L ω
  obtain ⟨h1', h2', h3', h4'⟩ := es8_regular_law (d := d) (k := 2) (T := L) (L := L) ρ 0 1
    hZm hZ'm hreg hreg' hlaw
  have hΦ : Measurable fun ω => Phi L L ρ 0 1 (Z ω) :=
    (measurable_Phi (d := d) (k := 2) L L ρ 0 1).comp hZm
  have hΦ' : Measurable fun ω => Phi L L ρ 0 1 (Z' ω) :=
    (measurable_Phi (d := d) (k := 2) L L ρ 0 1).comp hZ'm
  have hvol : ∀ ω, Good (ν ω) → volume (lemPairSet (ν ω) u₁ u₂ ra rb (indScaleReduced t₀ n) ρ) =
      ENNReal.ofReal (lebMeas L L ρ 0 1 (Z ω)) := fun ω hω => by
    rw [← hLc, lemPairSet_eq_lebSet hω]
    have : volume (lebSet L L ρ 0 1 (Z ω)) ≠ ⊤ := ne_top_of_le_ne_top
      (measure_Icc_lt_top (a := (0 : ℝ)) (b := (L : ℝ))).ne
      (measure_mono (fun x hx => ⟨hx.1, hx.2.1⟩))
    exact (ENNReal.ofReal_toReal this).symm
  have hcyc : Pe {ω | ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
      volume (lemPairSet (ν ω) u₁ u₂ ra rb (indScaleReduced t₀ n) ρ)} =
      Pe {ω | (39 / 10 : ℝ) ^ n ≤ Phi L L ρ 0 1 (Z ω)} := by
    refine measure_congr ?_
    filter_upwards [hgood, h1'] with ω hω h1ω
    refine propext ?_
    show (ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
      volume (lemPairSet (ν ω) u₁ u₂ ra rb (indScaleReduced t₀ n) ρ)) ↔
        (39 / 10 : ℝ) ^ n ≤ Phi L L ρ 0 1 (Z ω)
    rw [hvol ω hω, ← h1ω]
    exact ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg
  rw [hcyc]
  set c : ℝ := (39 / 10 : ℝ) ^ n with hc
  have hP1 : Pe {ω | c ≤ Phi L L ρ 0 1 (Z ω)} = Pd {ω | c ≤ Phi L L ρ 0 1 (Z' ω)} := by
    have e1 : Pe.map (fun ω => Phi L L ρ 0 1 (Z ω)) (Ici c) =
        Pd.map (fun ω => Phi L L ρ 0 1 (Z' ω)) (Ici c) := by rw [h3']
    rwa [Measure.map_apply hΦ measurableSet_Ici, Measure.map_apply hΦ' measurableSet_Ici] at e1
  have hP2 : Pd {ω | c ≤ Phi L L ρ 0 1 (Z' ω)} = Pd {ω | c ≤ lebMeas L L ρ 0 1 (Z' ω)} := by
    refine measure_congr ?_
    filter_upwards [h2'] with ω hω
    refine propext ?_
    show c ≤ Phi L L ρ 0 1 (Z' ω) ↔ c ≤ lebMeas L L ρ 0 1 (Z' ω)
    rw [hω]
  rw [hP1, hP2]
  have hthr := es8_threshold n hn39
  have hρ' : ρ ≤ (1.9 : ℝ) ^ (n + 1) := by
    have e : (1.9 : ℝ) = 19 / 10 := by norm_num
    rw [e, pow_succ, hρ]
    have : (0 : ℝ) < (19 / 10 : ℝ) ^ n := by positivity
    nlinarith
  have hsub : {ω | c ≤ lebMeas L L ρ 0 1 (Z' ω)} ⊆ {ω | (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n <
        (volume (baseProxSet Ñ u₁ u₂ T' L ((1.9 : ℝ) ^ (n + 1)) ω)).toReal} := by
    intro ω hω
    by_contra hnot
    simp only [mem_ofPred_eq, not_lt] at hnot
    have hsubset : lebSet L L ρ 0 1 (Z' ω) ⊆ baseProxSet Ñ u₁ u₂ T' L ((1.9 : ℝ) ^ (n + 1)) ω := by
      rw [hZ', lebSet_proxPaths u₁ u₂ le_rfl ρ ω]
      rintro x ⟨hx0, hxT, y, hy⟩
      exact ⟨hx0, hxT.trans (by exact_mod_cast hLT), y, hy.1, hy.2.trans hρ'⟩
    have hfin : volume (baseProxSet Ñ u₁ u₂ T' L ((1.9 : ℝ) ^ (n + 1)) ω) ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_Icc_lt_top (a := (0 : ℝ)) (b := (T' : ℝ))).ne
        (measure_mono (fun x hx => ⟨hx.1, hx.2.1⟩))
    have h5 : lebMeas L L ρ 0 1 (Z' ω) ≤
        (volume (baseProxSet Ñ u₁ u₂ T' L ((1.9 : ℝ) ^ (n + 1)) ω)).toReal :=
      ENNReal.toReal_mono hfin (measure_mono hsubset)
    have e : (39 / 10 : ℝ) ^ n = (3.9 : ℝ) ^ n := by norm_num
    have hω' : (3.9 : ℝ) ^ n ≤ lebMeas L L ρ 0 1 (Z' ω) := by rw [← e]; exact hω
    linarith
  have hprox := es8_proximity hÑ hd hnC hn2 ht1 ht4 u₁ u₂ (L := L) hLT
  exact (measure_mono hsub).trans hprox

end ElboimSly.Paper

end
