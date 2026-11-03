/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Adapted
public import ElboimSly.Paper.Escape.C56MeasGen
public import ElboimSly.Paper.Avoid.Hyp
public import ElboimSly.Paper.Induction.RelaxedMeasRegen2
public import ElboimSly.Paper.Roots.RegenCopies
public import ElboimSly.Foundations.Concentration.GeometricEvents
public import Mathlib

/-!
# `E^d`: the regenerated walk is a relaxed path (as a set of paths)

ES22 Claim 5.6, event `E^d`, using the induction hypothesis at arbitrary times (c).

`relPathSet β T` is the set of `CPath`s that either return to `0` at a time `iβ ≤ T` (a closing
time of the first piece) or have relaxed times, relative to `0`, of measure at least
`(0.9 + 1/n_T) T` in `[0, T]`.  It is measurable; for the regenerated walk it has probability
`≥ 1 - e^{-n_T²}` (`es4_hyp_c`); and for a regenerated walk that has not regenerated before `T`
it gives the relaxed-path bound for the path itself.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly

variable {k : ℕ}

/-- The relaxed-measure condition for a path (relaxed relative to `0`). -/
def relMeasureOK (β T : ℝ) (p : CPath (Fin (k + 2) → ℤ)) : Prop :=
  ENNReal.ofReal ((9 / 10 + 1 / (scaleIndex T : ℝ)) * T) ≤
    volume {s : ℝ | s ∈ Icc 0 T ∧ IsRelaxedTimeWrt β (cpR p) 0 s}

/-- Closing at a time `iβ ≤ T`. -/
def closesBy (β T : ℝ) (p : CPath (Fin (k + 2) → ℤ)) : Prop :=
  ∃ i ∈ Finset.Icc 1 ⌊T / β⌋₊, p.fn (((i : ℝ) * β).toNNReal) = 0

/-- `E^d` as a set of paths. -/
def relPathSet (β T : ℝ) : Set (CPath (Fin (k + 2) → ℤ)) :=
  {p | closesBy β T p ∨ relMeasureOK β T p}

theorem measurableSet_relPathSet {β : ℝ} (hβ : 0 < β) (T : ℝ) :
    MeasurableSet (relPathSet (k := k) β T) := by
  have : Fact (0 < β) := ⟨hβ⟩
  have hw : Measurable fun p : CPath (Fin (k + 2) → ℤ) × ℝ => cpR p.1 p.2 :=
    measurable_fn_at (fun p : CPath (Fin (k + 2) → ℤ) × ℝ => p.1) measurable_fst _
      measurable_snd.real_toNNReal
  have key := measurableSet_isRelaxedTimeWrt (β := β) (Ω := CPath (Fin (k + 2) → ℤ))
    (fun p r => cpR p r) (fun _ _ => 0) hw measurable_const (fun p s => cpRc p s)
  have hS : MeasurableSet {q : CPath (Fin (k + 2) → ℤ) × ℝ | q.2 ∈ Icc 0 T ∧
      IsRelaxedTimeWrt β (cpR q.1) 0 q.2} :=
    (measurable_snd measurableSet_Icc).inter key
  have hvol : Measurable fun p : CPath (Fin (k + 2) → ℤ) => volume {s : ℝ | s ∈ Icc 0 T ∧
      IsRelaxedTimeWrt β (cpR p) 0 s} := measurable_measure_prodMk_left hS
  have h1 : MeasurableSet {p : CPath (Fin (k + 2) → ℤ) | relMeasureOK β T p} :=
    measurableSet_le measurable_const hvol
  have h2 : MeasurableSet {p : CPath (Fin (k + 2) → ℤ) | closesBy β T p} := by
    have : {p : CPath (Fin (k + 2) → ℤ) | closesBy β T p} =
        ⋃ i ∈ Finset.Icc 1 ⌊T / β⌋₊, {p | p.fn (((i : ℝ) * β).toNNReal) = 0} := by
      ext p; simp [closesBy]
    rw [this]
    exact MeasurableSet.biUnion (Finset.countable_toSet _) fun i _ =>
      (CPath.measurable_eval _) (measurableSet_singleton _)
  exact h2.union h1

section Regen

variable {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}

omit [Fact (0 < β)] in
/-- Before the first closing time, the regeneration start is `0`. -/
theorem regenStart_eq_zero_of_lt_treg {ν : ℕ → Measure (RingSpace (k + 2) β)} {s : ℝ}
    (_hs : 0 ≤ s) (h : ENNReal.ofReal s < cycTreg (ν 0)) : regenStart ν s = 0 := by
  have hc : regenCount ν s = 0 := by
    unfold regenCount
    have : {i : ℕ | regenSigma ν i ≤ ENNReal.ofReal s} = {0} := by
      ext i
      simp only [Set.mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro hi
        by_contra hne
        have h1 : regenSigma ν 1 ≤ regenSigma ν i := Roots.regenSigma_mono ν (by omega)
        rw [Roots.regenSigma_one] at h1
        exact absurd (h1.trans hi) (not_le.2 h)
      · rintro rfl; simp [Roots.regenSigma_zero]
    rw [this]; simp
  unfold regenStart
  rw [hc]
  simp [Roots.regenSigma_zero]

omit mΩ in
theorem cpR_escCPath {ω : Ω} (hω : cycNgood N ω = N ω) {r : ℝ} (hr : 0 ≤ r) :
    cpR (escCPath N ω) r = regenWalk (avoidEnv N ω) r := by
  show avoidPath (cycNgood N) ω r.toNNReal = _
  have := congrFun (avoidWalk_congr hω) ((r.toNNReal : ℝ≥0) : ℝ)
  simp only [avoidPath]
  rw [this, Real.coe_toNNReal _ hr]
  rfl

omit mΩ in
/-- A relaxed path of the regenerated walk gives a path in `relPathSet`. -/
theorem escCPath_mem_relPathSet {ω : Ω} (hω : cycNgood N ω = N ω) {T : ℝ} (hT : 0 < T)
    (h : IsRelaxedPath (avoidEnv N ω) T) : escCPath N ω ∈ relPathSet β T := by
  have hg : ∀ j, Good (cycSlice j (N ω)) := by
    intro j; rw [← hω]; exact cycGood_cycNgood N ω j
  have hgood : ∀ j, Good (avoidEnv N ω j) := by
    intro j; rw [avoidEnv_eq_cycSlice]; exact hg j
  by_cases hA : cycTreg (avoidEnv N ω 0) ≤ ENNReal.ofReal T
  · left
    obtain ⟨i, hi, h0⟩ := exists_regenWalk_zero_of_treg_le hgood hT hA
    refine ⟨i, hi, ?_⟩
    have hr : 0 ≤ (i : ℝ) * β := by
      have : 0 < β := Fact.out
      positivity
    have := cpR_escCPath hω hr
    simp only [cpR] at this
    rw [this, h0]
  · right
    have hlt : ENNReal.ofReal T < cycTreg (avoidEnv N ω 0) := not_le.1 hA
    unfold relMeasureOK
    refine le_trans h (le_of_eq (congrArg volume ?_))
    ext s
    simp only [mem_ofPred_eq]
    refine and_congr_right fun hs => ?_
    have hs0 : regenStart (avoidEnv N ω) s = 0 :=
      regenStart_eq_zero_of_lt_treg hs.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs.2) hlt)
    unfold IsRelaxedTime
    rw [hs0]
    exact ind_isRelaxedTimeWrt_congr (β := β) (fun r hr => (cpR_escCPath hω hr).symm)
      le_rfl hs.1

/-- `E^d` has probability `≥ 1 - e^{-n_T²}` (the induction hypothesis at arbitrary times (c)). -/
theorem relPathSet_prob (hp : Es4Params (k + 2) β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr) {T : ℝ}
    (h1 : (4 : ℝ) ^ n₀ < T) (h2 : T ≤ (4 : ℝ) ^ n) :
    ENNReal.ofReal (1 - Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) ≤
      Pr {ω | escCPath N ω ∈ relPathSet β T} := by
  have hT : 0 < T := lt_of_le_of_lt (by positivity) h1
  refine (es4_hyp_c hp hN h1 h2).trans (measure_mono_ae ?_)
  filter_upwards [ae_cycNgood_eq hN] with ω hω hmem
  exact escCPath_mem_relPathSet hω hT hmem

omit mΩ in
/-- If the first piece of `M` has not closed by `T`, the path of the regenerated walk of `M`
has no closing time `iβ ≤ T`. -/
theorem not_closesBy_of_lt_treg {M : Ω → Measure (CycS ℕ (k + 2) β)} {ω : Ω}
    (hM : cycNgood M ω = M ω) {T : ℝ} (hT : ENNReal.ofReal T < cycTreg (avoidEnv M ω 0)) :
    ¬ closesBy β T (escCPath M ω) := by
  rintro ⟨i, hi, h0⟩
  have hβ : 0 < β := Fact.out
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  have hr : 0 ≤ (i : ℝ) * β := by positivity
  have hiT : (i : ℝ) * β ≤ T := by
    have := Nat.floor_le (show 0 ≤ T / β from by
      by_contra hneg
      push Not at hneg
      have : ⌊T / β⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
      omega)
    have h3 : (i : ℝ) ≤ T / β := le_trans (by exact_mod_cast hi2) this
    rwa [le_div_iff₀ hβ] at h3
  have hcw := cpR_escCPath hM hr
  simp only [cpR] at hcw
  rw [h0] at hcw
  have hlt : ENNReal.ofReal ((i : ℝ) * β) < cycTreg (avoidEnv M ω 0) :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hiT) hT
  -- before `treg` the regenerated walk is the first cyclic walk
  have hgood : ∀ j, Good (avoidEnv M ω j) := by
    intro j; rw [avoidEnv_eq_cycSlice]; rw [← hM]; exact cycGood_cycNgood M ω j
  have hu : ((((i : ℝ) * β).toNNReal : ℝ≥0) : ℝ≥0∞) < cycTreg (avoidEnv M ω 0) := by
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hr]; exact hlt
  have hwalk := regenWalk_of_lt_treg (avoidEnv M ω) hu
  rw [Real.coe_toNNReal _ hr] at hwalk
  have hz : cycWalk (avoidEnv M ω 0) 0 0 ((i : ℝ) * β) = 0 := by
    rw [← hwalk, ← hcw]
  have : cycTreg (avoidEnv M ω 0) ≤ ENNReal.ofReal ((i : ℝ) * β) := by
    unfold cycTreg
    exact iInf_le (fun k : {k : ℕ // 1 ≤ k ∧ cycWalk (avoidEnv M ω 0) 0 0 ((k : ℝ) * β) = 0} =>
      ENNReal.ofReal ((k.1 : ℝ) * β)) ⟨i, hi1, hz⟩
  exact absurd hlt (not_lt.2 this)

/-- If the regenerated walk is not `0` at any time `iβ ≤ T`, `i ≥ 1`, it has not regenerated by
`T`. -/
theorem regenStart_eq_zero_of_no_zero {ν : ℕ → Measure (RingSpace (k + 2) β)}
    (hg : ∀ j, Good (ν j)) {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ i ∈ Finset.Icc 1 ⌊T / β⌋₊, regenWalk ν ((i : ℝ) * β) ≠ 0) : regenStart ν T = 0 := by
  have hβ : 0 < β := Fact.out
  apply regenStart_eq_zero_of_lt_treg hT
  by_contra hc
  push Not at hc
  have hTpos : 0 < T := by
    rcases hT.eq_or_lt with h0 | h0
    · exfalso
      rw [← h0, ENNReal.ofReal_zero] at hc
      have := le_cycTreg (ν 0)
      have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal β := ENNReal.ofReal_pos.2 hβ
      exact absurd (lt_of_lt_of_le h1 this) (not_lt.2 (le_zero_iff.2 (le_antisymm hc bot_le)))
    · exact h0
  obtain ⟨i, hi, h0⟩ := exists_regenWalk_zero_of_treg_le hg hTpos hc
  exact h i hi h0

end Regen

end ElboimSly.Paper.Escape

end
