/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Operations
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import ElboimSly.Frozen.Defs.CopyEnv
public import ElboimSly.Frozen.Defs.RegenWalk
public import ElboimSly.Frozen.Defs.RingIntensity
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
import Mathlib

/-!
# Copies of the environment record, and the regenerated walk at the first regeneration time

The constructions of the regenerated walk (i) (the marginal part), regenerated cyclic walk.

* `isPoissonPointProcess_copyEnv`: each copy `copyEnv (N ω) k` of a Poisson point process on
  `ℕ × S_β` with intensity `# ⊗ μ_β` is a Poisson point process with intensity `μ_β`. This is the
  marginal statement of the constructions of the regenerated walk (i); independence of the copies is not needed for R1.
* `regenWalk_eq_zero_of_treg`: if `t_reg^{(1)} = nβ` and the second environment is good, the
  regenerated walk is at `0` at time `nβ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Roots

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem count_prod_restrict_map_snd (k : ℕ) :
    (((Measure.count : Measure ℕ).prod (ringIntensity d β)).restrict ({k} ×ˢ Set.univ)).map Prod.snd = ringIntensity d β := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.map_snd_prod,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.count_singleton, one_smul]

/-- Marginal part of the constructions of the regenerated walk (i): every copy of a Poisson point process of intensity
`# ⊗ μ_β` is a Poisson point process of intensity `μ_β`. -/
theorem isPoissonPointProcess_copyEnv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (h : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) (k : ℕ) :
    IsPoissonPointProcess (fun ω => copyEnv (N ω) k) (ringIntensity d β) P := by
  have h1 := (h.restrict (A := {k} ×ˢ Set.univ)
    ((measurableSet_singleton k).prod MeasurableSet.univ)).map_measure
    (φ := Prod.snd) measurable_snd
  rw [count_prod_restrict_map_snd] at h1
  exact h1

/-- `t_reg` is at least `β`. -/
theorem ofReal_le_cycTreg (ν : Measure (RingSpace d β)) : ENNReal.ofReal β ≤ cycTreg ν := by
  have hβ : 0 < β := Fact.out
  refine le_iInf fun k => ENNReal.ofReal_le_ofReal ?_
  have : (1 : ℝ) ≤ k.1 := by exact_mod_cast k.2.1
  nlinarith

omit [Fact (0 < β)] in
theorem regenSigma_zero (ν : ℕ → Measure (RingSpace d β)) : regenSigma ν 0 = 0 := by
  simp [regenSigma]

omit [Fact (0 < β)] in
theorem regenSigma_one (ν : ℕ → Measure (RingSpace d β)) : regenSigma ν 1 = cycTreg (ν 0) := by
  simp [regenSigma]

omit [Fact (0 < β)] in
theorem regenSigma_two (ν : ℕ → Measure (RingSpace d β)) :
    regenSigma ν 2 = cycTreg (ν 0) + cycTreg (ν 1) := by
  simp [regenSigma, Finset.sum_range_succ]

omit [Fact (0 < β)] in
theorem regenSigma_mono (ν : ℕ → Measure (RingSpace d β)) : Monotone (regenSigma ν) :=
  fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- If `t_reg^{(1)} = t` is finite, the regeneration count at time `t` is `1`. -/
theorem regenCount_eq_one (ν : ℕ → Measure (RingSpace d β)) {t : ℝ} (_ht : 0 ≤ t)
    (h : cycTreg (ν 0) = ENNReal.ofReal t) : regenCount ν t = 1 := by
  have hβ : 0 < β := Fact.out
  have h2 : ENNReal.ofReal t < regenSigma ν 2 := by
    rw [regenSigma_two, h]
    have := ofReal_le_cycTreg (ν 1)
    exact ENNReal.lt_add_right ENNReal.ofReal_ne_top
      (lt_of_lt_of_le (by simpa using hβ) this).ne'
  unfold regenCount
  have hset : {i : ℕ | regenSigma ν i ≤ ENNReal.ofReal t} = {0, 1} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hi
      by_contra hne
      have : 2 ≤ i := by omega
      exact absurd (lt_of_lt_of_le h2 (regenSigma_mono ν this)) (not_lt.2 hi)
    · rintro (rfl | rfl)
      · simp [regenSigma_zero]
      · rw [regenSigma_one, h]
  rw [hset]
  simp

/-- The regenerated walk is at `0` at the first regeneration time `t_reg^{(1)} = t`, provided the
second environment is good. -/
theorem regenWalk_eq_zero_of_treg (ν : ℕ → Measure (RingSpace d β)) (hν1 : Good (ν 1)) {t : ℝ}
    (ht : 0 ≤ t) (h : cycTreg (ν 0) = ENNReal.ofReal t) : regenWalk ν t = 0 := by
  have hc := regenCount_eq_one ν ht h
  have hs : regenStart ν t = t := by
    unfold regenStart
    rw [hc, regenSigma_one, h, ENNReal.toReal_ofReal ht]
  unfold regenWalk
  rw [hc, hs, sub_self]
  exact Cyclic.cycWalk_zero hν1 0 0

end ElboimSly.Roots

end
