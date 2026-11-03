/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import ElboimSly.Foundations.SRW.KernelDef
public import ElboimSly.Foundations.SRW.StoppedPosition
public import ElboimSly.Foundations.SRW.MarkovIndep
public import ElboimSly.Paper.Roots.RegenCopies
public import Mathlib

/-!
# The regenerated walk below `β` is a simple random walk

Identification of the regenerated walk below β.

* `regenWalk_eq_cycWalk_of_le`: for `t ≤ β` and good environments `ν 0`, `ν 1`,
  `regenWalk ν t = cycWalk (ν 0) 0 0 t`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem regenCount_eq_zero {ν : ℕ → Measure (RingSpace d β)} {t : ℝ}
    (h : ENNReal.ofReal t < cycTreg (ν 0)) : regenCount ν t = 0 := by
  unfold regenCount
  have : {i : ℕ | regenSigma ν i ≤ ENNReal.ofReal t} = {0} := by
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

theorem cycWalk_beta_eq_zero_of_treg {ν : Measure (RingSpace d β)}
    (h : cycTreg ν = ENNReal.ofReal β) : cycWalk ν 0 0 β = 0 := by
  have hβ : 0 < β := Fact.out
  have hlt : cycTreg ν < ENNReal.ofReal (2 * β) := by
    rw [h]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  unfold cycTreg at hlt
  obtain ⟨k, hk⟩ := iInf_lt_iff.1 hlt
  have hk' : (k.1 : ℝ) * β < 2 * β := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 hk
  have hk1 : k.1 = 1 := by
    have : (k.1 : ℝ) < 2 := by nlinarith
    have : k.1 < 2 := by exact_mod_cast this
    have := k.2.1
    omega
  have := k.2.2
  rw [hk1] at this
  simpa using this

/-- Identification of the regenerated walk below β (a), deterministic part. -/
theorem regenWalk_eq_cycWalk_of_le {ν : ℕ → Measure (RingSpace d β)}
    (h1 : Good (ν 1)) {t : ℝ} (ht0 : 0 ≤ t) (htβ : t ≤ β) :
    regenWalk ν t = cycWalk (ν 0) 0 0 t := by
  have hge := Roots.ofReal_le_cycTreg (ν 0)
  by_cases hc : ENNReal.ofReal t < cycTreg (ν 0)
  · simp [regenWalk, regenStart, regenSigma, regenCount_eq_zero hc]
  · have hle : cycTreg (ν 0) ≤ ENNReal.ofReal t := not_lt.1 hc
    have hteq : cycTreg (ν 0) = ENNReal.ofReal t :=
      le_antisymm hle ((ENNReal.ofReal_le_ofReal htβ).trans hge)
    have htb : t = β := by
      have h2 : ENNReal.ofReal β ≤ ENNReal.ofReal t := hge.trans hle
      exact le_antisymm htβ ((ENNReal.ofReal_le_ofReal_iff ht0).1 h2)
    subst htb
    rw [Roots.regenWalk_eq_zero_of_treg ν h1 ht0 hteq]
    exact (cycWalk_beta_eq_zero_of_treg hteq).symm

/-- The cyclic walk `W_{0,0}` of an environment as a path (junk off `Good`). -/
noncomputable def cycPath (ν : Measure (RingSpace d β)) : PathSpace d :=
  fun s => trajProc ν 0 0 s

theorem measurable_cycPath {Ω : Type*} [MeasurableSpace Ω] {ν : Ω → Measure (RingSpace d β)}
    (hν : Measurable ν) : Measurable fun ω => cycPath (ν ω) :=
  measurable_pi_iff.2 fun s => (measurable_pi_apply s).comp
    ((measurable_trajProc 0 0).comp hν)

theorem cycWalk_eq_cycPath {ν : Measure (RingSpace d β)} (hν : Good ν) (s : ℝ≥0) :
    cycWalk ν 0 0 (s : ℝ) = cycPath ν s :=
  cycWalk_eq_trajProc hν 0 0 s

theorem isRegularPath_cycPath {ν : Measure (RingSpace d β)} (hν : Good ν) :
    IsRegularPath (cycPath ν) := by
  intro t
  have h := (fwdTrajFn_spec hν 0 0).1.1 t
  have e : cycPath ν = fwdTrajFn hν 0 0 := by
    funext s; simp [cycPath, trajProc_of_good hν]
  rw [e]
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 h
  refine ⟨u - t, tsub_pos_of_lt hu, fun s hs1 hs2 => ?_⟩
  exact hsub ⟨hs1, by rwa [add_comm, tsub_add_cancel_of_le (show t ≤ u from le_of_lt hu)] at hs2⟩

theorem regenWalk_eq_cycPath {ν : ℕ → Measure (RingSpace d β)} (h0 : Good (ν 0))
    (h1 : Good (ν 1)) {s : ℝ≥0} (hs : (s : ℝ) ≤ β) :
    regenWalk ν s = cycPath (ν 0) s := by
  rw [regenWalk_eq_cycWalk_of_le h1 (NNReal.coe_nonneg s) hs, cycWalk_eq_cycPath h0]

end ElboimSly.Paper

end
