/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78H1Rat
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Frozen.Defs.CycClosesBy
public import ElboimSly.Frozen.Defs.CycTreg
public import ElboimSly.Paper.Heavy.PiecesPath
public import ElboimSly.Foundations.Cyclic.CycMeasurable
public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe
public import Mathlib

/-!
# The regenerated walk agrees with its first piece before closing

Support for the event cH_1 (the event `Osc_1`). If the first piece `W_{0,0}` of a regenerated walk
does not close by time `c`, then the regenerated walk equals it on `[0, c]` (`ℛ` of the constructions of the regenerated walk,
construction (i)). Consequently, the probability (for a single Poisson environment) that `W_{0,0}`
does not close by `T` and violates `Osc` on `[0, T]` is at most the probability, for the regenerated
walk of an auxiliary Poisson environment on `ℕ × ℝ^2`-space, of a rational violation in `[0, c]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- If `W_{0,0}` does not close by `c`, then `t_reg > c`. -/
theorem ofReal_lt_cycTreg {ν : Measure (RingSpace d β)} {c : ℝ} (hc : 0 ≤ c)
    (hcl : ¬ cycClosesBy ν 0 0 c) : ENNReal.ofReal c < cycTreg ν := by
  have hβ : 0 < β := Fact.out
  set k1 : ℕ := ⌊c / β⌋₊ + 1 with hk1
  have hk1c : c < k1 * β := by
    have := Nat.lt_floor_add_one (c / β)
    rw [div_lt_iff₀ hβ] at this
    exact_mod_cast this
  calc ENNReal.ofReal c < ENNReal.ofReal (k1 * β) :=
        (ENNReal.ofReal_lt_ofReal_iff (by nlinarith [Nat.cast_nonneg (α := ℝ) k1])).2 hk1c
    _ ≤ cycTreg ν := by
        unfold cycTreg
        refine le_iInf fun k => ENNReal.ofReal_le_ofReal ?_
        obtain ⟨k, hk1', hk0⟩ := k
        have hkc : c < k * β := by
          by_contra hle
          exact hcl ⟨k, hk1', not_lt.1 hle, hk0⟩
        have : (k1 : ℝ) ≤ k := by
          by_contra hlt
          push Not at hlt
          have : (k : ℝ) * β ≤ k1 * β := by nlinarith
          have h2 : (k : ℝ) < k1 := hlt
          have hk' : k < ⌊c / β⌋₊ + 1 := by exact_mod_cast h2
          have : k ≤ ⌊c / β⌋₊ := by omega
          have h3 : (k : ℝ) ≤ c / β := (Nat.le_floor_iff (div_nonneg hc hβ.le)).1 this
          rw [le_div_iff₀ hβ] at h3
          linarith
        nlinarith

omit [Fact (0 < β)] in
/-- The regenerated walk equals its first piece on `[0, c]` if that piece does not close by `c`. -/
theorem regenWalk_eq_first {ν : ℕ → Measure (RingSpace d β)} {c t : ℝ} (_ht0 : 0 ≤ t) (htc : t ≤ c)
    (hc : ENNReal.ofReal c < cycTreg (ν 0)) : regenWalk ν t = cycWalk (ν 0) 0 0 t := by
  have hset : {i : ℕ | regenSigma ν i ≤ ENNReal.ofReal t} = {0} := by
    ext i
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro hi
      by_contra hne
      have h1 : regenSigma ν 1 ≤ regenSigma ν i := by
        unfold regenSigma
        exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      have h2 : regenSigma ν 1 = cycTreg (ν 0) := by simp [regenSigma]
      rw [h2] at h1
      have := hc.trans_le (h1.trans hi)
      exact absurd (ENNReal.ofReal_le_ofReal htc) (not_le.2 this)
    · rintro rfl
      simp [regenSigma]
  have hcnt : regenCount ν t = 0 := by
    unfold regenCount; rw [hset]; simp
  unfold regenWalk regenStart
  rw [hcnt]
  simp [regenSigma]

/-- Cyclic closing of a good environment in terms of `trajProc`. -/
theorem cycClosesBy_iff_trajProc {ν : Measure (RingSpace d β)} (hν : Good ν) (c : ℝ) :
    cycClosesBy ν 0 0 c ↔ ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) * β ≤ c ∧
      trajProc ν 0 0 (((k : ℝ) * β).toNNReal) = 0 := by
  have hβ : 0 < β := Fact.out
  unfold cycClosesBy
  refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ => ?_
  have h0 : 0 ≤ (k : ℝ) * β := by positivity
  rw [← cycWalk_eq_trajProc hν 0 0, Real.coe_toNNReal _ h0]

/-- The violation set on the environment space. -/
def h1EnvBad (d : ℕ) (β : ℝ) [Fact (0 < β)] (T' c : ℝ≥0) (h r : ℝ) :
    Set (Measure (RingSpace d β)) :=
  (fun ν (t : Set.Icc (0 : ℝ≥0) T') => trajProc ν 0 0 (t : ℝ≥0)) ⁻¹' h1OscBad T' c h r \
    {ν | ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) * β ≤ c ∧ trajProc ν 0 0 (((k : ℝ) * β).toNNReal) = 0}

theorem measurableSet_h1EnvBad (T' c : ℝ≥0) (h r : ℝ) :
    MeasurableSet (h1EnvBad d β T' c h r) := by
  refine MeasurableSet.diff ?_ ?_
  · refine (measurableSet_h1OscBad T' c h r).preimage ?_
    exact measurable_pi_iff.2 fun t => (measurable_pi_apply (t : ℝ≥0)).comp (measurable_trajProc 0 0)
  · have : {ν : Measure (RingSpace d β) | ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) * β ≤ c ∧
        trajProc ν 0 0 (((k : ℝ) * β).toNNReal) = 0} =
        ⋃ k : ℕ, ⋃ (_ : 1 ≤ k ∧ (k : ℝ) * β ≤ c),
          {ν | trajProc ν 0 0 (((k : ℝ) * β).toNNReal) = 0} := by
      ext ν; simp [and_assoc]
    rw [this]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
    exact (measurableSet_singleton (0 : Fin d → ℤ)).preimage
      ((measurable_pi_apply _).comp (measurable_trajProc 0 0))

/-- A good environment that does not close by `T` and violates `Osc` on `[0, T]` lies in
`h1EnvBad`. -/
theorem mem_h1EnvBad {ν : Measure (RingSpace d β)} (hν : Good ν) {T c T' : ℝ≥0} (hT : T < c)
    (hcT : c ≤ T') {h r : ℝ} (hh : 0 < h)
    (hcβ : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * β ≤ c → (k : ℝ) * β ≤ T)
    (hcl : ¬ cycClosesBy ν 0 0 T)
    (hbad : ¬ ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T, |s - s'| ≤ h →
      ‖cycWalk ν 0 0 s - cycWalk ν 0 0 s'‖ ≤ r) : ν ∈ h1EnvBad d β T' c h r := by
  refine ⟨?_, fun hB => ?_⟩
  · simp only [not_forall, not_le] at hbad
    obtain ⟨s, hs, s', hs', hd, hlt⟩ := hbad
    have hw := isCyclicPath_cycWalk hν
    have hrc : ∀ x : ℝ, 0 ≤ x → ∀ᶠ u in 𝓝[≥] x, cycWalk ν 0 0 u = cycWalk ν 0 0 x :=
      fun x hx => hw.rc x hx
    have key : ∀ s s' : ℝ, s ∈ Icc (0 : ℝ) T → s' ∈ Icc (0 : ℝ) T → s ≤ s' → |s - s'| ≤ h →
        r < ‖cycWalk ν 0 0 s - cycWalk ν 0 0 s'‖ →
        (fun (t : Set.Icc (0 : ℝ≥0) T') => trajProc ν 0 0 (t : ℝ≥0)) ∈ h1OscBad T' c h r := by
      intro s s' hs hs' hss hd hlt
      obtain ⟨a, b, ha, hb, hab, hac, hbc, hGa, hGb⟩ := exists_rat_approx hrc hT hcT hh hs.1 hss
        hs'.2 (by rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hd; exact hd)
      refine mem_iUnion₂.2 ⟨(a, b), ⟨ha, hb, hab, hac, hbc⟩, ?_⟩
      show r < ‖trajProc ν 0 0 a.1 - trajProc ν 0 0 b.1‖
      rw [← cycWalk_eq_trajProc hν, ← cycWalk_eq_trajProc hν, hGa, hGb]
      exact hlt
    rcases le_total s s' with h1 | h1
    · exact key s s' hs hs' h1 hd hlt
    · refine key s' s hs' hs h1 (by rwa [abs_sub_comm]) ?_
      rwa [norm_sub_rev]
  · obtain ⟨k, hk1, hkc, hk0⟩ := hB
    refine hcl ⟨k, hk1, hcβ k hk1 hkc, ?_⟩
    have h0 : 0 ≤ (k : ℝ) * β := by
      have : 0 < β := Fact.out
      positivity
    rw [← Real.coe_toNNReal _ h0, cycWalk_eq_trajProc hν]
    exact hk0

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Transfer of the `Osc` violation from a single Poisson environment to the regenerated walk of an
auxiliary Poisson environment on `ℕ × RingSpace`. -/
theorem step78_osc_transfer {P : Measure Ω} {N₀ : Ω → Measure (RingSpace d β)}
    (hN₀ : IsPoissonPointProcess N₀ (ringIntensity d β) P) {P' : Measure Ω'}
    {N' : Ω' → Measure (ℕ × RingSpace d β)}
    (hN' : IsPoissonPointProcess N' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P')
    {T c T' : ℝ≥0} (hT : T < c) (hcT : c ≤ T') {h r : ℝ} (hh : 0 < h)
    (hcβ : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * β ≤ c → (k : ℝ) * β ≤ T) :
    P {ω | ¬ cycClosesBy (N₀ ω) 0 0 T ∧ ¬ ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T,
        |s - s'| ≤ h → ‖cycWalk (N₀ ω) 0 0 s - cycWalk (N₀ ω) 0 0 s'‖ ≤ r} ≤
      P' ((fun ω' (t : Set.Icc (0 : ℝ≥0) T') =>
          regenWalk (fun k => copyEnv (N' ω') k) ((t : ℝ≥0) : ℝ)) ⁻¹' h1OscBad T' c h r) := by
  have hM := measurableSet_h1EnvBad (d := d) (β := β) T' c h r
  have h0 := isPoissonPointProcess_slice hN' 0
  have hlaw : P'.map (fun ω => cycSlice 0 (N' ω)) = P.map N₀ := hN₀.map_eq_map h0
  have := hN₀.isProbabilityMeasure
  have hA : P {ω | ¬ cycClosesBy (N₀ ω) 0 0 T ∧ ¬ ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T,
        |s - s'| ≤ h → ‖cycWalk (N₀ ω) 0 0 s - cycWalk (N₀ ω) 0 0 s'‖ ≤ r} ≤
      P (N₀ ⁻¹' h1EnvBad d β T' c h r) := by
    refine measure_mono_ae ?_
    filter_upwards [ae_good hN₀] with ω hω hx
    exact mem_h1EnvBad hω hT hcT hh hcβ hx.1 hx.2
  have hB : P (N₀ ⁻¹' h1EnvBad d β T' c h r) =
      P' ((fun ω => cycSlice 0 (N' ω)) ⁻¹' h1EnvBad d β T' c h r) := by
    rw [← Measure.map_apply hN₀.measurable hM, ← Measure.map_apply h0.measurable hM, hlaw]
  refine hA.trans (hB.le.trans (measure_mono_ae ?_))
  filter_upwards [ae_cycGood hN'] with ω hω hx
  have hg0 := hω 0
  obtain ⟨hxA, hxB⟩ := hx
  have hcl : ¬ cycClosesBy (cycSlice 0 (N' ω)) 0 0 c := fun hcl =>
    hxB ((cycClosesBy_iff_trajProc hg0 c).1 hcl)
  have htreg := ofReal_lt_cycTreg (by positivity) hcl
  obtain ⟨x, hxp, hxlt⟩ := mem_iUnion₂.1 hxA
  refine mem_iUnion₂.2 ⟨x, hxp, ?_⟩
  have e : ∀ a : Set.Icc (0 : ℝ≥0) T', (a : ℝ≥0) ≤ c →
      regenWalk (fun k => copyEnv (N' ω) k) ((a : ℝ≥0) : ℝ) =
        trajProc (cycSlice 0 (N' ω)) 0 0 (a : ℝ≥0) := by
    intro a hac
    have := regenWalk_eq_first (ν := fun k => copyEnv (N' ω) k) (c := (c : ℝ))
      (NNReal.coe_nonneg _) (by exact_mod_cast hac) (by rw [copyEnv_eq_cycSlice]; exact htreg)
    rw [this, copyEnv_eq_cycSlice]
    exact cycWalk_eq_trajProc hg0 0 0 _
  show r < ‖regenWalk (fun k => copyEnv (N' ω) k) ((x.1 : ℝ≥0) : ℝ) -
    regenWalk (fun k => copyEnv (N' ω) k) ((x.2 : ℝ≥0) : ℝ)‖
  rw [e x.1 hxp.2.2.2.1, e x.2 hxp.2.2.2.2]
  exact hxlt

end ElboimSly.Paper.Step

end
