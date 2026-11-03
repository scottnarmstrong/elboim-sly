/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.JumpSrw
public import ElboimSly.Foundations.Cyclic.CycFastStat
public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import ElboimSly.Foundations.Cyclic.CycStationary
public import Mathlib

/-!
# Fast jumping is unlikely, Step 1: one window of the cyclic walk

Fast jumping is unlikely, Step 1. For a Poisson environment `ν` on `S_β` with `β ≥ 2` and the
cyclic walk `W = W^ν_{0,0}`, every window `(m, m + 2]` satisfies
`P(J_W(m, m + 2] ≥ k) ≤ exp (4 d (e - 1) - k)` (`jump_window_prob`).

The proof transfers the event to the canonical SRW on `[0, β]` by `cyc_srw_short_law`
(`law_short_core`), and to a window at time `m` by `cyc_stationary` (stationary increments of the cyclic walk).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.SRW ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Extension of a path on `[0, b]` to `[0, ∞)` by the constant `g b`. -/
def extendIic (b : ℝ≥0) (g : Set.Iic b → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  fun s => g ⟨min s b, min_le_right _ _⟩

theorem measurable_extendIic (b : ℝ≥0) : Measurable (extendIic (d := d) b) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem extendIic_restrictIic_mem_jgeSet {b : ℝ≥0} (hb : (2 : ℝ≥0) ≤ b) (f : ℝ≥0 → Fin d → ℤ)
    (k : ℕ) : extendIic b (restrictIic b f) ∈ jgeSet d k 0 2 ↔ f ∈ jgeSet d k 0 2 := by
  unfold jgeSet
  simp only [mem_ofPred_eq]
  refine JGE_congr k 0 2 (by norm_num) fun x hx => ?_
  have hx2 : x.toNNReal ≤ b := by
    refine le_trans ?_ hb
    exact Real.toNNReal_le_iff_le_coe.2 (by simpa using hx.2)
  simp [extendIic, restrictIic, min_eq_left hx2]

variable {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {ν : Ω → Measure (RingSpace d β)}

/-- The first-window event for the trajectory: `P(JGE (W) k 0 2) ≤ exp (4 d (e - 1) - k)`. -/
theorem trajFn_jge_prob (hβ : 2 ≤ β)
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (k : ℕ) :
    Pe.real {ω | trajFn (ν ω) ∈ jgeSet d k 0 2} ≤
      Real.exp (4 * d * (Real.exp 1 - 1) - k) := by
  obtain ⟨Ω', _, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hb : (2 : ℝ≥0) ≤ β.toNNReal := by
    rw [← NNReal.coe_le_coe]
    simpa [Real.coe_toNNReal _ (Fact.out : 0 < β).le] using hβ
  set b : ℝ≥0 := β.toNNReal with hbdef
  have hS := measurableSet_jgeSet (d := d) k 0 2
  have hS' : MeasurableSet (extendIic b ⁻¹' jgeSet d k 0 2) := measurable_extendIic b hS
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  have hF : Measurable fun ω => restrictIic b (trajFn (ν ω)) :=
    (measurable_restrictIic b).comp (measurable_trajFn.comp hν.measurable)
  have hG : Measurable fun ω => restrictIic b (canonical d (N₀) ω) :=
    (measurable_restrictIic b).comp (by
      refine measurable_pi_iff.2 fun s => ?_
      exact measurable_walk d (s : ℝ) |>.comp hN₀.measurable)
  have hlaw : Pe.map (fun ω => restrictIic b (trajFn (ν ω))) =
      Pd.map (fun ω => restrictIic b (canonical d N₀ ω)) := by
    rw [← law_short_core hν hN₀]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    funext s
    simp [trajFn, restrictIic, cycWalk_eq_trajProc hω]
  have e1 : {ω | trajFn (ν ω) ∈ jgeSet d k 0 2} =
      (fun ω => restrictIic b (trajFn (ν ω))) ⁻¹' (extendIic b ⁻¹' jgeSet d k 0 2) := by
    ext ω
    exact (extendIic_restrictIic_mem_jgeSet hb _ k).symm
  have e2 : (fun ω => restrictIic b (canonical d N₀ ω)) ⁻¹' (extendIic b ⁻¹' jgeSet d k 0 2) =
      {ω | JGE (srwReal (N₀ ω)) k 0 2} := by
    ext ω
    have := extendIic_restrictIic_mem_jgeSet hb (canonical d N₀ ω) k
    exact this.trans Iff.rfl
  have h3 : Pe {ω | trajFn (ν ω) ∈ jgeSet d k 0 2} =
      Pd {ω | JGE (srwReal (N₀ ω)) k 0 2} := by
    rw [e1, ← e2, ← Measure.map_apply hF hS', ← Measure.map_apply hG hS', hlaw]
  have h4 : Pe.real {ω | trajFn (ν ω) ∈ jgeSet d k 0 2} =
      Pd.real {ω | JGE (srwReal (N₀ ω)) k 0 2} := by
    simp only [Measure.real]
    rw [h3]
  rw [h4]
  exact srw_jge_prob hN₀ k

/-- The window event for the cyclic walk at the integer time `m`:
`P(J_W(m, m + 2] ≥ k) ≤ exp (4 d (e - 1) - k)`. -/
theorem jump_window_prob (hβ : 2 ≤ β)
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (k m : ℕ) :
    Pe.real {ω | k ≤ cycJumpCount (fun s : ℝ => cycWalk (ν ω) 0 0 s) (m : ℝ) ((m : ℝ) + 2)} ≤
      Real.exp (4 * d * (Real.exp 1 - 1) - k) := by
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  have hS := measurableSet_jgeSet (d := d) k 0 2
  set a : ℝ≥0 := (m : ℝ≥0) with ha
  have hsub : {ω | k ≤ cycJumpCount (fun s : ℝ => cycWalk (ν ω) 0 0 s) (m : ℝ) ((m : ℝ) + 2)} ≤ᵐ[Pe]
      {ω | shiftTraj a (ν ω) ∈ jgeSet d k 0 2} := by
    filter_upwards [hgood] with ω hω hk
    have hcyc := isCyclicPath_cycWalk hω
    have hsh := isCyclicPath_shiftPath hcyc (a := (m : ℝ)) (Nat.cast_nonneg m)
    have h1 : k ≤ cycJumpCount (shiftPath (fun s : ℝ => cycWalk (ν ω) 0 0 s) (m : ℝ)) 0 2 := by
      rw [cycJumpCount_shiftPath _ _ _ (Nat.cast_nonneg m)]
      exact hk
    have h2 := jGE_of_le hsh k 0 2 le_rfl (by norm_num) h1
    show JGE (fun s : ℝ => shiftTraj a (ν ω) s.toNNReal) k 0 2
    refine (JGE_congr k 0 2 (by norm_num) fun x hx => ?_).1 h2
    have hx0 : max x 0 = x := max_eq_left hx.1
    simp only [shiftPath, hx0, shiftTraj]
    have e1 := cycWalk_eq_trajProc hω 0 0 (a + x.toNNReal)
    have e2 := cycWalk_eq_trajProc hω 0 0 a
    have e3 : (((a + x.toNNReal : ℝ≥0)) : ℝ) = (m : ℝ) + x := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ hx.1]; simp [ha]
    rw [e3] at e1
    rw [e1]
    have e4 : ((a : ℝ≥0) : ℝ) = (m : ℝ) := by simp [ha]
    rw [e4] at e2
    rw [e2]
  have hst : Pe.map (fun ω => shiftTraj a (ν ω)) = Pe.map (fun ω => trajFn (ν ω)) :=
    cyc_stationary hν a
  have hm1 : Measurable fun ω => shiftTraj a (ν ω) :=
    (measurable_shiftTraj a).comp hν.measurable
  have hm2 : Measurable fun ω => trajFn (ν ω) := measurable_trajFn.comp hν.measurable
  have h1 : Pe {ω | shiftTraj a (ν ω) ∈ jgeSet d k 0 2} =
      Pe {ω | trajFn (ν ω) ∈ jgeSet d k 0 2} := by
    have : Pe (((fun ω => shiftTraj a (ν ω))) ⁻¹' jgeSet d k 0 2) =
        Pe (((fun ω => trajFn (ν ω))) ⁻¹' jgeSet d k 0 2) := by
      rw [← Measure.map_apply hm1 hS, ← Measure.map_apply hm2 hS, hst]
    exact this
  have := hν.isProbabilityMeasure
  calc Pe.real _ ≤ Pe.real {ω | shiftTraj a (ν ω) ∈ jgeSet d k 0 2} := measureReal_mono_ae' hsub
    _ = Pe.real {ω | trajFn (ν ω) ∈ jgeSet d k 0 2} := by
        simp only [Measure.real]; rw [h1]
    _ ≤ _ := trajFn_jge_prob hβ hν k

end ElboimSly.Paper.Heavy
