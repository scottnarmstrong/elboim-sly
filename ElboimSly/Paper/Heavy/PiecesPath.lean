/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.CyclicPath
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import ElboimSly.Foundations.Cyclic.CPathLeft
public import ElboimSly.Foundations.Cyclic.CycPathType

/-!
# Cyclic walks are cyclic paths

The pieces are cyclic paths (a), first part (supplement).

* `isCyclicPath_of_cycPath`: a foundational `CycPath` with `fn 0 = 0` gives an `IsCyclicPath` on `ℝ`.
* `isCyclicPath_cycWalk`: for a good environment `μ`, `s ↦ cycWalk μ 0 0 s` is a cyclic path.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped NNReal ENNReal

namespace ElboimSly.Paper

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ}

theorem eventually_nhdsLT_toNNReal {r : ℝ} (hr : 0 < r) {P : ℝ≥0 → Prop}
    (h : ∀ᶠ u in 𝓝[<] r.toNNReal, P u) : ∀ᶠ u in 𝓝[<] r, P u.toNNReal := by
  have ht : Tendsto Real.toNNReal (𝓝[<] r) (𝓝[<] r.toNNReal) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (continuous_real_toNNReal.tendsto r).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun u hu =>
        (Real.toNNReal_lt_toNNReal_iff hr).2 hu
  exact ht.eventually h

theorem eventually_nhdsGE_toNNReal {r : ℝ} {P : ℝ≥0 → Prop}
    (h : ∀ᶠ u in 𝓝[≥] r.toNNReal, P u) : ∀ᶠ u in 𝓝[≥] r, P u.toNNReal := by
  have ht : Tendsto Real.toNNReal (𝓝[≥] r) (𝓝[≥] r.toNNReal) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (continuous_real_toNNReal.tendsto r).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun u hu => Real.toNNReal_le_toNNReal hu
  exact ht.eventually h

/-- A foundational `CycPath` is a cyclic path (on `[0, ∞)`). -/
theorem isCyclicPath_of_cycPath (p : CycPath d) (w : ℝ → Fin d → ℤ)
    (hw : ∀ s : ℝ, 0 ≤ s → w s = p.1.fn s.toNNReal) (h0 : w 0 = 0) : IsCyclicPath w where
  zero := h0
  rc s hs := by
    have := eventually_nhdsGE_toNNReal (r := s) (p.1.rc s.toNNReal)
    filter_upwards [this, self_mem_nhdsWithin] with u hu hu0
    rw [hw u (hs.trans hu0), hw s hs]
    exact hu
  fin T := by
    have hsub : cycJumpSet w ∩ Iic T ⊆
        (fun x : ℝ≥0 => (x : ℝ)) '' (CDisc p.1.fn ∩ Iic T.toNNReal) := by
      rintro r ⟨⟨hr0, hr⟩, hrT⟩
      refine ⟨r.toNNReal, ⟨⟨?_, ?_⟩, Real.toNNReal_le_toNNReal hrT⟩, Real.coe_toNNReal r hr0.le⟩
      · exact Real.toNNReal_pos.2 hr0
      · intro hev
        apply hr
        have := eventually_nhdsLT_toNNReal hr0 hev
        filter_upwards [this, Ioo_mem_nhdsLT hr0] with u hu hu0
        rw [hw u hu0.1.le, hw r hr0.le]
        exact hu
    exact ((p.1.fin T.toNNReal).image _).subset hsub
  jump_size r hr := by
    obtain ⟨hr0, hnev⟩ := hr
    have hr' : 0 < r.toNNReal := Real.toNNReal_pos.2 hr0
    have hmem : r.toNNReal ∈ CDisc p.1.fn := by
      refine ⟨hr', fun hev => hnev ?_⟩
      have := eventually_nhdsLT_toNNReal hr0 hev
      filter_upwards [this, Ioo_mem_nhdsLT hr0] with u hu hu0
      rw [hw u hu0.1.le, hw r hr0.le]
      exact hu
    have hsum := p.2 _ hmem
    have hev := eventually_nhdsLT_toNNReal hr0 (p.1.eventually_left hr')
    filter_upwards [hev, Ioo_mem_nhdsLT hr0] with u hu hu0
    rw [hw u hu0.1.le, hw r hr0.le, hu]
    rw [← hsum]

variable {β : ℝ} [Fact (0 < β)]

/-- For a good environment `μ`, the cyclic walk `W^μ_{0,0}` is a cyclic path. -/
theorem isCyclicPath_cycWalk {μ : Measure (RingSpace d β)} (hμ : Good μ) :
    IsCyclicPath (fun s : ℝ => cycWalk μ 0 0 s) := by
  have hex := isForwardPath_exists_cycPath (fwdTrajFn_spec hμ 0 0).1
  obtain ⟨p, -, hp⟩ := hex
  refine isCyclicPath_of_cycPath p _ (fun s hs => ?_) (cycWalk_zero hμ 0 0)
  have h := Classical.epsilon_spec (p := fun γ : ℝ≥0 → Fin d → ℤ => IsForwardTrajectory μ 0 0 γ)
    ⟨_, fwdTrajFn_spec hμ 0 0⟩
  simp only [ElboimSly.cycWalk, hs, ite_true]
  rw [hp, fwdTrajFn_eq hμ h]

end ElboimSly.Paper
