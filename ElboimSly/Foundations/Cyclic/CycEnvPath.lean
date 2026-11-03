/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycLines
public import ElboimSly.Foundations.Interchange.TrajApi
public import ElboimSly.Frozen.Defs.Rings
public import ElboimSly.Frozen.Defs.IsForwardPath
public import Mathlib

/-!
# The environment path is a nearest-neighbour path obeying the swap rule

Basic properties of world-lines (a) (first part): for good `ν`, `P^ν_δ` lies in `CycPath`,
`P(0) = u`, and obeys the swap rule in terms of the atoms of `ν`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)]

theorem latticeAdj_of_edge {z w : Fin d → ℤ} (e : Edge d) (h : e.1 = s(z, w)) :
    ∑ i, |w i - z i| = 1 := by
  obtain ⟨u, v, huv, hadj⟩ := e.2
  rw [h] at huv
  have hadj' : ∑ i, |u i - v i| = 1 := hadj
  rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [← hadj']; exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  · exact hadj'

omit [Fact (0 < β)] in
/-- A forward path is a `CycPath` of length `∞`. -/
theorem isForwardPath_exists_cycPath {μ : Measure (RingSpace d β)} {a : ℝ}
    {γ : ℝ≥0 → Fin d → ℤ} (h : IsForwardPath μ a γ) :
    ∃ p : CycPath d, p.1.len = ⊤ ∧ p.1.fn = γ := by
  obtain ⟨hrc, hll, hfin, hswap⟩ := h
  have hdisc : ∀ s ∈ CDisc γ, 0 < s ∧ ∃ z, IsLeftLimit γ s z ∧ z ≠ γ s := by
    intro s ⟨hs0, hs1⟩
    obtain ⟨z, hz⟩ := hll s hs0
    refine ⟨hs0, z, hz, fun hzz => hs1 ?_⟩
    filter_upwards [hz] with u hu using hu.trans hzz
  let q : CPath (Fin d → ℤ) :=
    ⟨⊤, γ, hrc, fun T => hfin T |>.subset fun s hs => by
      obtain ⟨hs0, z, hz, hne⟩ := hdisc s hs.1
      exact ⟨hs0, hs.2, z, hz, hne⟩, fun s s' h _ => absurd h (by simp)⟩
  refine ⟨⟨q, fun s hs => ?_⟩, rfl, rfl⟩
  obtain ⟨hs0, z, hz, hne⟩ := hdisc s hs
  have hl : q.left s = z := q.left_eq_of_eventually hs0 hz
  show ∑ i, |q.fn s i - q.left s i| = 1
  rw [hl]
  have hsw := hswap s hs0 z hz
  have hex : ∃ e : Edge d, e.Mem z ∧ Rings μ e (a + s) := by
    by_contra hno
    exact hne (hsw.2 hno).symm
  obtain ⟨e, he, hre⟩ := hex
  exact latticeAdj_of_edge e (hsw.1 e he hre)

omit [Fact (0 < β)] in
theorem cycSlice_singleton (ι : I) (ν : Measure (I × RingSpace d β)) (x : RingSpace d β) :
    cycSlice ι ν {x} = ν {(ι, x)} := by
  unfold cycSlice
  rw [(measurableEmbedding_prodMk_left ι).comap_apply]
  simp

omit [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem good_envMeasure {ν : Measure (I × RingSpace d β)} {δ : CycData I d}
    (h : Good (cycSlice δ.copy ν)) : Good (envMeasure ν δ) := by
  unfold envMeasure
  split_ifs
  · exact h
  · exact good_reflectMeasure h

omit [Fact (0 < β)] in
theorem rings_envMeasure (ν : Measure (I × RingSpace d β)) (δ : CycData I d) (e : Edge d)
    (r : ℝ≥0) :
    Rings (envMeasure ν δ) e (δ.sgn * δ.phase + r) ↔
      1 ≤ ν {(δ.copy, (e, δ.clock β r))} := by
  have key : ∀ t : ℝ, Rings (cycSlice δ.copy ν) e t ↔
      1 ≤ ν {(δ.copy, (e, (t : AddCircle β)))} := fun t => by
    unfold Rings ringSet
    simp only [Set.mem_ofPred_eq, cycSlice_singleton]
  by_cases hf : δ.fwd = true
  · have hs : δ.sgn = 1 := by simp [CycData.sgn, hf]
    have h1 : (δ.sgn * δ.phase + r : ℝ) = (δ.phase + δ.sgn * r : ℝ) := by rw [hs]; ring
    simp only [envMeasure, hf, ite_true, h1, CycData.clock]
    exact key _
  · have hs : δ.sgn = -1 := by simp [CycData.sgn, hf]
    have h1 : -(δ.sgn * δ.phase + r : ℝ) = (δ.phase + δ.sgn * r : ℝ) := by rw [hs]; ring
    simp only [envMeasure, hf, Bool.false_eq_true, ite_false]
    rw [rings_reflectMeasure, h1, key]
    rfl

omit [MeasurableSingletonClass I] in
theorem envFn_spec {ν : Measure (I × RingSpace d β)} {δ : CycData I d}
    (h : Good (cycSlice δ.copy ν)) :
    IsForwardTrajectory (envMeasure ν δ) δ.start (δ.sgn * δ.phase) (envFn ν δ) :=
  Classical.epsilon_spec (p := fun γ => IsForwardTrajectory (envMeasure ν δ) δ.start
    (δ.sgn * δ.phase) γ) ⟨_, fwdTrajFn_spec (good_envMeasure h) _ _⟩

omit [MeasurableSingletonClass I] in
theorem envPath_len {ν : Measure (I × RingSpace d β)} {δ : CycData I d}
    (h : Good (cycSlice δ.copy ν)) : (envPath ν δ).1.len = ⊤ ∧ (envPath ν δ).1.fn = envFn ν δ := by
  have hex : ∃ p : CycPath d, p.1.len = ⊤ ∧ p.1.fn = envFn ν δ :=
    isForwardPath_exists_cycPath (envFn_spec h).1
  unfold envPath
  rw [dite_eq_left hex]
  exact hex.choose_spec

omit [MeasurableSingletonClass I] in
theorem envPath_zero {ν : Measure (I × RingSpace d β)} {δ : CycData I d}
    (h : Good (cycSlice δ.copy ν)) : (envPath ν δ).1.fn 0 = δ.start := by
  rw [(envPath_len h).2]
  exact (envFn_spec h).2

/-- Environment swap rule, in terms of the atoms of `ν`. Basic properties of world-lines (a). -/
theorem envPath_swap {ν : Measure (I × RingSpace d β)} {δ : CycData I d}
    (h : Good (cycSlice δ.copy ν)) {r : ℝ≥0} (hr : 0 < r) :
    (∀ e : Edge d, Edge.Mem ((envPath ν δ).1.left r) e →
      1 ≤ ν {(δ.copy, (e, δ.clock β r))} →
        e.1 = s((envPath ν δ).1.left r, (envPath ν δ).1.fn r)) ∧
    ((¬ ∃ e : Edge d, Edge.Mem ((envPath ν δ).1.left r) e ∧
        1 ≤ ν {(δ.copy, (e, δ.clock β r))}) →
      (envPath ν δ).1.fn r = (envPath ν δ).1.left r) := by
  have hL : IsLeftLimit (envFn ν δ) r ((envPath ν δ).1.left r) := by
    have := (envPath ν δ).1.eventually_left hr
    rwa [(envPath_len h).2] at this
  have hsw := (envFn_spec h).1.2.2.2 r hr _ hL
  rw [← (envPath_len h).2] at hsw
  refine ⟨fun e he hat => hsw.1 e he ?_, fun hn => hsw.2 fun ⟨e, he, hrg⟩ =>
    hn ⟨e, he, (rings_envMeasure ν δ e r).mp (by exact hrg)⟩⟩
  exact (rings_envMeasure ν δ e r).mpr hat

end ElboimSly.Cyclic

end
