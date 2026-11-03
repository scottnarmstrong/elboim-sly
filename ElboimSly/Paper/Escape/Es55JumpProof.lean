/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55JumpProofDet
public import ElboimSly.Paper.Escape.Es55Step1
public import Mathlib

/-!
# `es55Jump`: the regenerated walk of a Poisson environment does not jump at a fixed time

ES22 Lemma 5.5, Step 1.  A jump of the regenerated walk at `t` needs a ring atom of some
environment `N''(m, ·)` at the cyclic time `[t]`; such atoms are a.s. absent because the
intensity of `{m} × {e} × {[t]}` is zero (`Leb` has no atoms).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {k : ℕ}

/-- A Poisson point process has a.s. no points in a set of intensity zero. -/
theorem ppp_ae_zero {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {N : Ω → Measure S}
    {μ : Measure S} {P : Measure Ω} (hN : IsPoissonPointProcess N μ P) {A : Set S}
    (hA : MeasurableSet A) (h : μ A = 0) : ∀ᵐ ω ∂P, N ω A = 0 := by
  have h1 := hN.2.1 A hA
  rw [h, extPoissonMeasure_zero] at h1
  have hm : AEMeasurable (fun ω => N ω A) P :=
    (Measure.measurable_coe hA |>.comp hN.1).aemeasurable
  have : ∀ᵐ x ∂(P.map (fun ω => N ω A)), x = 0 := by
    rw [h1, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  exact (ae_map_iff hm (measurableSet_singleton _)).1 this

theorem intensity_atom_zero (m : ℕ) (e : Edge d) (θ : AddCircle β) :
    ((Measure.count : Measure ℕ).prod (ringIntensity d β)) {(m, (e, θ))} = 0 := by
  have : ({(m, (e, θ))} : Set (ℕ × RingSpace d β)) = {m} ×ˢ ({e} ×ˢ {θ}) := by simp
  rw [this, Measure.prod_prod]
  unfold ringIntensity
  rw [Measure.prod_prod]
  simp

theorem ae_noRings {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N'' : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
    (t : ℝ) : ∀ᵐ ω ∂Pr, ∀ m e, ¬ Rings (cycSlice m (N'' ω)) e t := by
  rw [ae_all_iff]; intro m
  rw [ae_all_iff]; intro e
  filter_upwards [ppp_ae_zero hN (measurableSet_singleton (m, (e, ((t : ℝ) : AddCircle β))))
    (intensity_atom_zero m e _)] with ω hω hr
  have h1 : 1 ≤ cycSlice m (N'' ω) {(e, ((t : ℝ) : AddCircle β))} := hr
  have h2 : cycSlice m (N'' ω) {(e, ((t : ℝ) : AddCircle β))} = 0 := by
    unfold cycSlice
    rw [(measurableEmbedding_prodMk_left m).comap_apply]
    simpa using hω
  rw [h2] at h1
  simp at h1

theorem rc_regenW {Ω : Type} {N'' : Ω → Measure (ℕ × RingSpace d β)} {ω : Ω}
    (hg : CycGood (N'' ω)) : RC (regenW N'' ω) := by
  intro s
  obtain ⟨ε, hε, hc⟩ := regenWalk_const_near (ν := fun k => cycSlice k (N'' ω)) hg
    (t := (s : ℝ)) s.2
  have hlt : s < s + ε.toNNReal := by
    have : (0 : ℝ≥0) < ε.toNNReal := Real.toNNReal_pos.2 hε
    exact lt_add_of_pos_right _ this
  filter_upwards [Ico_mem_nhdsGE hlt] with u hu
  have hu1 : (s : ℝ) ≤ u := by exact_mod_cast hu.1
  have hu2 : (u : ℝ) < s + ε := by
    have := (NNReal.coe_lt_coe.2 hu.2)
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
  exact hc u hu1 hu2

/-- **`es55Jump`.** The regenerated walk of a Poisson environment a.s. does not jump at a fixed
time `t > 0`. -/
theorem es55Jump : Es55Jump k := by
  intro β _ Ω _ Pr N'' hN t ht
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_cycGood hN, ae_noRings hN t] with ω hg hno
  rw [not_not]
  rw [noJumpRat_iff (rc_regenW hg) ht]
  obtain ⟨l, hl0, hlt, hl⟩ := regenWalk_left_const (ν := fun k => cycSlice k (N'' ω)) hg ht hno
  refine ⟨l, hl0, hlt, fun s hs1 hs2 => ?_⟩
  have h0 : 0 ≤ s := hl0.trans hs1.le
  have := hl s hs1 hs2
  simpa [regenW, Real.coe_toNNReal _ h0, Real.coe_toNNReal _ ht.le] using this

end ElboimSly.Paper.Escape
