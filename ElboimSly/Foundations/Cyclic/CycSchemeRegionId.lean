/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeRegion
public import Mathlib

/-!
# The explored-region identity `Z_j(η) = cycReg(ρ_j(η))`

The environment scheme (a), "explored region" paragraph.

* `CycScheme.probeR_le_iff`: for `s ≤ h`, `{R ≤ s}` is the front region of the current walk (empty
  if ended).
* `CycScheme.region_upd_eq_probe`: the one-step identity
  `cycReg(ρ_{j+1}) = cycReg(ρ_j) ∪ {x ∉ cycReg(ρ_j) : R_j(x) ≤ min(r', h_j)}`, i.e. the recursion of
  `ExplScheme.Z`, for the pure scheme.
* `CycScheme.wf_stateAt`: every state along a history is well formed.
* `CycScheme.Z_eq_region`: for any `ExplScheme` whose raw probes and horizons are those of the pure
  scheme, `sch.Z k η = cycReg (ρ_k(η))`.
* `CycScheme.Rt_eq_probeM`: the masked probe is the segment probe with mask `cycReg(ρ_k(η))`, i.e.
  the raw probe restricted to the unexplored region.
* `CycScheme.region_stateAt_mono`: the regions grow along the history.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

open scoped Classical in
omit [Fact (0 < β)] in
/-- The cyclic segment probe with mask `Z` is the unmasked one, set to `∞` on `Z`. Same statement as `cycSegR_mask` in `CycSchemeInst`, without its `MeasurableSingletonClass I` assumption. -/
theorem cycSegR_mask' (A : Finset (I × Edge d)) (x : I × Edge d → ℝ → AddCircle β)
    (sinv : I × Edge d → AddCircle β → ℝ) (h : ℝ≥0) (Z : Set (CycS I d β)) (s : CycS I d β) :
    cycSegR A x sinv h Z s = if s ∈ Z then ⊤ else cycSegR A x sinv h ∅ s := by
  classical
  unfold cycSegR segR
  by_cases hs : s ∈ Z
  · have : (cycEquiv s) ∈ (cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z := by
      simpa using hs
    simp [hs, this]
  · have : (cycEquiv s) ∉ (cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z := by
      simpa using hs
    simp [hs, this]

namespace CycScheme

variable (P : CycPlan I d β) (sc : ℝ≥0∞)

/-- The masked probe of the scheme: the segment probe with mask `cycReg(ρ)`. -/
noncomputable def probeM (st : State I d) : CycS I d β → ℝ≥0∞ :=
  cycSegR (probeA P st) (circX (cur P st).frontT (cur P st).frontS)
    (circS (cur P st).frontT (cur P st).frontS) (hOf P sc st) (st.1.region β)

open scoped Classical in
/-- The masked probe is the raw probe restricted to the unexplored region. -/
theorem probeM_eq (st : State I d) (x : CycS I d β) :
    probeM P sc st x = if x ∈ st.1.region β then ⊤ else probeR P sc st x :=
  cycSegR_mask' _ _ _ _ _ _

omit [MeasurableSpace I] in
theorem circS_front (E : CycEntry I d) (e : I × Edge d) {t : ℝ≥0} (ht0 : 0 < t) (htb : (t : ℝ) ≤ β) :
    circS E.frontT E.frontS e (E.data.clock β (E.time + t)) = t := by
  rw [← CycEntry.circX_front E e t]
  exact circS_circX _ _ E.frontS_cases e ⟨by exact_mod_cast ht0, htb⟩

/-- The sublevel sets of the raw probe are the front regions of the current walk. -/
theorem probeR_le_iff (st : State I d) {s : ℝ≥0} (hs : s ≤ hOf P sc st) (x : CycS I d β) :
    probeR P sc st x ≤ (s : ℝ≥0∞) ↔
      x ∈ (if st.2 = true then ∅ else (cur P st).frontReg β s : Set (CycS I d β)) := by
  classical
  have hβ : (hOf P sc st : ℝ) ≤ β := hOf_le_beta P sc st
  have hsβ : (s : ℝ) ≤ β := (by exact_mod_cast hs : (s : ℝ) ≤ hOf P sc st).trans hβ
  obtain ⟨ι, e, θ⟩ := x
  unfold probeR
  rw [cycSegR_apply]
  unfold segR
  by_cases hb : st.2 = true
  · simp [probeA, hb]
  · simp only [probeA, hb, ite_false, Bool.false_eq_true, mem_cycMask_iff, Set.mem_empty_iff_false,
      not_false_eq_true, and_true, mem_edgesAt]
    split_ifs with hc
    · obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hc
      constructor
      · intro hle
        have h6 : circS (cur P st).frontT (cur P st).frontS (ι, e) θ ≤ s := by
          have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 hle
          simpa using this
        refine ⟨(circS (cur P st).frontT (cur P st).frontS (ι, e) θ).toNNReal, ?_, ?_, h1, ?_, h2⟩
        · exact Real.toNNReal_pos.2 h3
        · exact Real.toNNReal_le_iff_le_coe.2 h6
        · rw [← CycEntry.circX_front (cur P st) (ι, e) _, Real.coe_toNNReal _ h3.le]
          exact h5.symm
      · rintro ⟨t, ht0, hts, -, h7, -⟩
        have ht : θ = (cur P st).data.clock β ((cur P st).time + t) := h7
        rw [ht, circS_front _ _ ht0 ((by exact_mod_cast hts : (t : ℝ) ≤ s).trans hsβ),
          ENNReal.ofReal_coe_nnreal]
        exact_mod_cast hts
    · simp only [top_le_iff, ENNReal.coe_ne_top, false_iff]
      rintro ⟨t, ht0, hts, h1, h7, h2⟩
      apply hc
      have htb : (t : ℝ) ≤ β := (by exact_mod_cast hts : (t : ℝ) ≤ s).trans hsβ
      have ht : θ = (cur P st).data.clock β ((cur P st).time + t) := h7
      have hS := circS_front (cur P st) (ι, e) ht0 htb
      refine ⟨⟨h1, h2⟩, ?_, ?_, ?_⟩
      all_goals rw [ht]
      · rw [hS]; exact_mod_cast ht0
      · rw [hS]; exact_mod_cast hts.trans hs
      · rw [hS, ← CycEntry.circX_front]

end CycScheme

end ElboimSly.Cyclic

end
