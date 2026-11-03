/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvCur
public import Mathlib

/-!
# The environment scheme (b): the raw probe on the front

The environment scheme (b), (i)--(ii). For an unfinished state the raw probe
`CycScheme.probeR` takes the value `t` at the front point `(ι, e, c_δ(r + t))`, `e ∋ w`,
`t ∈ (0, h]` (`probeR_front`), and is finite only at such points (`front_of_probeR_ne_top`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal
namespace ElboimSly.Cyclic
namespace CycScheme
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
variable (P : CycPlan I d β) (sc : ℝ≥0∞)

omit [Countable I] [MeasurableSingletonClass I] in
theorem probeR_front {st : State I d} (hst : st.2 = false) {e : Edge d} {t : ℝ≥0}
    (he : Edge.Mem (cur P st).pos e) (ht0 : 0 < t) (hth : t ≤ hOf P sc st) :
    probeR P sc st (frontPt β (cur P st) e t) = (t : ℝ≥0∞) := by
  have htβ : (t : ℝ) ∈ Ioc 0 β := ⟨by exact_mod_cast ht0, (by exact_mod_cast hth : (t:ℝ) ≤ hOf P sc st).trans (hOf_le_beta P sc st)⟩
  unfold probeR
  unfold frontPt
  rw [cycSegR_apply]
  have h1 : (cur P st).data.clock β ((cur P st).time + t) =
      circX (cur P st).frontT (cur P st).frontS ((cur P st).data.copy, e) (t : ℝ) :=
    (CycEntry.circX_front (cur P st) _ t).symm
  have hs : circS (cur P st).frontT (cur P st).frontS ((cur P st).data.copy, e)
      ((cur P st).data.clock β ((cur P st).time + t)) = t := by
    rw [h1]; exact circS_circX _ _ (cur P st).frontS_cases _ htβ
  unfold segR
  rw [ite_eq_left]
  · simp only [hs]; simp
  · refine ⟨?_, ?_, by simp⟩
    · simp [probeA, hst, mem_edgesAt, he]
    · refine ⟨?_, ?_, ?_⟩
      · simp only [hs]; exact_mod_cast ht0
      · simp only [hs]; exact_mod_cast hth
      · simp only [hs]; exact h1.symm

omit [Countable I] [MeasurableSingletonClass I] in
theorem front_of_probeR_ne_top {st : State I d} (hst : st.2 = false) {y : CycS I d β}
    (hy : probeR P sc st y ≠ ⊤) :
    ∃ (e : Edge d) (t : ℝ≥0), y = frontPt β (cur P st) e t ∧ Edge.Mem (cur P st).pos e ∧ 0 < t ∧
      t ≤ hOf P sc st ∧ probeR P sc st y = (t : ℝ≥0∞) := by
  obtain ⟨ι, e, θ⟩ := y
  unfold probeR at hy ⊢
  rw [cycSegR_apply] at hy ⊢
  unfold segR at hy ⊢
  by_cases hc : ((ι, e) ∈ probeA P st ∧ θ ∈ segImg (circX (cur P st).frontT (cur P st).frontS)
      (circS (cur P st).frontT (cur P st).frontS) (hOf P sc st) (ι, e) ∧
      ((ι, e), θ) ∉ (cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' (∅ : Set (CycS I d β)))
  · rw [ite_eq_left hc] at hy ⊢
    obtain ⟨hA, ⟨h0, hh, hx⟩, -⟩ := hc
    have hA' : (ι, e) ∈ edgesAt (cur P st).data.copy (cur P st).pos := by
      simpa [probeA, hst] using hA
    rw [mem_edgesAt] at hA'
    obtain ⟨hι, hmem⟩ := hA'
    set t := (circS (cur P st).frontT (cur P st).frontS (ι, e) θ).toNNReal with ht
    have htr : (t : ℝ) = circS (cur P st).frontT (cur P st).frontS (ι, e) θ :=
      Real.coe_toNNReal _ h0.le
    refine ⟨e, t, ?_, hmem, ?_, ?_, ?_⟩
    · unfold frontPt
      refine Prod.ext hι (Prod.ext rfl ?_)
      show θ = _
      have := hx.symm
      rw [← htr] at this
      exact this.trans (CycEntry.circX_front (cur P st) (ι, e) t)
    · rw [← NNReal.coe_pos, htr]; exact h0
    · rw [← NNReal.coe_le_coe, htr]; exact hh
    · rw [ENNReal.ofReal, ht]
  · rw [ite_eq_right hc] at hy
    exact absurd rfl hy
end CycScheme
end ElboimSly.Cyclic

end
