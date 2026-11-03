/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Adapted
public import ElboimSly.Paper.Avoid.Claim2Final
public import Mathlib

/-!
# The coupled walk as a `CPath`-valued random variable

ES22 Claim 5.6, use of ES22 Lemma 2.1.  `escCPath M` is measurable, independent of
`ℱ_T` when `avoidPath (cycNgood M)` is, and has the same law as `escCPath N` when the paths do.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω]

theorem measurable_escCPath {M : Ω → Measure (CycS ℕ d β)}
    (hM : Measurable (avoidPath (cycNgood M))) : Measurable (escCPath M) := by
  rw [CPath.measurable_iff]
  refine ⟨measurable_const, fun s => ?_⟩
  exact (measurable_pi_apply s).comp hM

omit mΩ in
theorem escCPath_preimage {M : Ω → Measure (CycS ℕ d β)} {B : Set (CPath (Fin d → ℤ))}
    (hB : MeasurableSet B) :
    ∃ B' : Set (ℝ≥0 → Fin d → ℤ), MeasurableSet B' ∧
      ∀ ω, (escCPath M ω ∈ B ↔ avoidPath (cycNgood M) ω ∈ B') := by
  obtain ⟨B'', hB'', rfl⟩ := hB
  refine ⟨Prod.mk (⊤ : ℝ≥0∞) ⁻¹' B'', measurable_prodMk_left hB'', fun ω => Iff.rfl⟩

omit mΩ in
theorem comap_escCPath_le {M : Ω → Measure (CycS ℕ d β)} :
    MeasurableSpace.comap (escCPath M) inferInstance ≤
      MeasurableSpace.comap (avoidPath (cycNgood M)) inferInstance := by
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨B', hB', h⟩ := escCPath_preimage (M := M) hB
  refine ⟨B', hB', ?_⟩
  ext ω
  exact (h ω).symm

theorem indep_escCPath {M : Ω → Measure (CycS ℕ d β)} {Pr : Measure Ω} {H : MeasurableSpace Ω}
    (h : Indep H (MeasurableSpace.comap (avoidPath (cycNgood M)) inferInstance) Pr) :
    Indep H (MeasurableSpace.comap (escCPath M) inferInstance) Pr :=
  indep_of_indep_of_le_right h comap_escCPath_le

theorem map_escCPath_eq {M N : Ω → Measure (CycS ℕ d β)} {Pr : Measure Ω}
    (hM : Measurable (avoidPath (cycNgood M)))
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
    (hlaw : Pr.map (avoidPath (cycNgood M)) = Pr.map (avoidPath N)) :
    Pr.map (escCPath M) = Pr.map (escCPath N) := by
  have hNg : Measurable (avoidPath (cycNgood N)) :=
    measurable_avoidPath_cycNgood hN.measurable
  ext B hB
  rw [Measure.map_apply (measurable_escCPath hM) hB,
    Measure.map_apply (measurable_escCPath hNg) hB]
  obtain ⟨B'', hB'', rfl⟩ := hB
  have hB' : MeasurableSet (Prod.mk (⊤ : ℝ≥0∞) ⁻¹' B'') := measurable_prodMk_left hB''
  have e1 : escCPath M ⁻¹' ((fun p : CPath (Fin d → ℤ) => (p.len, p.fn)) ⁻¹' B'') =
      avoidPath (cycNgood M) ⁻¹' (Prod.mk (⊤ : ℝ≥0∞) ⁻¹' B'') := rfl
  have e2 : escCPath N ⁻¹' ((fun p : CPath (Fin d → ℤ) => (p.len, p.fn)) ⁻¹' B'') =
      avoidPath (cycNgood N) ⁻¹' (Prod.mk (⊤ : ℝ≥0∞) ⁻¹' B'') := rfl
  rw [e1, e2, ← Measure.map_apply hM hB', hlaw, Measure.map_apply_of_aemeasurable
    (aemeasurable_avoidPath hN) hB']
  refine measure_congr ?_
  filter_upwards [ae_cycNgood_eq hN] with ω hω
  have : avoidPath N ω = avoidPath (cycNgood N) ω := by
    funext s; exact (congrFun (avoidWalk_congr hω) _).symm
  simp only [mem_preimage, this]

end ElboimSly.Paper.Escape

end
