/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Ergodic.Generate
public import ElboimSly.Foundations.PPP.Restriction
import Mathlib

/-!
# Mixing

Mixing.

Uses restriction (b), independence of restrictions to disjoint sets.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff

namespace ElboimSly

variable {d : ℕ} {β : ℝ}

theorem indep_locSigma [Fact (0 < β)] {F G : Set (Edge d)}
    (hFG : Disjoint F G) : Indep (locSigma d β F) (locSigma d β G) (ringLaw d β) :=
  isPoissonPointProcess_ringLaw.indepFun_restrict (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.univ)
    (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.univ)
    (Set.disjoint_prod.2 (Or.inl hFG))

theorem measureReal_thetaShift_preimage [Fact (0 < β)] (z : Fin d → ℤ)
    {S : Set (Measure (RingSpace d β))} (hS : MeasurableSet S) :
    (ringLaw d β).real (thetaShift d β z ⁻¹' S) = (ringLaw d β).real S := by
  simp only [Measure.real]
  rw [(measurePreserving_thetaShift z).measure_preimage hS.nullMeasurableSet]

theorem measureReal_inter_thetaShift [Fact (0 < β)]
    {F : Set (Edge d)} {z : Fin d → ℤ} (hz : Disjoint F (edgeShift z ⁻¹' F))
    {A B : Set (Measure (RingSpace d β))} (hA : MeasurableSet[locSigma d β F] A)
    (hB : MeasurableSet[locSigma d β F] B) :
    (ringLaw d β).real (A ∩ thetaShift d β z ⁻¹' B) =
      (ringLaw d β).real A * (ringLaw d β).real B := by
  have hind := (Indep_iff _ _ _).1 (indep_locSigma hz) A (thetaShift d β z ⁻¹' B) hA
    (measurableSet_locSigma_preimage_thetaShift z hB)
  have hBm : MeasurableSet B := locSigma_le _ _ hB
  have hpre := measureReal_thetaShift_preimage (β := β) z hBm
  simp only [Measure.real] at hpre ⊢
  rw [hind, ENNReal.toReal_mul, hpre]

theorem abs_mul_sub_mul_le {a a' b b' : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb' : 0 ≤ b')
    (hb1' : b' ≤ 1) :
    |a' * b' - a * b| ≤ |a' - a| + |b' - b| := by
  have e : a' * b' - a * b = (a' - a) * b' + a * (b' - b) := by ring
  rw [e]
  calc |(a' - a) * b' + a * (b' - b)| ≤ |(a' - a) * b'| + |a * (b' - b)| := abs_add_le _ _
    _ = |a' - a| * b' + a * |b' - b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hb', abs_of_nonneg ha]
    _ ≤ |a' - a| * 1 + 1 * |b' - b| := by gcongr
    _ = _ := by ring

theorem symmDiff_inter_subset {α : Type*} (A A' X X' : Set α) :
    (A ∩ X) ∆ (A' ∩ X') ⊆ (A ∆ A') ∪ (X ∆ X') := by
  intro x hx
  simp only [Set.symmDiff_def, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff] at hx ⊢
  tauto

theorem preimage_symmDiff' {α γ : Type*} (f : α → γ) (S T : Set γ) :
    f ⁻¹' (S ∆ T) = (f ⁻¹' S) ∆ (f ⁻¹' T) := by
  ext x; simp [Set.symmDiff_def]

/-- Mixing, uses restriction (b). -/
theorem ringLaw_mixing [Fact (0 < β)]
    {A B : Set (Measure (RingSpace d β))} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : Fin d → ℤ, R < ‖z‖ →
      |(ringLaw d β).real (A ∩ thetaShift d β z ⁻¹' B) -
        (ringLaw d β).real A * (ringLaw d β).real B| ≤ ε := by
  have hε4 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := by simpa using (by positivity : 0 < ε / 4)
  obtain ⟨n₁, A', hA', hAA⟩ := exists_localEvent_measure_symmDiff_lt hA hε4
  obtain ⟨n₂, B', hB', hBB⟩ := exists_localEvent_measure_symmDiff_lt hB hε4
  have hA'n : MeasurableSet[locSigma d β (edgeFin d (max n₁ n₂))] A' :=
    locSigma_mono (edgeFin_mono (le_max_left _ _)) _ hA'
  have hB'n : MeasurableSet[locSigma d β (edgeFin d (max n₁ n₂))] B' :=
    locSigma_mono (edgeFin_mono (le_max_right _ _)) _ hB'
  obtain ⟨R, hR⟩ := exists_disjoint_edgeShift (edgeFin_finite (d := d) (max n₁ n₂))
  refine ⟨R, fun z hz => ?_⟩
  have hA'm : MeasurableSet A' := locSigma_le _ _ hA'
  have hB'm : MeasurableSet B' := locSigma_le _ _ hB'
  have hθ : MeasurableSet (thetaShift d β z ⁻¹' B) := measurable_thetaShift z hB
  have hθ' : MeasurableSet (thetaShift d β z ⁻¹' B') := measurable_thetaShift z hB'm
  have hind := measureReal_inter_thetaShift (hR z hz) hA'n hB'n
  have eA : (ringLaw d β).real (A' ∆ A) < ε / 4 := by
    simpa [Measure.real] using ENNReal.toReal_lt_of_lt_ofReal hAA
  have eB : (ringLaw d β).real (B' ∆ B) < ε / 4 := by
    simpa [Measure.real] using ENNReal.toReal_lt_of_lt_ofReal hBB
  have dA : |(ringLaw d β).real A' - (ringLaw d β).real A| ≤ (ringLaw d β).real (A' ∆ A) :=
    abs_measureReal_sub_le_measureReal_symmDiff hA'm.nullMeasurableSet hA.nullMeasurableSet
  have dB : |(ringLaw d β).real B' - (ringLaw d β).real B| ≤ (ringLaw d β).real (B' ∆ B) :=
    abs_measureReal_sub_le_measureReal_symmDiff hB'm.nullMeasurableSet hB.nullMeasurableSet
  have s1 : |(ringLaw d β).real (A ∩ thetaShift d β z ⁻¹' B) -
      (ringLaw d β).real (A' ∩ thetaShift d β z ⁻¹' B')| ≤
      (ringLaw d β).real (A ∆ A') + (ringLaw d β).real (B ∆ B') := by
    refine (abs_measureReal_sub_le_measureReal_symmDiff (hA.inter hθ).nullMeasurableSet
      (hA'm.inter hθ').nullMeasurableSet).trans ?_
    refine (measureReal_mono (symmDiff_inter_subset _ _ _ _)).trans ?_
    refine (measureReal_union_le _ _).trans ?_
    rw [← preimage_symmDiff', measureReal_thetaShift_preimage z (hB.symmDiff hB'm)]
  have s2 := abs_mul_sub_mul_le (a := (ringLaw d β).real A) (a' := (ringLaw d β).real A')
    (b := (ringLaw d β).real B) (b' := (ringLaw d β).real B') measureReal_nonneg
    measureReal_le_one measureReal_nonneg measureReal_le_one
  rw [symmDiff_comm A A', symmDiff_comm B B'] at s1
  rw [← hind] at s2
  have := abs_sub_le ((ringLaw d β).real (A ∩ thetaShift d β z ⁻¹' B))
    ((ringLaw d β).real (A' ∩ thetaShift d β z ⁻¹' B')) ((ringLaw d β).real A *
      (ringLaw d β).real B)
  linarith

end ElboimSly
