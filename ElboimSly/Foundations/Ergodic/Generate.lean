/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Ergodic.Shift
import Mathlib

/-!
# The law of the ring process, local events generate, approximation

Properties of translations and local σ-algebras (c), local events generate, approximation by local events.

`edgeFin n` is the finite set of the first `n` edges in the enumeration of `Edge d` by
`Encodable.encode`; `ringLaw` is the law `Π_{μ_β}` of a PPP with intensity `μ_β`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ}

/-! ### The law `Π` -/

theorem exists_ringLaw (d : ℕ) (β : ℝ) [Fact (0 < β)] :
    ∃ Λ : Measure (Measure (RingSpace d β)),
      IsPoissonPointProcess (id : Measure (RingSpace d β) → _) (ringIntensity d β) Λ := by
  obtain ⟨Ω, _, P, N, _, h, _⟩ := exists_isPoissonPointProcess_ringIntensity d β
  exact ⟨P.map N, h.of_map_eq measurable_id (by simp)⟩

/-- The law `Π_{μ_β}` of a Poisson point process with intensity `μ_β`, on the space of measures.
Translations and local σ-algebras. -/
noncomputable def ringLaw (d : ℕ) (β : ℝ) [Fact (0 < β)] : Measure (Measure (RingSpace d β)) :=
  (exists_ringLaw d β).choose

theorem isPoissonPointProcess_ringLaw [Fact (0 < β)] :
    IsPoissonPointProcess (id : Measure (RingSpace d β) → _) (ringIntensity d β)
      (ringLaw d β) :=
  (exists_ringLaw d β).choose_spec

instance isProbabilityMeasure_ringLaw [Fact (0 < β)] : IsProbabilityMeasure (ringLaw d β) :=
  isPoissonPointProcess_ringLaw.isProbabilityMeasure

/-- Uniqueness in law: the law of every PPP with intensity `μ_β` is `ringLaw`. -/
theorem map_eq_ringLaw [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (RingSpace d β)} (h : IsPoissonPointProcess N (ringIntensity d β) P) :
    P.map N = ringLaw d β := by
  simpa using isPoissonPointProcess_ringLaw.map_eq_map h

/-- Properties of translations and local σ-algebras (c): `ϑ_z` preserves `Π`. -/
theorem measurePreserving_thetaShift [Fact (0 < β)] (z : Fin d → ℤ) :
    MeasurePreserving (thetaShift d β z) (ringLaw d β) (ringLaw d β) := by
  refine ⟨measurable_thetaShift z, ?_⟩
  have := isPoissonPointProcess_ringLaw.map_measure_law_eq (φ := ringShift d β z)
    (measurable_ringShift z) (map_ringShift_ringIntensity z)
  rw [Measure.map_id] at this
  exact this

/-! ### Enumeration of edges -/

/-- The first `n` edges in the enumeration given by `Encodable.encode`. -/
def edgeFin (d : ℕ) (n : ℕ) : Set (Edge d) :=
  {e | (@Encodable.encode _ (Encodable.ofCountable (Edge d)) e) < n}

theorem edgeFin_finite (n : ℕ) : (edgeFin d n).Finite := by
  let := Encodable.ofCountable (Edge d)
  exact (Set.finite_Iio n).preimage (Encodable.encode_injective.injOn)

theorem edgeFin_mono {n m : ℕ} (h : n ≤ m) : edgeFin d n ⊆ edgeFin d m :=
  fun _ he => lt_of_lt_of_le he h

theorem iUnion_edgeFin : ⋃ n, edgeFin d n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  exact Set.mem_iUnion.2 ⟨_ + 1, Nat.lt_succ_self _⟩

/-! ### Local events generate -/

/-- The algebra `𝒜_loc = ⋃ₙ 𝔐_{F_n}` of local events. -/
def localAlgebra (d : ℕ) (β : ℝ) : Set (Set (Measure (RingSpace d β))) :=
  {A | ∃ n, MeasurableSet[locSigma d β (edgeFin d n)] A}

/-- Local events generate: `𝒜_loc` is an algebra of sets. -/
theorem isSetAlgebra_localAlgebra : MeasureTheory.IsSetAlgebra (localAlgebra d β) where
  empty_mem := ⟨0, @MeasurableSet.empty _ (locSigma d β (edgeFin d 0))⟩
  compl_mem := fun _ ⟨n, hn⟩ => ⟨n, hn.compl⟩
  union_mem := by
    rintro s t ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, MeasurableSet.union ?_ ?_⟩
    · exact locSigma_mono (edgeFin_mono (le_max_left n m)) _ hn
    · exact locSigma_mono (edgeFin_mono (le_max_right n m)) _ hm

theorem measurableSet_of_mem_localAlgebra {A : Set (Measure (RingSpace d β))}
    (h : A ∈ localAlgebra d β) : MeasurableSet A := by
  obtain ⟨n, hn⟩ := h
  exact locSigma_le _ _ hn

/-- Local events generate: `σ(𝒜_loc) = 𝔐`. -/
theorem generateFrom_localAlgebra :
    MeasurableSpace.generateFrom (localAlgebra d β) =
      (inferInstance : MeasurableSpace (Measure (RingSpace d β))) := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun A hA => measurableSet_of_mem_localAlgebra hA
  · set M' := MeasurableSpace.generateFrom (localAlgebra d β) with hM'
    have hle : ∀ n, locSigma d β (edgeFin d n) ≤ M' := fun n A hA =>
      MeasurableSpace.measurableSet_generateFrom ⟨n, hA⟩
    have hev : ∀ B, MeasurableSet B →
        @Measurable _ _ M' _ (fun ν : Measure (RingSpace d β) => ν B) := by
      intro B hB
      have hmono : Monotone fun n => B ∩ (edgeFin d n ×ˢ (Set.univ : Set (AddCircle β))) :=
        fun n m h => Set.inter_subset_inter_right _ (Set.prod_mono (edgeFin_mono h) le_rfl)
      have hU : ⋃ n, B ∩ (edgeFin d n ×ˢ (Set.univ : Set (AddCircle β))) = B := by
        ext x
        constructor
        · rintro hx
          obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
          exact hn.1
        · intro hx
          have : x.1 ∈ ⋃ n, edgeFin d n := by rw [iUnion_edgeFin]; trivial
          obtain ⟨n, hn⟩ := Set.mem_iUnion.1 this
          exact Set.mem_iUnion.2 ⟨n, hx, hn, trivial⟩
      have hfun : (fun ν : Measure (RingSpace d β) => ν B) =
          fun ν => ⨆ n, resMeas d β (edgeFin d n) ν B := by
        funext ν
        simp only [resMeas, Measure.restrict_apply hB]
        rw [← hmono.measure_iUnion, hU]
      rw [hfun]
      refine Measurable.iSup fun n => ?_
      have h1 : @Measurable _ _ (locSigma d β (edgeFin d n)) _
          (fun ν : Measure (RingSpace d β) => resMeas d β (edgeFin d n) ν B) :=
        @Measurable.comp _ _ _ (locSigma d β (edgeFin d n)) _ _ _ _
          (Measure.measurable_coe hB) (comap_measurable _)
      exact h1.mono (hle n) le_rfl
    show (⨆ s, ⨆ _ : MeasurableSet s,
      MeasurableSpace.comap (fun μ : Measure (RingSpace d β) => μ s) inferInstance) ≤ M'
    refine iSup₂_le fun B hB => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    exact hev B hB

/-! ### Approximation by local events -/

/-- Approximation by local events. -/
theorem exists_localEvent_measure_symmDiff_lt [Fact (0 < β)]
    {A : Set (Measure (RingSpace d β))} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∃ A' : Set (Measure (RingSpace d β)), MeasurableSet[locSigma d β (edgeFin d n)] A' ∧
      ringLaw d β (symmDiff A' A) < ε := by
  obtain ⟨t, ⟨n, ht⟩, hlt⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := ringLaw d β) isSetAlgebra_localAlgebra.isSetRing
    ⟨{Set.univ}, by simp, by
      simp only [Set.singleton_subset_iff]
      exact ⟨0, @MeasurableSet.univ _ (locSigma d β (edgeFin d 0))⟩, by simp⟩
    generateFrom_localAlgebra.symm hA hε
  exact ⟨n, t, ht, hlt⟩

end ElboimSly
