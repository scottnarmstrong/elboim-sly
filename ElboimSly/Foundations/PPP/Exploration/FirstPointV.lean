/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointB
public import ElboimSly.Foundations.PPP.Exploration.Atoms
public import ElboimSly.Foundations.PPP.Giry
import Mathlib

/-!
# First-point law: the law of the revealed configuration

First-point law of a deterministic probe, proof of "The law": on `{D(h) hit}`, `V` has law
`ι_*(1_{D(h)} e^{-m∘R} · μ)` with `ι(x) = δ_x`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

/-- `ι_*(1_{D(h)} e^{-m∘R} · μ)`, the law of the revealed configuration on `{D(h) hit}`. -/
noncomputable def diracLaw (μ : Measure S) (R : S → ℝ≥0∞) (h : ℝ≥0) : Measure (Measure S) :=
  ((μ.restrict (probeRegion R h)).withDensity fun x => expNeg (probeMass μ R (R x))).map
    Measure.dirac

omit [SigmaFinite μ] in
theorem diracLaw_apply (_hR : Measurable R) {s : Set (Measure S)} (hs : MeasurableSet s) :
    diracLaw μ R h s = ∫⁻ x in Measure.dirac ⁻¹' s ∩ probeRegion R h,
      expNeg (probeMass μ R (R x)) ∂μ := by
  unfold diracLaw
  rw [Measure.map_apply Measure.measurable_dirac hs,
    withDensity_apply _ (Measure.measurable_dirac hs), Measure.restrict_restrict
      (Measure.measurable_dirac hs)]

omit [SigmaFinite μ] in
theorem ae_atomReg (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) {l : ℕ} {B : Fin l → Set S}
    (hB : ∀ i, MeasurableSet (B i)) :
    ∀ᵐ ν ∂W, ∀ ε : Fin l → Bool, Reg R h (atom B ε) ν :=
  ae_reg hW hP.measurable hP.mass_lt_top (fun ε => measurableSet_atom hB ε)

theorem map_probeV_restrict (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) :
    (W.restrict {ν | 1 ≤ tau μ ν (probeRegion R h)}).map (probeV μ R h) = diracLaw μ R h := by
  classical
  have hR := hP.measurable
  have := hW.isProbabilityMeasure
  have hsuccm : MeasurableSet {ν : Measure S | 1 ≤ tau μ ν (probeRegion R h)} :=
    measurableSet_le measurable_const
      ((Measure.measurable_coe (measurableSet_probeRegion hR h)).comp (measurable_tau μ))
  have hV := measurable_probeV μ (h := h) hR
  have key : ∀ s ∈ countEvents S,
      (W.restrict {ν | 1 ≤ tau μ ν (probeRegion R h)}).map (probeV μ R h) s =
        diracLaw μ R h s := by
    intro s' hs'
    obtain ⟨l, B, C0, hB, hC0, rfl⟩ := hs'
    have hs : MeasurableSet {ν : Measure S | (fun i => ν (B i)) ∈ C0} :=
      countEvents_measurableSet ⟨l, B, C0, hB, hC0, rfl⟩
    set T : Finset (Fin l → Bool) :=
      Finset.univ.filter fun ε => (fun i => if ε i then (1 : ℝ≥0∞) else 0) ∈ C0 with hT
    rw [Measure.map_apply hV hs, Measure.restrict_apply (hV hs), diracLaw_apply hR hs]
    have hgood := ae_goodSet hW hP MeasurableSet.univ
    have hatom := ae_atomReg hW hP hB
    have hae : (probeV μ R h ⁻¹' {ν : Measure S | (fun i => ν (B i)) ∈ C0} ∩
        {ν : Measure S | 1 ≤ tau μ ν (probeRegion R h)} : Set (Measure S)) =ᵐ[W]
        (⋃ ε ∈ T, firstEvent μ R h (atom B ε) : Set (Measure S)) := by
      filter_upwards [hgood, ae_succ_V_univ hW hP hh, hatom] with ν hν hV1 hreg
      obtain ⟨hlf, hreg0, -, -⟩ := hν
      apply propext
      constructor
      · rintro ⟨hsν, hsucc⟩
        have h1 := hV1 hsucc
        have hint : ∀ ε : Fin l → Bool, ∃ n : ℕ, probeV μ R h ν (atom B ε) = n := by
          intro ε
          rw [probeV_apply hlf hR (measurableSet_atom hB ε)]
          exact exists_natCast_measure_region hR (measurableSet_atom hB ε) (hreg ε)
        obtain ⟨ε₀, hε₀⟩ := exists_atom_eq_one hB h1 hint
        have hBi := measure_eq_of_atom hB h1 hε₀
        simp only [Set.mem_iUnion]
        refine ⟨ε₀, ?_, hsucc, h1, hε₀⟩
        rw [hT, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have : (fun i => probeV μ R h ν (B i)) = fun i => if ε₀ i then (1 : ℝ≥0∞) else 0 :=
          funext hBi
        rw [← this]; exact hsν
      · intro hmem
        simp only [Set.mem_iUnion] at hmem
        obtain ⟨ε, hεT, hsucc, h1, hε⟩ := hmem
        refine ⟨?_, hsucc⟩
        have hBi := measure_eq_of_atom hB h1 hε
        rw [hT, Finset.mem_filter] at hεT
        have : (fun i => probeV μ R h ν (B i)) = fun i => if ε i then (1 : ℝ≥0∞) else 0 :=
          funext hBi
        show (fun i => probeV μ R h ν (B i)) ∈ C0
        rw [this]; exact hεT.2
    rw [measure_congr hae, measure_biUnion_finset]
    · have hset : Measure.dirac ⁻¹' {ν : Measure S | (fun i => ν (B i)) ∈ C0} ∩ probeRegion R h =
          ⋃ ε ∈ T, (probeRegion R h ∩ atom B ε) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion,
          hT, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hx, hxD⟩
          refine ⟨fun i => decide (x ∈ B i), ?_, hxD, mem_atom.2 fun i => by simp⟩
          have : (fun i => if decide (x ∈ B i) = true then (1 : ℝ≥0∞) else 0) =
              fun i => Measure.dirac x (B i) := by
            funext i
            rw [Measure.dirac_apply' _ (hB i)]
            simp [Set.indicator]
          rw [this]; exact hx
        · rintro ⟨ε, hε, hxD, hxα⟩
          refine ⟨?_, hxD⟩
          have : (fun i => Measure.dirac x (B i)) = fun i => if ε i then (1 : ℝ≥0∞) else 0 := by
            funext i
            rw [Measure.dirac_apply' _ (hB i)]
            have := (mem_atom.1 hxα i)
            by_cases hxi : x ∈ B i
            · simp [Set.indicator, hxi, this.1 hxi]
            · have : ε i ≠ true := fun e => hxi (this.2 e)
              simp [Set.indicator, hxi, this]
          show (fun i => Measure.dirac x (B i)) ∈ C0
          rw [this]; exact hε
      rw [hset, lintegral_biUnion_finset]
      · refine Finset.sum_congr rfl fun ε _ => ?_
        rw [measure_firstEvent hW hP hh (measurableSet_atom hB ε)]
        rfl
      · intro ε _ ε' _ hne
        exact (pairwise_disjoint_atom B hne).mono Set.inter_subset_right Set.inter_subset_right
      · exact fun ε _ => (measurableSet_probeRegion hR h).inter (measurableSet_atom hB ε)
    · intro ε _ ε' _ hne
      rw [Function.onFun, Set.disjoint_left]
      rintro ν ⟨-, h1, h2⟩ ⟨-, -, h3⟩
      have := measure_atom_eq_zero hB h1 h2 (Ne.symm hne)
      rw [this] at h3
      exact absurd h3 (by simp)
    · exact fun ε _ => measurableSet_firstEvent hR (measurableSet_atom hB ε)
  refine ext_of_generate_finite (countEvents S) generateFrom_countEvents.symm
    isPiSystem_countEvents key (key _ univ_mem_countEvents)

end ElboimSly
