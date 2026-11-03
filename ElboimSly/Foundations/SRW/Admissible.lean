/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.MarkovIndep
public import Mathlib

/-!
# Admissible filtrations; the Markov property for every SRW

Path space, laws, SRWs, admissible filtrations (d), (e); Markov property for every SRW; admissible filtrations; independent stationary increments; Markov property at fixed times (b).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The natural filtration `ℱ^Z_t = σ(Z(s) : s ≤ t)`. -/
@[instance_reducible] def natFil (Z : Ω → PathSpace d) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ s ≤ t, MeasurableSpace.comap (fun ω => Z ω s) inferInstance

/-- Path space, laws, SRWs, admissible filtrations (e): `F` is admissible for `Z`. -/
structure IsAdmissible (P : Measure Ω) (Z : Ω → PathSpace d) (F : ℝ≥0 → MeasurableSpace Ω) :
    Prop where
  mono : Monotone F
  le : ∀ t, F t ≤ mΩ
  adapted : ∀ s t, s ≤ t → Measurable[F t] (fun ω => Z ω s)
  indep : ∀ t, Indep (MeasurableSpace.comap (fun ω => theta t (Z ω)) inferInstance) (F t) P

theorem natFil_le {Z : Ω → PathSpace d} (hZ : Measurable Z) (t : ℝ≥0) : natFil Z t ≤ mΩ :=
  iSup₂_le fun s _ => ((measurable_pi_apply s).comp hZ).comap_le

omit mΩ in
theorem natFil_mono (Z : Ω → PathSpace d) : Monotone (natFil Z) := fun _ _ h =>
  iSup₂_le fun s hs => le_iSup₂_of_le s (hs.trans h) le_rfl

omit mΩ in
theorem measurable_natFil (Z : Ω → PathSpace d) {s t : ℝ≥0} (h : s ≤ t) :
    Measurable[natFil Z t] (fun ω => Z ω s) := by
  intro u hu
  exact (le_iSup₂_of_le s h le_rfl :
    MeasurableSpace.comap (fun ω => Z ω s) inferInstance ≤ natFil Z t) _ ⟨u, hu, rfl⟩

/-- If `𝒢` is independent of `𝒜 ≥ ℬ ⊔ 𝒞` and `ℬ`, `𝒞` are independent, then `𝒢 ⊔ ℬ` and `𝒞`
are independent. -/
theorem indep_sup_of_indep {m𝒢 mB mC mA : MeasurableSpace Ω} (h𝒢 : m𝒢 ≤ mΩ) (hB : mB ≤ mΩ)
    (hC : mC ≤ mΩ) (hBA : mB ≤ mA) (hCA : mC ≤ mA) (_hA : mA ≤ mΩ)
    (hi : Indep m𝒢 mA P) (hj : Indep mB mC P) [IsProbabilityMeasure P] :
    Indep (m𝒢 ⊔ mB) mC P := by
  let p1 : Set (Set Ω) :=
    {s | ∃ A B, MeasurableSet[m𝒢] A ∧ MeasurableSet[mB] B ∧ s = A ∩ B}
  have hp1 : IsPiSystem p1 := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ _
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', by ext; simp; tauto⟩
  have hgen : m𝒢 ⊔ mB = MeasurableSpace.generateFrom p1 := by
    apply le_antisymm
    · refine sup_le (fun s hs => ?_) (fun s hs => ?_)
      · exact MeasurableSpace.measurableSet_generateFrom ⟨s, univ, hs, MeasurableSet.univ, by simp⟩
      · exact MeasurableSpace.measurableSet_generateFrom ⟨univ, s, MeasurableSet.univ, hs, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨A, B, hA, hB, rfl⟩
      exact (le_sup_left (a := m𝒢) (b := mB) _ hA).inter (le_sup_right (a := m𝒢) (b := mB) _ hB)
  have hpC : IsPiSystem {s | MeasurableSet[mC] s} := @MeasurableSpace.isPiSystem_measurableSet Ω mC
  have hgC : mC = MeasurableSpace.generateFrom {s | MeasurableSet[mC] s} :=
    (@MeasurableSpace.generateFrom_measurableSet Ω mC).symm
  refine IndepSets.indep (sup_le h𝒢 hB) hC hp1 hpC hgen hgC ?_
  rw [IndepSets_iff]
  rintro _ C ⟨A, B, hA, hB, rfl⟩ hC'
  have hBA' : MeasurableSet[mA] B := hBA _ hB
  have hCA' : MeasurableSet[mA] C := hCA _ hC'
  have e1 : P (A ∩ B ∩ C) = P A * P (B ∩ C) := by
    rw [inter_assoc]
    exact ((Indep_iff _ _ _).1 hi) A (B ∩ C) hA (hBA' |>.inter hCA')
  have e2 : P (A ∩ B) = P A * P B := ((Indep_iff _ _ _).1 hi) A B hA hBA'
  have e3 : P (B ∩ C) = P B * P C := ((Indep_iff _ _ _).1 hj) B C hB hC'
  rw [e1, e2, e3, mul_assoc]

end SRW
end ElboimSly
