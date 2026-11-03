/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactProbA
public import ElboimSly.Foundations.SRW.TransienceDiff
public import ElboimSly.Foundations.SRW.TransienceMain
public import ElboimSly.Foundations.SRW.Modulus
public import Mathlib

/-!
# The probability of the escape scenario

Contacts are few (ii), "Probability of the scenario": `P(X̄ ∈ Γ_{y₀}) ≥ c₁`, with
`c₁ = e^{-4d} c_esc(d)`.

* `es8CEsc d = e^{-2d} / (2 R!)`: the constant `c_esc(d)` of transience: escape from the unit box.
* `es8C1 d = e^{-4d} c_esc(d)`.
* `prob_contactGamma`: `c₁ ≤ P(X̄ ∈ Γ_{y₀})` when `0 < ‖y₀‖ ≤ 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

/-- Constants and thresholds of the base: the constant `c_esc(d)` of transience: escape from the unit box. -/
noncomputable def es8CEsc (d : ℕ) : ℝ := Real.exp (-(2 * d)) / (2 * (escR d).factorial)

/-- Constants and thresholds of the base: `c₁(d) = e^{-4d} c_esc(d)`. -/
noncomputable def es8C1 (d : ℕ) : ℝ := Real.exp (-(4 * d)) * es8CEsc d

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

/-- The part of `Γ` determined by times at most `1`. -/
def escA [NeZero d] (y₀ : Fin d → ℤ) : Set (PathSpace (d + d)) :=
  {γ | fstP γ 1 = 0 ∧ sndP γ 1 = (escDir y₀).vec ∧
    ∀ q : ℚ, 0 ≤ q → q ≤ 1 → fstP γ (ratNN q) = 0 ∧
      (sndP γ (ratNN q) = 0 ∨ sndP γ (ratNN q) = (escDir y₀).vec)}

/-- The part of `Γ` determined by the shifted path `θ₁ x̄`. -/
def escB [NeZero d] (y₀ : Fin d → ℤ) : Set (PathSpace (d + d)) :=
  {γ | ∀ q : ℚ, 0 ≤ q → 2 ≤ ‖(y₀ + (escDir y₀).vec) + (sndP γ (ratNN q) - fstP γ (ratNN q))‖}

theorem mem_escGamma_iff [NeZero d] (y₀ : Fin d → ℤ) (γ : PathSpace (d + d)) :
    γ ∈ contactGamma y₀ ↔ γ ∈ escA y₀ ∧ theta 1 γ ∈ escB y₀ := by
  have e : ∀ q : ℚ, sndP (theta 1 γ) (ratNN q) - fstP (theta 1 γ) (ratNN q) =
      (sndP γ (1 + ratNN q) - fstP γ (1 + ratNN q)) - (sndP γ 1 - fstP γ 1) := by
    intro q; funext i
    simp only [sndP, fstP, theta, Pi.sub_apply]; ring
  simp only [contactGamma, escA, escB, mem_ofPred_eq, e, and_assoc]

theorem measurableSet_escB [NeZero d] (y₀ : Fin d → ℤ) : MeasurableSet (escB y₀) := by
  have : escB y₀ = ⋂ q : ℚ, {γ | (γ (ratNN q), γ (ratNN q)) ∈
      {p : (Fin (d + d) → ℤ) × (Fin (d + d) → ℤ) | 0 ≤ q → 2 ≤ ‖(y₀ + (escDir y₀).vec) +
        ((fun i : Fin d => p.1 (Fin.natAdd d i)) - (fun i : Fin d => p.1 (Fin.castAdd d i)))‖}} := by
    ext γ; simp only [mem_iInter, mem_ofPred_eq, escB]; exact Iff.rfl
  rw [this]
  exact MeasurableSet.iInter fun q => measurableSet_pair_preimage _ _ _

section

variable [NeZero d] (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
include h

omit h [MeasurableSpace Ω] in
theorem measurableSet_pair_escA (y₀ : Fin d → ℤ) :
    MeasurableSet[natFil (drvPair Ñ) 1] {ω | drvPair Ñ ω ∈ escA y₀} := by
  have hm : ∀ s : ℝ≥0, s ≤ 1 → ∀ S : Set (Fin (d + d) → ℤ),
      MeasurableSet[natFil (drvPair Ñ) 1] {ω | drvPair Ñ ω s ∈ S} := fun s hs S =>
    measurable_natFil (drvPair Ñ) hs (MeasurableSet.of_discrete (s := S))
  have e : {ω | drvPair Ñ ω ∈ escA y₀} =
      {ω | drvPair Ñ ω 1 ∈ {z | (fun i : Fin d => z (Fin.castAdd d i)) = 0}} ∩
      ({ω | drvPair Ñ ω 1 ∈ {z | (fun i : Fin d => z (Fin.natAdd d i)) = (escDir y₀).vec}} ∩
      ⋂ q : ℚ, {ω | 0 ≤ q → q ≤ 1 → drvPair Ñ ω (ratNN q) ∈ {z |
        (fun i : Fin d => z (Fin.castAdd d i)) = 0 ∧
        ((fun i : Fin d => z (Fin.natAdd d i)) = 0 ∨
          (fun i : Fin d => z (Fin.natAdd d i)) = (escDir y₀).vec)}}) := by
    ext ω; simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, escA]; exact Iff.rfl
  rw [e]
  refine (hm 1 le_rfl _).inter ((hm 1 le_rfl _).inter (MeasurableSet.iInter fun q => ?_))
  by_cases hq : 0 ≤ q ∧ q ≤ 1
  · have hqs : ratNN q ≤ 1 := by
      unfold ratNN
      exact Real.toNNReal_le_iff_le_coe.2 (by simpa using (show ((q : ℚ) : ℝ) ≤ 1 by exact_mod_cast hq.2))
    have := hm (ratNN q) hqs {z | (fun i : Fin d => z (Fin.castAdd d i)) = 0 ∧
        ((fun i : Fin d => z (Fin.natAdd d i)) = 0 ∨
          (fun i : Fin d => z (Fin.natAdd d i)) = (escDir y₀).vec)}
    convert this using 1
    ext ω; simp [hq.1, hq.2]
  · have : {ω : Ω | 0 ≤ q → q ≤ 1 → drvPair Ñ ω (ratNN q) ∈ {z |
        (fun i : Fin d => z (Fin.castAdd d i)) = 0 ∧
        ((fun i : Fin d => z (Fin.natAdd d i)) = 0 ∨
          (fun i : Fin d => z (Fin.natAdd d i)) = (escDir y₀).vec)}} = univ := by
      ext ω; simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ hq
    rw [this]; exact MeasurableSet.univ

theorem ae_single_point_subset (y₀ : Fin d → ℤ) :
    singlePoint (drvPoint Ñ) (dirMap d (escDir y₀, 1)) ≤ᵐ[P] {ω | drvPair Ñ ω ∈ escA y₀} := by
  filter_upwards [drivers_ae_good h] with ω hG
  intro hF
  have hpair := drivers_pair_eq ω hG
  have hw := walk_single_point hG.2.2 (dirMap d (escDir y₀, 1)) (fun v => by
    have := mem_iInter.1 hF v
    simpa [cntN] using this)
  have hv : (dirMap d (escDir y₀, 1)).vec = Fin.append (0 : Fin d → ℤ) (escDir y₀).vec :=
    vec_dirMap_one _
  have hval : ∀ s : ℝ≥0, drvPair Ñ ω s = walk (d + d) (drvPoint Ñ ω) (s : ℝ) := fun s => by
    rw [hpair]; rfl
  have hf : ∀ z : Fin (d + d) → ℤ, z = 0 ∨ z = Fin.append (0 : Fin d → ℤ) (escDir y₀).vec →
      (fun i : Fin d => z (Fin.castAdd d i)) = 0 ∧
      ((fun i : Fin d => z (Fin.natAdd d i)) = 0 ∨
        (fun i : Fin d => z (Fin.natAdd d i)) = (escDir y₀).vec) := by
    rintro z (rfl | rfl)
    · exact ⟨rfl, Or.inl rfl⟩
    · refine ⟨?_, Or.inr ?_⟩
      · funext i; exact Fin.append_left _ _ i
      · funext i; exact Fin.append_right _ _ i
  have h1 : drvPair Ñ ω 1 = Fin.append (0 : Fin d → ℤ) (escDir y₀).vec := by
    rw [hval]; simp only [NNReal.coe_one]; rw [hw.2, hv]
  refine ⟨?_, ?_, fun q hq0 hq1 => ?_⟩
  · show (fun i : Fin d => drvPair Ñ ω 1 (Fin.castAdd d i)) = 0
    rw [h1]; funext i; exact Fin.append_left _ _ i
  · show (fun i : Fin d => drvPair Ñ ω 1 (Fin.natAdd d i)) = _
    rw [h1]; funext i; exact Fin.append_right _ _ i
  · have hs : ((ratNN q : ℝ≥0) : ℝ) ≤ 1 := by
      unfold ratNN; rw [Real.coe_toNNReal _ (by exact_mod_cast hq0)]; exact_mod_cast hq1
    have := hw.1 _ hs
    rw [← hval] at this
    refine hf _ ?_
    rcases this with e | e
    · exact Or.inl e
    · exact Or.inr (e.trans hv)

end

end ElboimSly.Paper
