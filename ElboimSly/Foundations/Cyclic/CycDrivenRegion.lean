/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegionRule
public import ElboimSly.Foundations.Cyclic.CycClosingStopLen
public import Mathlib

/-!
# The driven walk is a driven world-line

The driven walk is a driven world-line. Let `𝒫₁` be the plan with one walk, start data `(1, 0, 0, +1)`
and the closing rule (`closingPlan`). Then the stopping length of every path `p` is
`treg(p) = inf {kβ : k ≥ 1, p(kβ) = 0}` (`closingPlan_stopLen`), and for `x ∈ cycCF`, the driven path
`p` of `𝒫₁` driven by `x` (offset `0`, no previous walks) satisfies `treg(p) = treg^x` and
`p = w^x` on `[0, treg^x]` (on `[0, ∞)` if `treg^x = ∞`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The plan `𝒫₁` of the driven walk is a driven world-line: one walk, start `(1, 0, 0, +1)`, closing rule. -/
noncomputable def regionPlan (d : ℕ) (β : ℝ) : CycPlan Unit d β :=
  closingPlan β 1 (fun _ _ => regionData d ()) (fun _ => measurable_const)

/-- The closing times of two paths agree if the paths agree up to the closing time of one. -/
theorem pathTreg_congr {b : ℝ≥0} (_hb : 0 < b) {p w : ℝ≥0 → Fin d → ℤ}
    (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ pathTreg b w → p s = w s) : pathTreg b p = pathTreg b w := by
  classical
  apply le_antisymm
  · by_cases hex : ∃ k : ℕ, 1 ≤ k ∧ w ((k : ℝ≥0) * b) = 0
    · set k0 := Nat.find hex with hk0
      have hk0s := Nat.find_spec hex
      have hτ : pathTreg b w = (((k0 : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := by
        apply le_antisymm
        · exact iInf_le (fun k : {k : ℕ // 1 ≤ k ∧ w ((k : ℝ≥0) * b) = 0} =>
            ((((k.1 : ℝ≥0) * b : ℝ≥0)) : ℝ≥0∞)) ⟨k0, hk0s⟩
        · refine le_iInf fun k => ?_
          have : k0 ≤ k.1 := Nat.find_min' hex k.2
          exact ENNReal.coe_le_coe.2 (mul_le_mul_of_nonneg_right (Nat.cast_le.2 this) zero_le)
      rw [hτ]
      have hp : p ((k0 : ℝ≥0) * b) = 0 := by
        rw [h _ (by rw [hτ])]; exact hk0s.2
      exact iInf_le (fun k : {k : ℕ // 1 ≤ k ∧ p ((k : ℝ≥0) * b) = 0} =>
        ((((k.1 : ℝ≥0) * b : ℝ≥0)) : ℝ≥0∞)) ⟨k0, hk0s.1, hp⟩
    · have : pathTreg b w = ⊤ := by
        unfold pathTreg
        have : IsEmpty {k : ℕ // 1 ≤ k ∧ w ((k : ℝ≥0) * b) = 0} :=
          ⟨fun k => hex ⟨k.1, k.2⟩⟩
        exact iInf_of_empty _
      rw [this]; exact le_top
  · refine le_iInf fun k => ?_
    by_cases hle : (((k.1 : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) ≤ pathTreg b w
    · have : w ((k.1 : ℝ≥0) * b) = 0 := by rw [← h _ hle]; exact k.2.2
      exact iInf_le (fun k : {k : ℕ // 1 ≤ k ∧ w ((k : ℝ≥0) * b) = 0} =>
        ((((k.1 : ℝ≥0) * b : ℝ≥0)) : ℝ≥0∞)) ⟨k.1, k.2.1, this⟩
    · exact (not_le.1 hle).le

omit [Fact (0 < β)] in
/-- The records of zero walks have empty explored region and no known rings. -/
theorem region_zero (ρ : CycRecN Unit d 0) :
    CycRec.region β (Sum.inl ⟨0, ρ⟩) = ∅ := by
  ext z
  simp [CycRec.region, CycRec.IsEntry, CycRec.nth]

omit [Fact (0 < β)] in
theorem ringSet_zero (ρ : CycRecN Unit d 0) :
    CycRec.ringSet β (Sum.inl ⟨0, ρ⟩) = ∅ := by
  ext z
  simp [CycRec.ringSet, CycRec.IsEntry, CycRec.nth]

/-- The driven path of a walk in a copy `ι` that no previous walk has touched: for `x ∈ cycCF` and
`p` the driven path driven by `X` (`X.fn = x`) with offset `0` (the regions `R`, `Q` having empty
slice at `ι`), `treg(p) = treg^x` and `p = w^x` on `[0, treg^x]`. -/
theorem driven_region_of_slice {I : Type*} [MeasurableSpace I] {ι : I}
    {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ CycCF β.toNNReal)
    {R Q : Set (I × RingSpace d β)}
    (hR : ∀ (e : Edge d) (θ : AddCircle β), ((ι, (e, θ)) : I × RingSpace d β) ∉ R)
    (hQ : ∀ (e : Edge d) (θ : AddCircle β), ((ι, (e, θ)) : I × RingSpace d β) ∉ Q)
    (X : CPath (Fin d → ℤ)) (hXu : X.UnitJumps) {a : ℝ≥0} (hXa : IsShiftOf X a x) :
    let p := drivenPath β R Q (regionData d ι) X a
    pathTreg β.toNNReal p.1.fn = drivenTreg β.toNNReal x ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ drivenTreg β.toNNReal x → p.1.fn s = drivenWalk β.toNNReal x s := by
  intro p
  have hβ : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  obtain ⟨hdr, hi, hno⟩ := hx
  have hQf : {θ : AddCircle β | ∃ e : Edge d, ((regionData d ι).copy, (e, θ)) ∈ Q}.Finite := by
    have : {θ : AddCircle β | ∃ e : Edge d, ((regionData d ι).copy, (e, θ)) ∈ Q} = ∅ := by
      ext θ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
      exact fun e => hQ e θ
    rw [this]; exact finite_empty
  have hp : IsDriven β R Q (regionData d ι) X a p.1 := drivenPath_spec hXu hQf
  have hagree : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ drivenTreg β.toNNReal x →
      p.1.fn s = drivenWalk β.toNNReal x s := by
    intro s hs
    refine drv_eq_of_le (R := R) (Q := Q) (δ := regionData d ι)
      (X := X) (a := a) (T := s) (p := p.1) (p' := drivenCPath hdr hβ) ?_ ?_ ?_ s le_rfl
    · rw [hp.2.1]
      show (regionData d ι).start = drivenWalk β.toNNReal x 0
      rw [drivenWalk_zero hdr.toIsRegPath hβ]; rfl
    · intro r hr _; exact hp.2.2 r hr
    · intro r hr hrs
      exact drvRule_drivenCPath (ι := ι) hdr hβ hi hno hR hQ X hXa hr
        ((by exact_mod_cast hrs : (r : ℝ≥0∞) ≤ s).trans hs)
  exact ⟨pathTreg_congr hβ hagree, hagree⟩

/-- **the driven walk is a driven world-line.** Let `x ∈ cycCF` and let `p` be the driven path of `𝒫₁` driven
by `X` (`X.fn = x`), with offset `0`. Then `treg(p) = treg^x` and `p = w^x` on `[0, treg^x]`
(on `[0, ∞)` if `treg^x = ∞`). The stopping length of `𝒫₁` is `treg` (`closingPlan_stopLen`). -/
theorem cyc_driven_region {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ CycCF β.toNNReal)
    (X : CPath (Fin d → ℤ)) (hX : X.fn = x) (ρ : CycRecN Unit d 0) :
    let p := drivenPath β (CycRec.region β (Sum.inl ⟨0, ρ⟩))
      (CycRec.ringSet β (Sum.inl ⟨0, ρ⟩)) (regionData d ()) X 0
    (regionPlan d β).stopLen 0 ρ p = drivenTreg β.toNNReal x ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ drivenTreg β.toNNReal x → p.1.fn s = drivenWalk β.toNNReal x s := by
  intro p
  have hXu : X.UnitJumps := by
    intro s hs
    have hs0 : 0 < s := hs.1
    rw [hX] at hs
    have := hx.1.unit s hs
    rw [CPath.left_eq_leftVal X hs0, hX]
    unfold IsUnitStep at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hXa : IsShiftOf X 0 x := hX ▸ isShiftOf_self X
  have h := driven_region_of_slice (ι := ()) (d := d) (β := β) hx
    (R := CycRec.region β (Sum.inl ⟨0, ρ⟩)) (Q := CycRec.ringSet β (Sum.inl ⟨0, ρ⟩))
    (by rw [region_zero]; simp) (by rw [ringSet_zero]; simp) X hXu hXa
  refine ⟨?_, h.2⟩
  rw [regionPlan, closingPlan_stopLen]
  exact h.1

end ElboimSly.Cyclic

end
