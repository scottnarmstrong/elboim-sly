/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegWalk
public import ElboimSly.Foundations.Cyclic.CycDrivenRegion
public import ElboimSly.Foundations.Cyclic.DrivenSrwShort
public import Mathlib

/-!
# The constructions of the regenerated walk (ii): the regenerated walk from independent driving paths

The constructions of the regenerated walk (ii). With `𝒥_k = k`, the driven final record of the plan
`𝒫_reg` has walk `k` in copy `k`, where no other walk has events. So walk `k` is the driven path
of `𝒫₁` driven by `X_k`, which equals `W^{X_k}` up to closing on `{X_k ∈ cycCF}`
(`cyc_driven_region`), and `W_reg` of the driven final record is the regenerated walk built
from the pieces `W^{X_k}` (`drivenRegenWalk`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The plan `𝒫_reg`: infinitely many walks, walk `k` in copy `k` (copy `k` is piece `k + 1`),
start vertex `0`, phase `0`, forward, and the closing rule for every walk. -/
noncomputable def regPlan (d : ℕ) (β : ℝ) : CycPlan ℕ d β :=
  closingPlan β ⊤ (fun k _ => regionData d k) (fun _ => measurable_const)

/-- The regenerated walk built from the driving paths `Y 0, Y 1, …` (piece `k + 1` driven by
`Y k`): the pieces `W^{Y k}` glued at the partial sums of the closing times `treg^{Y k}`.
Regenerated cyclic walk, construction (ii). -/
noncomputable def drivenRegenWalk (b : ℝ≥0) (Y : ℕ → ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  gluedWalk (partialSums fun k => drivenTreg b (Y k)) fun k => drivenWalk b (Y k)

omit [Fact (0 < β)] in
/-- Records whose `i`-th world-line lies in copy `i` have no region in copy `k` beyond `k`. -/
theorem region_slice_empty {k : ℕ} {f : CycRecN ℕ d k} (hf : ∀ i : Fin k, (f i).1.copy = i)
    (e : Edge d) (θ : AddCircle β) :
    ((k, (e, θ)) : ℕ × RingSpace d β) ∉ CycRec.region β (Sum.inl ⟨k, f⟩) := by
  rintro ⟨e', ⟨j, hj⟩, hz⟩
  simp only [CycRec.nth] at hj
  by_cases hjk : j < k
  · rw [dite_eq_left hjk] at hj
    cases hj
    obtain ⟨r, -, -, h1, -⟩ := hz
    have := hf ⟨j, hjk⟩
    simp only [CycEntry.data] at h1
    rw [this] at h1
    simp at h1
    omega
  · rw [dite_eq_right hjk] at hj
    exact absurd hj (by simp)

omit [Fact (0 < β)] in
theorem ringSet_slice_empty {k : ℕ} {f : CycRecN ℕ d k} (hf : ∀ i : Fin k, (f i).1.copy = i)
    (e : Edge d) (θ : AddCircle β) :
    ((k, (e, θ)) : ℕ × RingSpace d β) ∉ CycRec.ringSet β (Sum.inl ⟨k, f⟩) := by
  rintro ⟨e', ⟨j, hj⟩, hz⟩
  simp only [CycRec.nth] at hj
  by_cases hjk : j < k
  · rw [dite_eq_left hjk] at hj
    cases hj
    obtain ⟨r, -, -, -, h1, -⟩ := hz
    have := hf ⟨j, hjk⟩
    simp only [CycEntry.data] at h1
    rw [this] at h1
    simp at h1
    omega
  · rw [dite_eq_right hjk] at hj
    exact absurd hj (by simp)

/-- The path rule of the driven record of `𝒫_reg` with `𝒥_k = k`. -/
noncomputable def drivenIndepRule (β : ℝ) [Fact (0 < β)] (X : ℕ → CycPath d) : PathRule ℕ d :=
  fun k ρ => drivenPath β (CycRec.region β (Sum.inl ⟨k, ρ⟩)) (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩))
    (regionData d k) (X k).1 (drvOffset (fun k _ => k) ρ k)

theorem drivenFinal_indep (X : ℕ → CycPath d) :
    (regPlan d β).drivenFinal (J := ℕ) (fun k _ => k) X =
      (regPlan d β).cycFinal (drivenIndepRule β X) := rfl

/-- Walk `k` of the driven record with `𝒥_k = k` is the driven path of `𝒫₁` driven by `X k`. -/
theorem regPlan_E_driven (X : ℕ → CycPath d) (hX : ∀ k, (X k).1.fn ∈ CycCF β.toNNReal) (k : ℕ) :
    ((regPlan d β).E (drivenIndepRule β X) k).len = drivenTreg β.toNNReal (X k).1.fn ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ drivenTreg β.toNNReal (X k).1.fn →
        ((regPlan d β).E (drivenIndepRule β X) k).path.fn s = drivenWalk β.toNNReal (X k).1.fn s := by
  set P := regPlan d β with hP
  set path := drivenIndepRule β X with hpathdef
  have hideal : ∀ i : Fin k, ((P.ideal path k) i).1.copy = i := fun i => by
    rw [P.ideal_apply]; rfl
  have hoff : drvOffset (fun k _ => k) (P.ideal path k) k = 0 := by
    unfold drvOffset
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right (Fin.is_lt i).ne]
  have hpath : path k (P.ideal path k) =
      drivenPath β (CycRec.region β (Sum.inl ⟨k, P.ideal path k⟩))
        (CycRec.ringSet β (Sum.inl ⟨k, P.ideal path k⟩)) (regionData d k) (X k).1 0 := by
    show drivenPath β _ _ (regionData d k) (X k).1
      (drvOffset (fun k _ => k) (P.ideal path k) k) = _
    rw [hoff]
  have hreg := driven_region_of_slice (ι := k) (hX k)
    (R := CycRec.region β (Sum.inl ⟨k, P.ideal path k⟩))
    (Q := CycRec.ringSet β (Sum.inl ⟨k, P.ideal path k⟩))
    (region_slice_empty hideal) (ringSet_slice_empty hideal) (X k).1 (X k).2 (isShiftOf_self (X k).1)
  have hstop : P.stopLen k (P.ideal path k) (path k (P.ideal path k)) =
      drivenTreg β.toNNReal (X k).1.fn := by
    rw [hpath]
    show (closingPlan β ⊤ _ _).stopLen _ _ _ = _
    rw [closingPlan_stopLen]
    exact hreg.1
  have hE : P.E path k = (regionData d k, (path k (P.ideal path k)).cut
      (drivenTreg β.toNNReal (X k).1.fn)) := by
    unfold CycPlan.E CycPlan.nextEntry
    rw [hstop]; rfl
  refine ⟨?_, fun s hs => ?_⟩
  · rw [hE]
    show ((path k (P.ideal path k)).1.cut _).len = _
    rw [CPath.cut_len]
  · rw [hE]
    show ((path k (P.ideal path k)).1.cut _).fn s = _
    rw [CPath.cut_fn, min_eq_left hs, ENNReal.toNNReal_coe, hpath]
    exact hreg.2 s hs

/-- **the constructions of the regenerated walk (ii)**: `W_reg` of the driven final record of `𝒫_reg` with `𝒥_k = k`
is the regenerated walk built from the driven pieces `W^{X k}`, provided every `X k` is a
coincidence-free driving path. -/
theorem regRecWalk_drivenFinal_indep (X : ℕ → CycPath d)
    (hX : ∀ k, (X k).1.fn ∈ CycCF β.toNNReal) (t : ℝ≥0) :
    regRecWalk ((regPlan d β).drivenFinal (J := ℕ) (fun k _ => k) X) t =
      drivenRegenWalk β.toNNReal (fun k => (X k).1.fn) t := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  rw [drivenFinal_indep]
  exact (regPlan d β).regRecWalk_cycFinal (drivenIndepRule β X) rfl hb
    (fun k => drivenTreg β.toNNReal (X k).1.fn) (fun k => drivenWalk β.toNNReal (X k).1.fn)
    (fun k => (drivenWalk_eq_self_of_cycCF (hX k) hb).1)
    (fun k _ => regPlan_E_driven X hX k) t

end ElboimSly.Cyclic

end
