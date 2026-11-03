/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenDriven
public import ElboimSly.Foundations.Cyclic.CycRegenShift
public import Mathlib

/-!
# The constructions of the regenerated walk (iii): the regenerated walk from one cut driving path

The constructions of the regenerated walk (iii). With `𝒥_k = 1`, walk `k` is driven by
`X^{(k)} = X(σ_{k-1} + ·) - X(σ_{k-1})`, with offset `a_k = Λ_{k-1} = σ_{k-1} ∈ βℤ`.
If `X ∈ cycCF` then `X^{(k)} ∈ cycCF`, so the pieces are `W^{X^{(k)}}` up to closing
(`cyc_driven_region`). The regenerated walk of construction (iii) is `drivenRegenWalkCut`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

theorem pathTreg_top_or (b : ℝ≥0) (p : ℝ≥0 → Fin d → ℤ) :
    pathTreg b p = ⊤ ∨ ∃ k : ℕ, 1 ≤ k ∧ pathTreg b p = (((k : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) ∧
      p ((k : ℝ≥0) * b) = 0 := by
  classical
  by_cases hex : ∃ k : ℕ, 1 ≤ k ∧ p ((k : ℝ≥0) * b) = 0
  · right
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
    apply le_antisymm
    · exact iInf_le (fun k : {k : ℕ // 1 ≤ k ∧ p ((k : ℝ≥0) * b) = 0} =>
        ((((k.1 : ℝ≥0) * b : ℝ≥0)) : ℝ≥0∞)) ⟨Nat.find hex, Nat.find_spec hex⟩
    · refine le_iInf fun k => ?_
      have : Nat.find hex ≤ k.1 := Nat.find_min' hex k.2
      exact ENNReal.coe_le_coe.2 (mul_le_mul_of_nonneg_right (Nat.cast_le.2 this) zero_le)
  · left
    unfold pathTreg
    have : IsEmpty {k : ℕ // 1 ≤ k ∧ p ((k : ℝ≥0) * b) = 0} := ⟨fun k => hex ⟨k.1, k.2⟩⟩
    exact iInf_of_empty _

/-- The cut times `σ_0 = 0`, `σ_{k+1} = σ_k + treg^{X^{(k)}}`, `X^{(k)} = X(σ_k + ·) - X(σ_k)`. -/
noncomputable def cutTimes (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℕ → ℝ≥0∞
  | 0 => 0
  | k + 1 => cutTimes b x k + drivenTreg b (shiftPath x (cutTimes b x k).toNNReal)

/-- The closing time of the `k`-th cut piece. -/
noncomputable def cutTau (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (k : ℕ) : ℝ≥0∞ :=
  drivenTreg b (shiftPath x (cutTimes b x k).toNNReal)

/-- The `k`-th cut piece `W^{X^{(k)}}`. -/
noncomputable def cutPiece (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (k : ℕ) : ℝ≥0 → Fin d → ℤ :=
  drivenWalk b (shiftPath x (cutTimes b x k).toNNReal)

/-- The regenerated walk built from one driving path `x` cut at the regeneration times.
Regenerated cyclic walk, construction (iii). -/
noncomputable def drivenRegenWalkCut (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  gluedWalk (cutTimes b x) (cutPiece b x)

theorem cutTimes_eq_partialSums (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) :
    cutTimes b x = partialSums (cutTau b x) := by
  funext k
  induction k with
  | zero => simp [cutTimes, partialSums]
  | succ k ih => rw [partialSums_succ, ← ih]; rfl

theorem cutTimes_mul (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (k : ℕ) :
    ∃ m : ℕ, (cutTimes b x k).toNNReal = (m : ℝ≥0) * b := by
  induction k with
  | zero => exact ⟨0, by simp [cutTimes]⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    by_cases hfin : cutTimes b x (k + 1) = ⊤
    · exact ⟨0, by simp [hfin]⟩
    · have hlt : cutTimes b x (k + 1) < ⊤ := lt_top_iff_ne_top.2 hfin
      have h1 : cutTimes b x k ≠ ⊤ := fun h => by
        rw [show cutTimes b x (k + 1) = cutTimes b x k + _ from rfl, h] at hfin
        simp at hfin
      have h2 : cutTau b x k ≠ ⊤ := fun h => by
        have : cutTimes b x (k + 1) = cutTimes b x k + cutTau b x k := rfl
        rw [this, h] at hfin
        simp at hfin
      rcases pathTreg_top_or b (drivenWalk b (shiftPath x (cutTimes b x k).toNNReal)) with h | ⟨j, -, hj, -⟩
      · exact absurd h h2
      · refine ⟨m + j, ?_⟩
        have : cutTimes b x (k + 1) = cutTimes b x k + cutTau b x k := rfl
        rw [this, ENNReal.toNNReal_add h1 h2]
        have hτ : cutTau b x k = (((j : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := hj
        rw [hτ, hm, ENNReal.toNNReal_coe]
        push_cast; ring

theorem shift_mem_cycCF {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ CycCF b) (k : ℕ) :
    shiftPath x (cutTimes b x k).toNNReal ∈ CycCF b := by
  obtain ⟨m, hm⟩ := cutTimes_mul b x k
  rw [hm]
  exact cycCF_shiftPath hx m

theorem cutTau_ge {b : ℝ≥0} (hb : 0 < b) {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ CycCF b) (k : ℕ) :
    (b : ℝ≥0∞) ≤ cutTau b x k :=
  (drivenWalk_eq_self_of_cycCF (shift_mem_cycCF hx k) hb).1

variable {β : ℝ} [Fact (0 < β)]

/-- The path rule of the driven record of `𝒫_reg` with `𝒥_k = 1`. -/
noncomputable def drivenCutRule (β : ℝ) [Fact (0 < β)] (X : CycPath d) : PathRule ℕ d :=
  fun k ρ => drivenPath β (CycRec.region β (Sum.inl ⟨k, ρ⟩)) (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩))
    (regionData d k) X.1 (drvOffset (J := Unit) (fun _ _ => ()) ρ ())

theorem drivenFinal_cut (X : CycPath d) :
    (regPlan d β).drivenFinal (J := Unit) (fun _ _ => ()) (fun _ => X) =
      (regPlan d β).cycFinal (drivenCutRule β X) := rfl

/-- Walk `k` of a record of `𝒫_reg` whose path is `p`, with closing time `τ`. -/
theorem regPlan_E_of (path : PathRule ℕ d) (k : ℕ) (p : CycPath d)
    (hp : path k ((regPlan d β).ideal path k) = p) {b : ℝ≥0} (hb : b = β.toNNReal)
    {τ : ℝ≥0∞} {w : ℝ≥0 → Fin d → ℤ} (hτ : pathTreg b p.1.fn = τ)
    (hagree : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ τ → p.1.fn s = w s) :
    ((regPlan d β).E path k).len = τ ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ τ → ((regPlan d β).E path k).path.fn s = w s := by
  subst hb
  have hstop : (regPlan d β).stopLen k ((regPlan d β).ideal path k) p = τ := by
    show (closingPlan β ⊤ _ _).stopLen _ _ _ = _
    rw [closingPlan_stopLen]
    exact hτ
  have hE : (regPlan d β).E path k = (regionData d k, p.cut τ) := by
    unfold CycPlan.E CycPlan.nextEntry
    rw [hp, hstop]; rfl
  refine ⟨?_, fun s hs => ?_⟩
  · rw [hE]
    show (p.1.cut τ).len = _
    rw [CPath.cut_len]
  · rw [hE]
    show (p.1.cut τ).fn s = _
    rw [CPath.cut_fn, min_eq_left hs, ENNReal.toNNReal_coe]
    exact hagree s hs

theorem regen_cut_E (X : CycPath d) (hX : X.1.fn ∈ CycCF β.toNNReal) (k : ℕ) :
    (regPlan d β).AllFin (drivenCutRule β X) k →
      ((regPlan d β).E (drivenCutRule β X) k).len = cutTau β.toNNReal X.1.fn k ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ cutTau β.toNNReal X.1.fn k →
        ((regPlan d β).E (drivenCutRule β X) k).path.fn s = cutPiece β.toNNReal X.1.fn k s := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hall
  set P := regPlan d β with hP
  set path := drivenCutRule β X with hpathdef
  have hlen : ∀ i : Fin k, ((P.ideal path k) i).len = cutTau β.toNNReal X.1.fn i := fun i => by
    rw [P.ideal_apply]
    exact (ih i i.2 (fun j hj => hall j (hj.trans i.2))).1
  have hfin : ∀ i : Fin k, cutTau β.toNNReal X.1.fn i ≠ ⊤ := fun i => by
    rw [← hlen i, P.ideal_apply]
    exact (hall i i.2).ne
  have hoff : drvOffset (J := Unit) (fun _ _ => ()) (P.ideal path k) () =
      (cutTimes β.toNNReal X.1.fn k).toNNReal := by
    unfold drvOffset
    simp only [ite_true]
    rw [cutTimes_eq_partialSums, partialSums, ENNReal.toNNReal_sum (fun i _ => ?_),
      Finset.sum_range]
    · exact Finset.sum_congr rfl fun i _ => by rw [hlen i]
    · exact hfin ⟨i, by simpa using ‹i ∈ Finset.range k›⟩
  have hideal : ∀ i : Fin k, ((P.ideal path k) i).1.copy = i := fun i => by
    rw [P.ideal_apply]; rfl
  have hpath : path k (P.ideal path k) =
      drivenPath β (CycRec.region β (Sum.inl ⟨k, P.ideal path k⟩))
        (CycRec.ringSet β (Sum.inl ⟨k, P.ideal path k⟩)) (regionData d k) X.1
        (cutTimes β.toNNReal X.1.fn k).toNNReal := by
    show drivenPath β _ _ (regionData d k) X.1 (drvOffset (J := Unit) (fun _ _ => ()) _ ()) = _
    rw [hoff]
  have hreg := driven_region_of_slice (ι := k) (shift_mem_cycCF hX k)
    (R := CycRec.region β (Sum.inl ⟨k, P.ideal path k⟩))
    (Q := CycRec.ringSet β (Sum.inl ⟨k, P.ideal path k⟩))
    (region_slice_empty hideal) (ringSet_slice_empty hideal) X.1 X.2
    (isShiftOf_shiftPath X.1 (cutTimes β.toNNReal X.1.fn k).toNNReal)
  exact regPlan_E_of path k _ hpath rfl hreg.1 hreg.2

/-- **the constructions of the regenerated walk (iii)**: `W_reg` of the driven final record of `𝒫_reg` with `𝒥_k = 1`
is the regenerated walk built from one coincidence-free driving path cut at the regeneration
times. -/
theorem regRecWalk_drivenFinal_cut (X : CycPath d) (hX : X.1.fn ∈ CycCF β.toNNReal) (t : ℝ≥0) :
    regRecWalk ((regPlan d β).drivenFinal (J := Unit) (fun _ _ => ()) (fun _ => X)) t =
      drivenRegenWalkCut β.toNNReal X.1.fn t := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  rw [drivenFinal_cut, drivenRegenWalkCut, cutTimes_eq_partialSums]
  exact (regPlan d β).regRecWalk_cycFinal (drivenCutRule β X) rfl hb (cutTau β.toNNReal X.1.fn)
    (cutPiece β.toNNReal X.1.fn) (cutTau_ge hb hX) (fun k hk => regen_cut_E X hX k hk) t

end ElboimSly.Cyclic

end
