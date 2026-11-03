/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvRule
public import Mathlib

/-!
# The driving scheme (c): the data of a driven record

The driving scheme (c). For a record `ρ` with `GAt P (drule P jx X) k r ρ`, the driving
index and offset of the state `(ρ, b)` are those of walk `k` after the first `k` full driven
world-lines (`drvIdx_of_gAt`, `drvOff_of_gAt`), the path `gpth` of walk `k` is the driven path for the
region and the known rings of those world-lines, and it satisfies the rules (D1′)–(D3′)
(`isDriven_gpth`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

namespace CycSchemeGen

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {J : Type*} {jx : ∀ k : ℕ, CycRecN I d k → J} {X : J → CycPath d}
  {P : CycPlan I d β} {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}

theorem drvIdx_of_gAt (j0 : J) (h : GAt P (drule P jx X) k r ρ) (b : Bool) :
    drvIdx jx j0 (ρ, b) = jx k (P.ideal (drule P jx X) k) := by
  rw [h.rec_eq]
  unfold drvIdx
  simp only
  congr 1
  funext m
  simp [CycRec.snoc]

theorem drvOff_of_gAt (h : GAt P (drule P jx X) k r ρ) (b : Bool) :
    drvOff jx (ρ, b) =
      drvOffset jx (P.ideal (drule P jx X) k) (jx k (P.ideal (drule P jx X) k)) := by
  rw [h.rec_eq]
  unfold drvOff
  simp only
  have : (fun m : Fin k => CycRec.snoc (P.ideal (drule P jx X) k)
      (gdat P (drule P jx X) k, (gpth P (drule P jx X) k).cut (r : ℝ≥0∞)) m.castSucc) =
      P.ideal (drule P jx X) k := by
    funext m; simp [CycRec.snoc]
  rw [this]

theorem isDriven_gpth (h : GAt P (drule P jx X) k r ρ) :
    IsDriven β (CycRec.region β (Sum.inl ⟨k, P.ideal (drule P jx X) k⟩))
      (CycRec.ringSet β (Sum.inl ⟨k, P.ideal (drule P jx X) k⟩))
      (gdat P (drule P jx X) k) (X (jx k (P.ideal (drule P jx X) k))).1
      (drvOffset jx (P.ideal (drule P jx X) k) (jx k (P.ideal (drule P jx X) k)))
      (gpth P (drule P jx X) k).1 := by
  have hf : ∀ i : Fin k, (P.ideal (drule P jx X) k i).len ≠ ⊤ := by
    intro i
    rw [P.ideal_apply]
    exact (h.allFin i i.2).ne
  have hQ : {θ : AddCircle β | ∃ e : Edge d, ((gdat P (drule P jx X) k).copy, (e, θ)) ∈
      CycRec.ringSet β (Sum.inl ⟨k, P.ideal (drule P jx X) k⟩ : CycRec I d)}.Finite := by
    refine (finite_clock_ringSet (P.ideal (drule P jx X) k) hf).subset ?_
    rintro θ ⟨e, he⟩
    exact ⟨_, he, rfl⟩
  exact drivenPath_spec (X (jx k (P.ideal (drule P jx X) k))).2 hQ

end CycSchemeGen

end ElboimSly.Cyclic

end
