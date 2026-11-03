/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.SchemeMeas
import Mathlib

/-!
# Sequential first-point exploration: the revealed part

Sequential first-point exploration (a), which is pathwise.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] (sch : ExplScheme μ U)

namespace ExplScheme

/-- The region `D_k(ρ_k)` revealed at step `k`. -/
def Dreg (k : ℕ) (x : U × Measure S) : Set S :=
  probeRegion (sch.Rt k (sch.Hfun k x)) (sch.stepAt k (sch.Hfun k x) x.2).1

theorem stepAt_fst_le (k : ℕ) (η : Hist U S k) (ν : Measure S) :
    (sch.stepAt k η ν).1 ≤ sch.h k η := probeRho_le_h

theorem Z_succ_eq (k : ℕ) (x : U × Measure S) :
    sch.Z (k + 1) (sch.Hfun (k + 1) x) = sch.Z k (sch.Hfun k x) ∪ sch.Dreg k x := by
  have hρ : min (sch.Hfun (k + 1) x).last.1 (sch.h k (sch.Hfun k x)) =
      (sch.stepAt k (sch.Hfun k x) x.2).1 := by
    rw [Hfun_last]; exact min_eq_left (sch.stepAt_fst_le _ _ _)
  simp only [Z, Hfun_init, hρ]
  ext y
  simp only [Set.mem_union, Set.mem_ofPred_eq, Dreg, probeRegion]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [sch.Rt_of_notMem h1]; exact h2)
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hy : y ∈ sch.Z k (sch.Hfun k x)
      · exact Or.inl hy
      · exact Or.inr ⟨hy, by rwa [sch.Rt_of_notMem hy] at h⟩

theorem Z_mono (k : ℕ) (x : U × Measure S) :
    sch.Z k (sch.Hfun k x) ⊆ sch.Z (k + 1) (sch.Hfun (k + 1) x) := by
  rw [Z_succ_eq]; exact Set.subset_union_left

theorem Z_antitone_le {j k : ℕ} (hjk : j ≤ k) (x : U × Measure S) :
    sch.Z j (sch.Hfun j x) ⊆ sch.Z k (sch.Hfun k x) := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (sch.Z_mono _ x)

theorem Hfun_coord (k : ℕ) (x : U × Measure S) (j : Fin k) :
    (sch.Hfun k x).2 j = sch.stepAt j (sch.Hfun j x) x.2 := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Hfun_succ, Hist.snoc]
    · simp [Hfun_succ, Hist.snoc, ih i]

end ExplScheme

end ElboimSly
