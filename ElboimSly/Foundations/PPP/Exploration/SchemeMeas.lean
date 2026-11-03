/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.Scheme
import Mathlib

/-!
# The exploration of a configuration; measurability

Exploration scheme; the exploration of N (the exploration of `N`), measurability for schemes (b)-(d).

For `x = (u, ν) ∈ 𝕌 × 𝓜(S)`, `Hfun k x ∈ ℋ_k` is the history `H_k` of the exploration of `ν` with
auxiliary datum `u`: `H_0 = u`, `H_{k+1} = (H_k, St_{k,H_k}(ν))`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] (sch : ExplScheme μ U)

namespace ExplScheme

/-- The step map of the masked probe of step `k` at history `η`. -/
noncomputable def stepAt (k : ℕ) (η : Hist U S k) (ν : Measure S) : Outcome S :=
  probeStep μ (sch.Rt k η) (sch.h k η) ν

/-- The history `H_k` of the exploration of `ν` with auxiliary datum `u`. -/
noncomputable def Hfun : (k : ℕ) → U × Measure S → Hist U S k
  | 0, x => (x.1, Fin.elim0)
  | k + 1, x => (Hfun k x).snoc (sch.stepAt k (Hfun k x) x.2)

/-- The whole history `H_∞ = (U, (ρ_j, V_j)_j)`. -/
noncomputable def Hinf (x : U × Measure S) : U × (ℕ → Outcome S) :=
  (x.1, fun j => sch.stepAt j (sch.Hfun j x) x.2)

/-- Measurability for schemes (b). -/
theorem measurable_stepAt (k : ℕ) :
    Measurable fun p : Hist U S k × Measure S => sch.stepAt k p.1 p.2 :=
  measurable_probeStep_param μ (R := sch.Rt k) (h := sch.h k) (sch.measurable_Rt k)
    (sch.measurable_h k)

theorem measurable_Hfun (k : ℕ) : Measurable (sch.Hfun k) := by
  induction k with
  | zero => exact measurable_fst.prodMk measurable_const
  | succ k ih =>
    exact (Hist.measurable_snoc k).comp (ih.prodMk ((sch.measurable_stepAt k).comp
      (ih.prodMk measurable_snd)))

theorem measurable_Hinf : Measurable sch.Hinf :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun j => (sch.measurable_stepAt j).comp
    ((sch.measurable_Hfun j).prodMk measurable_snd))

theorem Hfun_succ (k : ℕ) (x : U × Measure S) :
    sch.Hfun (k + 1) x = (sch.Hfun k x).snoc (sch.stepAt k (sch.Hfun k x) x.2) := rfl

theorem Hfun_init (k : ℕ) (x : U × Measure S) : (sch.Hfun (k + 1) x).init = sch.Hfun k x := by
  rw [Hfun_succ, Hist.init_snoc]

theorem Hfun_last (k : ℕ) (x : U × Measure S) :
    (sch.Hfun (k + 1) x).last = sch.stepAt k (sch.Hfun k x) x.2 := by
  rw [Hfun_succ, Hist.last_snoc]

/-- Measurability for schemes (d): restriction to the explored region. -/
theorem measurable_restrict_Z (k : ℕ) :
    Measurable fun p : Hist U S k × Measure S => (tau μ p.2).restrict (sch.Z k p.1) :=
  measurable_tau_restrict_section μ (sch.measurableSet_Z k)

/-- Measurability for schemes (d): restriction to the unexplored region. -/
theorem measurable_restrict_Zc (k : ℕ) :
    Measurable fun p : Hist U S k × Measure S => (tau μ p.2).restrict (sch.Z k p.1)ᶜ :=
  measurable_tau_restrict_section μ (sch.measurableSet_Z k).compl

end ExplScheme

end ElboimSly
