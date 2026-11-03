/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmFront
public import ElboimSly.Foundations.PPP.Dirac
public import ElboimSly.Foundations.PPP.Simple
import Mathlib

/-!
# Sequential first-point exploration: the revealed point

Sequential first-point exploration (f), second part. If `(S, μ)` has a dissecting system and `μ` is
diffuse, then almost surely on `{V_k ≠ 0}`, `V_k = δ_{X_k}` with `X_k = ξ(V_k)` (dirac masses), and
`R̃_k(H_k, X_k) = ρ_k`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {sch : ExplScheme μ U} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem restrict_count_eq_dirac [MeasurableSingletonClass S] {A : Set S} (hA : MeasurableSet A)
    (h1 : (Measure.count.restrict A) Set.univ = 1) : ∃ x, Measure.count.restrict A = Measure.dirac x := by
  rw [Measure.restrict_apply_univ, Measure.count_apply hA] at h1
  have : A.encard = 1 := by exact_mod_cast h1
  obtain ⟨x, rfl⟩ := Set.encard_eq_one.1 this
  refine ⟨x, ?_⟩
  rw [Measure.restrict_singleton, Measure.count_singleton, one_smul]

namespace ExplRun

variable (run : ExplRun sch P)

include run

/-- Sequential first-point exploration (f): the revealed point lies on the front. -/
theorem ae_dirac_front (D : SepPartSeq S) (hD : D.IsDissecting μ) (hdiff : ∀ x, μ {x} = 0)
    (k : ℕ) :
    ∀ᵐ ω ∂P, (run.H (k + 1) ω).last.2 Set.univ ≠ 0 →
      ∃ x : S, (run.H (k + 1) ω).last.2 = Measure.dirac x ∧
        D.atomMap (run.H (k + 1) ω).last.2 = Sum.inl x ∧
        sch.Rt k (run.H k ω) x = (run.H (k + 1) ω).last.1 := by
  filter_upwards [run.isPPP.ae_mem_bSimple D hD hdiff, run.ae_V_univ k, run.ae_front k]
    with ω hs hV hfront hne
  have hV1 : (run.H (k + 1) ω).last.2 Set.univ = 1 := hV.resolve_left hne
  have hl : (run.H (k + 1) ω).last = sch.stepAt k (run.H k ω) (run.N ω) := sch.Hfun_last k _
  have hA : MeasurableSet (probeRegion (sch.Rt k (run.H k ω))
      (probeRho μ (sch.Rt k (run.H k ω)) (sch.h k (run.H k ω)) (run.N ω))) :=
    measurableSet_probeRegion (sch.isProbe_Rt k _).measurable _
  have hVeq : (run.H (k + 1) ω).last.2 = (run.N ω).restrict (probeRegion (sch.Rt k (run.H k ω))
      (probeRho μ (sch.Rt k (run.H k ω)) (sch.h k (run.H k ω)) (run.N ω))) := by
    rw [hl]
    show probeV μ _ _ _ = _
    unfold probeV
    rw [tau_of_mem μ (run.lf ω)]
  have hcount := SepPartSeq.eq_count_restrict_of_mem_bSimple hs
  have hatoms := SepPartSeq.measurableSet_atoms hs
  have hV2 : (run.H (k + 1) ω).last.2 =
      Measure.count.restrict (probeRegion (sch.Rt k (run.H k ω))
        (probeRho μ (sch.Rt k (run.H k ω)) (sch.h k (run.H k ω)) (run.N ω)) ∩
        SepPartSeq.atoms (run.N ω)) := by
    rw [hVeq]
    calc (run.N ω).restrict (probeRegion (sch.Rt k (run.H k ω))
          (probeRho μ (sch.Rt k (run.H k ω)) (sch.h k (run.H k ω)) (run.N ω)))
        = (Measure.count.restrict (SepPartSeq.atoms (run.N ω))).restrict
            (probeRegion (sch.Rt k (run.H k ω))
              (probeRho μ (sch.Rt k (run.H k ω)) (sch.h k (run.H k ω)) (run.N ω))) :=
          congrArg (fun m : Measure S => m.restrict (probeRegion (sch.Rt k (run.H k ω))
            (probeRho μ (sch.Rt k (run.H k ω)) (sch.h k (run.H k ω)) (run.N ω)))) hcount
      _ = _ := Measure.restrict_restrict hA
  have hmeas : MeasurableSet (probeRegion (sch.Rt k (run.H k ω))
      (probeRho μ (sch.Rt k (run.H k ω)) (sch.h k (run.H k ω)) (run.N ω)) ∩
      SepPartSeq.atoms (run.N ω)) := hA.inter hatoms
  have := D.measurableSingletonClass
  obtain ⟨x, hx⟩ := restrict_count_eq_dirac hmeas (by rw [← hV2]; exact hV1)
  have hVx : (run.H (k + 1) ω).last.2 = Measure.dirac x := hV2.trans hx
  refine ⟨x, hVx, by rw [hVx]; exact D.atomMap_dirac x, ?_⟩
  have hm : MeasurableSet {y | sch.Rt k (run.H k ω) y ≠ (run.H (k + 1) ω).last.1} :=
    (measurableSet_eq_fun (sch.isProbe_Rt k _).measurable measurable_const).compl
  rw [hVx, Measure.dirac_apply' _ hm] at hfront
  by_contra hcon
  have : x ∈ {y | sch.Rt k (run.H k ω) y ≠ (run.H (k + 1) ω).last.1} := hcon
  simp [Set.indicator_of_mem this] at hfront

end ExplRun

end ElboimSly
