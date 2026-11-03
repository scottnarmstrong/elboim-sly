/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycContGlue
public import ElboimSly.Foundations.Cyclic.CycRegenLaw
public import ElboimSly.Foundations.Cyclic.CycHitDef
public import Mathlib

/-!
# The regenerated walk as a glue of independent pieces

Plan-level coupling after a stopping time (d), proof. For a good environment, the regenerated walk of the
slices `ν^k` is `contGlue` of the walk of `ν^0` and the walks of `ν^{k+1}`
(`regenWalk_eq_contGlue`). For a `PPP(# ⊗ μ_β)` the walk of the first slice is independent of the
walks of the others, and the shifted sequence has the law of the sequence (`law_head_tail`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem walkMap_eq_cycWalk {ν : Measure (RingSpace d β)} (hν : Good ν) (s : ℝ≥0) :
    walkMap ν s = ElboimSly.cycWalk ν 0 0 (s : ℝ) := by
  classical
  unfold walkMap
  rw [ite_eq_left hν]

/-- For a good environment, the regenerated walk is the glue of the first walk and the shifted
sequence of walks. -/
theorem regenWalk_eq_contGlue {ν : ℕ → Measure (RingSpace d β)} (hg : ∀ k, Good (ν k))
    (t : ℝ≥0) :
    ElboimSly.regenWalk ν (t : ℝ) =
      contGlue β.toNNReal (walkMap (ν 0)) (fun k => walkMap (ν (k + 1))) t := by
  have hp : contPieces (walkMap (ν 0)) (fun k => walkMap (ν (k + 1))) =
      fun (k : ℕ) (s : ℝ≥0) => ElboimSly.cycWalk (ν k) 0 0 (s : ℝ) := by
    funext k s
    cases k with
    | zero => exact walkMap_eq_cycWalk (hg 0) s
    | succ k => exact walkMap_eq_cycWalk (hg (k + 1)) s
  rw [← gluedWalk_eq_regenWalk]
  unfold contGlue
  rw [hp]
  have : (fun k => pathTreg β.toNNReal
      (fun s : ℝ≥0 => ElboimSly.cycWalk (ν k) 0 0 (s : ℝ))) = fun k => ElboimSly.cycTreg (ν k) :=
    funext fun k => pathTreg_cycWalk (ν k)
  rw [this]

section law

variable {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
include hN

theorem measurable_walkSlice (k : ℕ) :
    Measurable fun ω => walkMap (cycSlice k (N ω)) :=
  measurable_walkMap.comp (isPoissonPointProcess_slice hN k).measurable

theorem iIndepFun_walkSlice : iIndepFun (fun k ω => walkMap (cycSlice k (N ω))) Pr :=
  (iIndepFun_slice hN).comp (fun _ ν => walkMap ν) fun _ => measurable_walkMap

theorem law_walkSlice (k : ℕ) :
    Pr.map (fun ω => walkMap (cycSlice k (N ω))) = Pr.map (fun ω => walkMap (cycSlice 0 (N ω))) := by
  have h := (isPoissonPointProcess_slice hN 0).map_eq_map (isPoissonPointProcess_slice hN k)
  have e : ∀ j, (fun ω => walkMap (cycSlice j (N ω))) =
      walkMap ∘ (fun ω => cycSlice j (N ω)) := fun j => rfl
  rw [e k, e 0, ← Measure.map_map measurable_walkMap (isPoissonPointProcess_slice hN k).measurable,
    ← Measure.map_map measurable_walkMap (isPoissonPointProcess_slice hN 0).measurable, h]

/-- The tail of the sequence of walks has the law of the sequence. -/
theorem law_tail :
    Pr.map (fun ω k => walkMap (cycSlice (k + 1) (N ω))) =
      Pr.map (fun ω k => walkMap (cycSlice k (N ω))) := by
  have := hN.isProbabilityMeasure
  have hm : ∀ k, Measurable fun ω => walkMap (cycSlice k (N ω)) := measurable_walkSlice hN
  have h1 := (iIndepFun_walkSlice hN).map_fun_eq_infinitePi_map hm
  have h2 := ((iIndepFun_walkSlice hN).precomp (g := Nat.succ) Nat.succ_injective).map_fun_eq_infinitePi_map
    (fun k => hm (k + 1))
  rw [h2, h1]
  congr 1
  funext k
  exact law_walkSlice hN (k + 1) |>.trans (law_walkSlice hN k).symm

/-- The walk of the first slice is independent of the walks of the others. -/
theorem indepFun_head_tail :
    IndepFun (fun ω => walkMap (cycSlice 0 (N ω))) (fun ω k => walkMap (cycSlice (k + 1) (N ω))) Pr := by
  have := hN.isProbabilityMeasure
  have hm : ∀ k, Measurable fun ω => walkMap (cycSlice k (N ω)) := measurable_walkSlice hN
  have hI : iIndep (fun k => MeasurableSpace.comap (fun ω => walkMap (cycSlice k (N ω)))
      inferInstance) Pr := iIndepFun_walkSlice hN
  have hle : ∀ k, MeasurableSpace.comap (fun ω => walkMap (cycSlice k (N ω))) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) := fun k => (hm k).comap_le
  have key := indep_iSup_of_disjoint hle hI (S := {0}) (T := {i | 1 ≤ i}) (by
    rw [Set.disjoint_left]; intro i hi hi'; simp at hi hi'; omega)
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right key ?_) ?_
  · -- the tail is measurable with respect to the later slices
    have : Measurable[⨆ i ∈ {i : ℕ | 1 ≤ i},
        MeasurableSpace.comap (fun ω => walkMap (cycSlice i (N ω))) inferInstance]
        (fun ω k => walkMap (cycSlice (k + 1) (N ω))) := by
      let : MeasurableSpace Ω := ⨆ i ∈ {i : ℕ | 1 ≤ i},
        MeasurableSpace.comap (fun ω => walkMap (cycSlice i (N ω))) inferInstance
      refine measurable_pi_iff.2 fun k => ?_
      exact Measurable.mono (comap_measurable _) (le_iSup₂_of_le (k + 1) (by simp) le_rfl) le_rfl
    exact this.comap_le
  · exact le_iSup₂_of_le 0 rfl le_rfl

/-- The law of (first walk, tail) is the product of the law of the first walk and the law of the
sequence of walks. -/
theorem law_head_tail :
    Pr.map (fun ω => (walkMap (cycSlice 0 (N ω)), fun k => walkMap (cycSlice (k + 1) (N ω)))) =
      (Pr.map (fun ω => walkMap (cycSlice 0 (N ω)))).prod
        (Pr.map (fun ω k => walkMap (cycSlice k (N ω)))) := by
  have := hN.isProbabilityMeasure
  have hm : ∀ k, Measurable fun ω => walkMap (cycSlice k (N ω)) := measurable_walkSlice hN
  have ht : Measurable fun ω k => walkMap (cycSlice (k + 1) (N ω)) :=
    measurable_pi_iff.2 fun k => hm (k + 1)
  rw [← law_tail hN]
  exact (indepFun_iff_map_prod_eq_prod_map_map (hm 0).aemeasurable ht.aemeasurable).1
    (indepFun_head_tail hN)

end law

end ElboimSly.Cyclic

end
