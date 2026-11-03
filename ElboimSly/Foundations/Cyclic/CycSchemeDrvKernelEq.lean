/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvKernel
public import Mathlib

/-!
# The driving scheme (b): `(ψ_{η'})_* K'_j(η') = K_j(Ψ_j(η'))`

The driving scheme (b). The two kernels are given by the same formula, in which
`v ∈ 𝒟` is replaced by the edge `{w, w + v}` at `w` (`stepEdge`), the weights `f'` and `f` agree
(`drvPhi_at`) and so do the masses `m`; and `ψ` maps `(h, 0) ↦ (h, 0)` and
`(t, δ_{(j_k, v, a_k + r + t)}) ↦ (t, δ_{(ι, {w, w + v}, c_δ(r + t))})`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
  {J : Type*} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) (P : CycPlan I d β) (sc : ℝ≥0∞)

/-- The edge of the environment probe attached to a driving index `a = (v, j)`. -/
noncomputable def drvEdge (st : CycScheme.State I d) (a : Dir d × J) : I × Edge d :=
  ((CycScheme.cur P st).data.copy, stepEdge (CycScheme.cur P st).pos a.1)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in
theorem drvT_nonneg (st : CycScheme.State I d) : 0 ≤ drvT jx P st :=
  add_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in
/-- The driving point at parameter `s` is sent by `φ` to the environment front point. -/
theorem drvPhi_at (st : CycScheme.State I d) (a : Dir d × J) {s : ℝ} (hs : 0 < s) :
    drvPhi (β := β) jx P st (a, drvX (jx := jx) P st a s) =
      ((drvEdge P st a).1, ((drvEdge P st a).2,
        circX (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS (drvEdge P st a) s)) := by
  unfold drvPhi drvEdge
  simp only
  congr 2
  have h1 : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.le
  have h2 := CycEntry.circX_front (β := β) (CycScheme.cur P st) (drvEdge P st a) s.toNNReal
  rw [h1] at h2
  refine Eq.trans ?_ h2.symm
  congr 1
  unfold drvX drvT
  have : ((drvOff jx st : ℝ≥0) : ℝ) + ((CycScheme.cur P st).time : ℝ) + 1 * s -
      (drvOff jx st : ℝ) = (((CycScheme.cur P st).time + s.toNNReal : ℝ≥0) : ℝ) := by
    push_cast
    rw [h1]; ring
  rw [this, Real.toNNReal_coe]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in
theorem segF_drv_eq (st : CycScheme.State I d) (a : Dir d × J) {s : ℝ} (hs : 0 < s) :
    segF (drvX (jx := jx) P st) (drvW (jx := jx) P st) (drvMask (β := β) jx P st) a s =
      segF (circX (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS) (fun _ _ => 1)
        (cycEquiv.symm ⁻¹' st.1.region β) (drvEdge P st a) s := by
  classical
  unfold segF
  have hpos : (0 : ℝ) < drvX (jx := jx) P st a s := by
    unfold drvX
    have := drvT_nonneg (jx := jx) P st
    linarith
  have hmem : ((a, drvX (jx := jx) P st a s) ∈ drvMask (β := β) jx P st) ↔
      ((drvEdge P st a, circX (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS
        (drvEdge P st a) s) ∈ cycEquiv.symm ⁻¹' st.1.region β) := by
    unfold drvMask
    simp only [mem_ofPred_eq]
    rw [drvPhi_at P st a hs]
    rfl
  by_cases hm : (a, drvX (jx := jx) P st a s) ∈ drvMask (β := β) jx P st
  · rw [ite_eq_left hm, ite_eq_left (hmem.1 hm)]
  · rw [ite_eq_right hm, ite_eq_right (fun h => hm (hmem.2 h))]
    unfold drvW
    rw [Set.indicator_of_mem (show drvT jx P st + 1 * s ∈ Set.Ioi (0 : ℝ) from hpos)]

omit [Fact (0 < β)] in
omit [Countable I] [MeasurableSingletonClass I] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in
/-- `a ↦ (ι, {w, w + v})` is a bijection from the driving probe set onto the environment probe set. -/
theorem sum_drvA_eq (st : CycScheme.State I d) (f : I × Edge d → ℝ≥0∞) :
    ∑ a ∈ drvA jx j0 st, f (drvEdge P st a) = ∑ e ∈ CycScheme.probeA P st, f e := by
  classical
  refine Finset.sum_bij (fun a _ => drvEdge P st a) (fun a ha => ?_) (fun a ha a' ha' h => ?_)
    (fun e he => ?_) (fun a _ => rfl)
  · rw [mem_drvA] at ha
    rw [CycScheme.probeA_mem_iff]
    exact ⟨ha.1, rfl, mem_stepEdge _ _⟩
  · rw [mem_drvA] at ha ha'
    have h1 : stepEdge (CycScheme.cur P st).pos a.1 = stepEdge (CycScheme.cur P st).pos a'.1 :=
      congrArg Prod.snd h
    have h2 := stepEdge_injective _ h1
    exact Prod.ext h2 (ha.2.trans ha'.2.symm)
  · rw [CycScheme.probeA_mem_iff] at he
    obtain ⟨hb, hc, hm⟩ := he
    obtain ⟨v, hv⟩ := exists_stepEdge _ _ hm
    refine ⟨(v, drvIdx jx j0 st), (mem_drvA j0 st _).2 ⟨hb, rfl⟩, ?_⟩
    exact Prod.ext hc.symm hv

theorem measurable_drvPsiOut_const (hj : ∀ k, Measurable (jx k)) (st : CycScheme.State I d) :
    Measurable (drvPsiOut (jx := jx) (β := β) j0 P sc st) :=
  (measurable_drvPsiOut j0 P sc hj).comp (measurable_const.prodMk measurable_id)

omit [Countable I] [MeasurableSingletonClass I] in
theorem drvPsiOut_zero (st : CycScheme.State I d) (r : ℝ≥0∞) :
    drvPsiOut (jx := jx) (β := β) j0 P sc st (r, 0) = (r, 0) := by
  unfold drvPsiOut
  rw [tau_of_mem _ (zero_mem_lfSet _)]
  simp

theorem drvPsiOut_dirac (st : CycScheme.State I d) (r : ℝ≥0∞) (p : DrvS d J)
    (hp : p ∈ drvF j0 P sc st (jx := jx)) (hj : ∀ k, Measurable (jx k)) :
    drvPsiOut (jx := jx) (β := β) j0 P sc st (r, Measure.dirac p) =
      (r, Measure.dirac (drvPhi (β := β) jx P st p)) := by
  classical
  unfold drvPsiOut
  have hlf : (Measure.dirac p : Measure (DrvS d J)) ∈ lfSet (drvIntensity d J) :=
    fun k => measure_lt_top _ _
  have hF : MeasurableSet (drvF j0 P sc st (jx := jx)) :=
    measurable_prodMk_left (measurableSet_drvF j0 P sc hj)
  have hφ : Measurable (drvPhi (β := β) jx P st : DrvS d J → CycS I d β) :=
    measurable_drvPhi (P := P) hj (st := fun _ : DrvS d J => st) measurable_const measurable_id
  simp only
  rw [tau_of_mem _ hlf, restrict_dirac' hF, ite_eq_left hp, Measure.map_dirac' hφ]

variable (U : Type*) [MeasurableSpace U] (hj : ∀ k, Measurable (jx k))

/-- The driving scheme (b): for all `k` and `η'`,
`(ψ_{η'})_* K'_k(η') = K_k(Ψ_k(η'))`. -/
theorem drvScheme_kernel (k : ℕ) (η : Hist U (DrvS d J) k) :
    ((drvScheme j0 P sc U hj).kernelAt k η).map
        (drvPsiOut (jx := jx) (β := β) j0 P sc
          (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η))) =
      (cycScheme P sc U).kernelAt k (drvPsi jx j0 P sc U k η) := by
  classical
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hψ := measurable_drvPsiOut_const (β := β) j0 P sc hj
    (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η))
  rw [lintegral_map hg hψ, drvScheme_lintegral_kernelAt j0 P sc U hj k η
      (g := fun o => g (drvPsiOut (jx := jx) (β := β) j0 P sc
        (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η)) o)) (hg.comp hψ),
    cycScheme_lintegral_kernelAt P sc k (drvPsi jx j0 P sc U k η) hg]
  dsimp only
  set st := CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η) with hst
  have hM : ∀ r, segM (drvA jx j0 st) (drvX (jx := jx) P st) (drvW (jx := jx) P st)
      (drvMask (β := β) jx P st) r =
      segM (CycScheme.probeA P st) (circX (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS)
        (fun _ _ => 1) (cycEquiv.symm ⁻¹' st.1.region β) r := fun r => by
    unfold segM
    refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [← sum_drvA_eq j0 P st (fun e => segF (circX (CycScheme.cur P st).frontT
      (CycScheme.cur P st).frontS) (fun _ _ => 1) (cycEquiv.symm ⁻¹' st.1.region β) e s)]
    exact Finset.sum_congr rfl fun a _ => segF_drv_eq P st a hs.1
  simp only [hM]
  congr 1
  · rw [drvPsiOut_zero]
  · rw [← sum_drvA_eq j0 P st (fun e => ∫⁻ s in Set.Ioc (0 : ℝ) (CycScheme.hOf P sc st),
      segF (circX (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS) (fun _ _ => 1)
        (cycEquiv.symm ⁻¹' st.1.region β) e s *
      (expNeg (segM (CycScheme.probeA P st) (circX (CycScheme.cur P st).frontT
          (CycScheme.cur P st).frontS) (fun _ _ => 1) (cycEquiv.symm ⁻¹' st.1.region β) s) *
        g (ENNReal.ofReal s, Measure.dirac (e.1, (e.2, circX (CycScheme.cur P st).frontT
          (CycScheme.cur P st).frontS e s)))))]
    refine Finset.sum_congr rfl fun a ha => ?_
    refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [segF_drv_eq P st a hs.1]
    congr 3
    have hp : (a, drvX (jx := jx) P st a s) ∈ drvF j0 P sc st (jx := jx) := by
      rw [mem_drvA] at ha
      refine ⟨ha.1, ha.2, ?_, ?_⟩
      · show 0 < drvT jx P st + 1 * s - drvT jx P st
        linarith [hs.1]
      · show drvT jx P st + 1 * s - drvT jx P st ≤ _
        linarith [hs.2]
    rw [drvPsiOut_dirac j0 P sc st _ _ hp hj, drvPhi_at P st a hs.1]

end ElboimSly.Cyclic

end
