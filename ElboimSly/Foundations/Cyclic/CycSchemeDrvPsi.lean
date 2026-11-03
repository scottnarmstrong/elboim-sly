/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvMeas1
public import ElboimSly.Foundations.PPP.Exploration.Section
public import Mathlib

/-!
# The driving scheme (a): the outcome map `ψ` and its measurability

The driving scheme (a). `drvF st` is the set `F = {(j_k, v, a_k + r + t) : t ∈ (0, h]}`,
`drvPhi` is `φ`, and `drvPsiOut st (r', ν') = (r', φ_*(τ(ν')|_F))` is `ψ_{η'}`.
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

/-- The set `F = {(j_k, v, a_k + r + t) : v ∈ 𝒟, t ∈ (0, h]}` (empty if ended). -/
def drvF (st : CycScheme.State I d) : Set (DrvS d J) :=
  {p | st.2 = false ∧ p.1.2 = drvIdx jx j0 st ∧ 0 < p.2 - drvT jx P st ∧
    p.2 - drvT jx P st ≤ (CycScheme.hOf P sc st : ℝ)}

/-- The outcome map `ψ_{η'}(r', ν') = (r', φ_*(τ(ν')|_F))`. -/
noncomputable def drvPsiOut (st : CycScheme.State I d) (o : Outcome (DrvS d J)) :
    Outcome (CycS I d β) :=
  (o.1, ((tau (drvIntensity d J) o.2).restrict (drvF j0 P sc st (jx := jx))).map
    (drvPhi (β := β) jx P st))

variable {α : Type*} [MeasurableSpace α] {st : α → CycScheme.State I d}

omit [Fact (0 < β)] in
omit [Countable I] [MeasurableSingletonClass I] in
theorem measurable_drvT (hj : ∀ k, Measurable (jx k)) (hst : Measurable st) :
    Measurable fun a => drvT jx P (st a) :=
  ((measurable_coe_nnreal_real.comp ((measurable_drvOff hj).comp hst)).add
    (measurable_coe_nnreal_real.comp (measurable_time.comp (measurable_cur hst))))

omit [Fact (0 < β)] in
omit [Countable I] [MeasurableSingletonClass I] in
theorem measurable_drvPhi (hj : ∀ k, Measurable (jx k)) (hst : Measurable st)
    {p : α → DrvS d J} (hp : Measurable p) :
    Measurable fun a => drvPhi (β := β) jx P (st a) (p a) := by
  have hE := measurable_cur (P := P) hst
  have h1 : Measurable fun a => (CycScheme.cur P (st a)).data.copy :=
    measurable_entry_copy.comp hE
  have h2 : Measurable fun a => stepEdge (CycScheme.cur P (st a)).pos (p a).1.1 :=
    (measurable_of_countable (fun z : (Fin d → ℤ) × Dir d => stepEdge z.1 z.2)).comp
      ((measurable_pos.comp hE).prodMk (measurable_fst.comp (measurable_fst.comp hp)))
  have h3 : Measurable fun a => (CycScheme.cur P (st a)).data.clock β
      ((p a).2 - ((drvOff jx (st a) : ℝ≥0) : ℝ)).toNNReal :=
    measurable_clock.comp (hE.prodMk (measurable_real_toNNReal.comp
      ((measurable_snd.comp hp).sub (measurable_coe_nnreal_real.comp
        ((measurable_drvOff hj).comp hst)))))
  exact h1.prodMk (h2.prodMk h3)

theorem measurableSet_drvF (hj : ∀ k, Measurable (jx k)) :
    MeasurableSet {x : CycScheme.State I d × DrvS d J | x.2 ∈ drvF j0 P sc x.1 (jx := jx)} := by
  have hst : Measurable fun x : CycScheme.State I d × DrvS d J => x.1 := measurable_fst
  have hy : Measurable fun x : CycScheme.State I d × DrvS d J => x.2.2 :=
    measurable_snd.comp measurable_snd
  have hT := measurable_drvT (P := P) hj hst
  have h1 : MeasurableSet {x : CycScheme.State I d × DrvS d J | x.1.2 = false} :=
    (measurable_snd.comp measurable_fst) (measurableSet_singleton false)
  have h2 : MeasurableSet {x : CycScheme.State I d × DrvS d J |
      x.2.1.2 = drvIdx jx j0 x.1} :=
    measurableSet_eq_fun (measurable_snd.comp (measurable_fst.comp measurable_snd))
      ((measurable_drvIdx hj j0).comp hst)
  have h3 : MeasurableSet {x : CycScheme.State I d × DrvS d J | 0 < x.2.2 - drvT jx P x.1} :=
    measurableSet_lt measurable_const (hy.sub hT)
  have h4 : MeasurableSet {x : CycScheme.State I d × DrvS d J |
      x.2.2 - drvT jx P x.1 ≤ (CycScheme.hOf P sc x.1 : ℝ)} :=
    measurableSet_le (hy.sub hT) (measurable_coe_nnreal_real.comp (measurable_hOf (P := P)
      (sc := sc) hst))
  exact h1.inter (h2.inter (h3.inter h4))

theorem measurable_drvPsiOut (hj : ∀ k, Measurable (jx k)) :
    Measurable fun q : CycScheme.State I d × Outcome (DrvS d J) =>
      drvPsiOut (jx := jx) (β := β) j0 P sc q.1 q.2 := by
  refine (measurable_fst.comp measurable_snd).prodMk ?_
  rw [measurable_measure_iff]
  intro B hB
  have hZ : MeasurableSet {x : CycScheme.State I d × DrvS d J |
      x.2 ∈ drvF j0 P sc x.1 (jx := jx) ∧ drvPhi (β := β) jx P x.1 x.2 ∈ B} :=
    (measurableSet_drvF j0 P sc hj).inter
      ((measurable_drvPhi (P := P) hj measurable_fst measurable_snd) hB)
  have key : ∀ q : CycScheme.State I d × Outcome (DrvS d J),
      (drvPsiOut (jx := jx) (β := β) j0 P sc q.1 q.2).2 B =
        tau (drvIntensity d J) q.2.2 (Prod.mk q.1 ⁻¹' {x : CycScheme.State I d × DrvS d J |
          x.2 ∈ drvF j0 P sc x.1 (jx := jx) ∧ drvPhi (β := β) jx P x.1 x.2 ∈ B}) := by
    intro q
    have hφ : Measurable (drvPhi (β := β) jx P q.1 : DrvS d J → CycS I d β) :=
      measurable_drvPhi (P := P) hj (st := fun _ : DrvS d J => q.1) measurable_const
        measurable_id
    have hF : MeasurableSet (drvF j0 P sc q.1 (jx := jx)) :=
      measurable_prodMk_left (measurableSet_drvF j0 P sc hj)
    show (((tau (drvIntensity d J) q.2.2).restrict (drvF j0 P sc q.1 (jx := jx))).map
      (drvPhi (β := β) jx P q.1)) B = _
    rw [Measure.map_apply hφ hB, Measure.restrict_apply (hφ hB)]
    congr 1
    ext x
    simp [and_comm]
  have hm : Measurable fun q : CycScheme.State I d × Outcome (DrvS d J) =>
      tau (drvIntensity d J) q.2.2 (Prod.mk q.1 ⁻¹' {x : CycScheme.State I d × DrvS d J |
          x.2 ∈ drvF j0 P sc x.1 (jx := jx) ∧ drvPhi (β := β) jx P x.1 x.2 ∈ B}) :=
    (measurable_tau_section (drvIntensity d J) hZ).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  convert hm using 1
  funext q
  exact key q

end ElboimSly.Cyclic

end
