/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvPsi
public import ElboimSly.Foundations.PPP.Exploration.SegmentReal
public import Mathlib

/-!
# The driving scheme (a): the raw probe is a real segment probe

The driving scheme (a), "for each `η'`, `(R'_j(η', ·), h)` is the segment probe of
Segment probes on E×mathbbT_β and E×mathbbR, case (ii), with `E := J × 𝒟`, `A := {(j_k, v) : v ∈ 𝒟}`, `t := a_k + r`,
`σ := +1`, `I := (0, ∞)` and mask `Z^pull`".

* `drvProbeR_eq_segR`: the identification;
* `isProbe_drvProbeR`: it is a probe for `drvIntensity d J`;
* `measurable_drvProbeR`: joint measurability in the state and the point.
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

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in
theorem mem_drvA (st : CycScheme.State I d) (e : Dir d × J) :
    e ∈ drvA jx j0 st ↔ st.2 = false ∧ e.2 = drvIdx jx j0 st := by
  classical
  unfold drvA
  cases hb : st.2
  · simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_image, Finset.mem_univ, true_and,
      true_and]
    constructor
    · rintro ⟨v, rfl⟩
      rfl
    · intro h
      exact ⟨e.1, Prod.ext rfl h.symm⟩
  · simp

omit [Countable I] [MeasurableSingletonClass I] [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] in
theorem drvProbeR_eq_segR (st : CycScheme.State I d) :
    drvProbeR (β := β) jx j0 P sc st = segR (drvA jx j0 st)
      (fun _ s => drvT jx P st + 1 * s) (fun _ y => 1 * (y - drvT jx P st))
      (CycScheme.hOf P sc st) (drvMask (β := β) jx P st) := by
  classical
  funext p
  unfold drvProbeR segR
  have hiff : (st.2 = false ∧ p.1.2 = drvIdx jx j0 st ∧ 0 < p.2 - drvT jx P st ∧
      p.2 - drvT jx P st ≤ (CycScheme.hOf P sc st : ℝ) ∧
      drvPhi (β := β) jx P st p ∉ st.1.region β) ↔
      (p.1 ∈ drvA jx j0 st ∧ p.2 ∈ segImg (fun _ s => drvT jx P st + 1 * s)
        (fun _ y => 1 * (y - drvT jx P st)) (CycScheme.hOf P sc st) p.1 ∧
        p ∉ drvMask (β := β) jx P st) := by
    rw [mem_drvA]
    simp only [segImg, mem_ofPred_eq, drvMask, one_mul]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨⟨h1, h2⟩, ⟨h3, h4, by ring⟩, h5⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4, -⟩, h5⟩
      exact ⟨h1, h2, h3, h4, h5⟩
  by_cases hc : st.2 = false ∧ p.1.2 = drvIdx jx j0 st ∧ 0 < p.2 - drvT jx P st ∧
      p.2 - drvT jx P st ≤ (CycScheme.hOf P sc st : ℝ) ∧
      drvPhi (β := β) jx P st p ∉ st.1.region β
  · rw [ite_eq_left hc, ite_eq_left (hiff.1 hc)]
    simp
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.2 h))]

variable (hj : ∀ k, Measurable (jx k))
include hj

theorem measurableSet_drvMask :
    MeasurableSet {x : CycScheme.State I d × DrvS d J |
      x.2 ∈ drvMask (β := β) jx P x.1} :=
  measurableSet_mem_region (ρ := fun x : CycScheme.State I d × DrvS d J => x.1.1)
    (x := fun x => drvPhi (β := β) jx P x.1 x.2) (measurable_fst.comp measurable_fst)
    (measurable_drvPhi (P := P) hj measurable_fst measurable_snd)

open scoped Classical in
theorem measurable_drvProbeR :
    Measurable fun q : CycScheme.State I d × DrvS d J => drvProbeR (β := β) jx j0 P sc q.1 q.2 := by
  classical
  have hS : MeasurableSet {q : CycScheme.State I d × DrvS d J |
      q.2 ∈ drvF j0 P sc q.1 (jx := jx) ∧ q.2 ∉ drvMask (β := β) jx P q.1} :=
    (measurableSet_drvF j0 P sc hj).inter (measurableSet_drvMask P hj).compl
  have hv : Measurable fun q : CycScheme.State I d × DrvS d J =>
      ENNReal.ofReal (q.2.2 - drvT jx P q.1) :=
    ENNReal.measurable_ofReal.comp ((measurable_snd.comp measurable_snd).sub
      (measurable_drvT (P := P) hj measurable_fst))
  have key : (fun q : CycScheme.State I d × DrvS d J =>
      drvProbeR (β := β) jx j0 P sc q.1 q.2) = fun q =>
      if q ∈ {q : CycScheme.State I d × DrvS d J |
        q.2 ∈ drvF j0 P sc q.1 (jx := jx) ∧ q.2 ∉ drvMask (β := β) jx P q.1} then
        ENNReal.ofReal (q.2.2 - drvT jx P q.1) else ⊤ := by
    funext q
    unfold drvProbeR
    simp only [drvF, drvMask, mem_ofPred_eq, and_assoc]
  rw [key]
  exact Measurable.ite hS hv measurable_const

theorem isProbe_drvProbeR (st : CycScheme.State I d) :
    IsProbe (drvIntensity d J) (drvProbeR (β := β) jx j0 P sc st) (CycScheme.hOf P sc st) := by
  rw [drvProbeR_eq_segR]
  have hS := segSetup_real (E := Dir d × J) (drvA jx j0 st) (fun _ => drvT jx P st) (fun _ => 1)
    (fun _ => Or.inl rfl) (CycScheme.hOf P sc st) (I := Set.Ioi 0) measurableSet_Ioi
  exact isProbe_segR (lam := volume.restrict (Set.Ioi (0 : ℝ))) hS
    (measurable_prodMk_left (measurableSet_drvMask P hj))

end ElboimSly.Cyclic

end
