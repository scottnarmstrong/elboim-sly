/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeMeas2
public import ElboimSly.Foundations.PPP.Exploration.SchemeMeas
public import Mathlib

/-!
# Measurability of the environment scheme, part 3: the update and the probes

The environment scheme (a): "the update `(ρ, ε, o) ↦ (ρ_{j+1}, ε_{j+1})` is measurable, and
`η ↦ (ρ_j(η), ε_j(η))` is measurable by induction"; "the data of segment probes on E×mathbbT_β and E×mathbbR (b) are
measurable in `η`".

* `measurable_upd`: the update is measurable on `State × Outcome`;
* `measurable_stateAt`: `η ↦ (ρ_j(η), ε_j(η))` is measurable;
* `probeR_apply`, `measurable_probeR`: the raw probe is jointly measurable in `(state, point)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
variable {α : Type*} [MeasurableSpace α]
variable {P : CycPlan I d β} {sc : ℝ≥0∞} {st : α → CycScheme.State I d}

/-! ### The update -/

theorem measurable_newEntry' {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) : Measurable fun a => CycScheme.newEntry P sc (st a) (o a) := by
  have hE := measurable_cur (P := P) hst
  have hs := measurable_sStar (P := P) (sc := sc) hst ho
  have hv := measurable_newV P sc hst ho
  refine (measurable_fst.comp hE).prodMk ?_
  exact measurable_cycPath_extend.comp ((measurable_snd.comp hE).prodMk
    (((measurable_time.comp hE).add hs).prodMk hv))

theorem measurable_newRec {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) : Measurable fun a => CycScheme.newRec P sc (st a) (o a) := by
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  exact measurable_setLast.comp ((measurable_fst.comp hst).prodMk (measurable_newEntry' hst ho))

theorem measurableSet_stops {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) : MeasurableSet {a | CycScheme.stops P sc (st a) (o a)} := by
  classical
  have hE := measurable_cur (P := P) hst
  have hnr := measurable_newRec (P := P) (sc := sc) hst ho
  have hv := measurable_newV P sc hst ho
  have hs := measurable_sStar (P := P) (sc := sc) hst ho
  have hne : MeasurableSet {a | CycScheme.newV P sc (st a) (o a) = (CycScheme.cur P (st a)).pos} :=
    measurableSet_eq_fun hv (measurable_pos.comp hE)
  have hstop : MeasurableSet {a | P.stOf (CycScheme.newRec P sc (st a) (o a)) = true} :=
    (P.measurable_stOf.comp hnr) (measurableSet_singleton true)
  have hdl : MeasurableSet {a | P.dlOf (CycScheme.newRec P sc (st a) (o a)) = 0} :=
    (P.measurable_dlOf.comp hnr) (measurableSet_singleton 0)
  have hdl2 : MeasurableSet {a | (CycScheme.sStar P sc (st a) (o a) : ℝ≥0∞) =
      CycScheme.hDl P (st a).1 (CycScheme.cur P (st a))} :=
    measurableSet_eq_fun (measurable_coe_nnreal_ennreal.comp hs) (measurable_hDl hst)
  have : {a | CycScheme.stops P sc (st a) (o a)} =
      ({a | CycScheme.newV P sc (st a) (o a) = (CycScheme.cur P (st a)).pos}ᶜ ∩
        ({a | P.stOf (CycScheme.newRec P sc (st a) (o a)) = true} ∪
          {a | P.dlOf (CycScheme.newRec P sc (st a) (o a)) = 0})) ∪
      ({a | CycScheme.newV P sc (st a) (o a) = (CycScheme.cur P (st a)).pos} ∩
        {a | (CycScheme.sStar P sc (st a) (o a) : ℝ≥0∞) =
          CycScheme.hDl P (st a).1 (CycScheme.cur P (st a))}) := by
    ext a
    simp only [CycScheme.stops, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    by_cases h : CycScheme.newV P sc (st a) (o a) = (CycScheme.cur P (st a)).pos <;> simp [h]
  rw [this]
  exact (hne.compl.inter (hstop.union hdl)).union (hne.inter hdl2)

theorem measurable_upd' {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) : Measurable fun a => CycScheme.upd P sc (st a) (o a) := by
  classical
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  have hnr := measurable_newRec (P := P) (sc := sc) hst ho
  have hs := measurable_sStar (P := P) (sc := sc) hst ho
  have hρ : Measurable fun a => (st a).1 := measurable_fst.comp hst
  have hE := measurable_cur (P := P) hst
  unfold CycScheme.upd
  refine Measurable.ite (measurable_snd.comp hst (measurableSet_singleton true)) hst ?_
  refine Measurable.ite (measurableSet_stops hst ho) ?_ ?_
  · refine Measurable.ite ?_ ?_ (hnr.prodMk measurable_const)
    · exact (CycRec.measurable_num.comp hρ) (MeasurableSet.of_discrete (s := {x : ℕ∞ | x < P.K}))
    · exact (measurable_push.comp (hnr.prodMk
        (measurable_newEntry.comp (P.measurable_startOf.comp hnr)))).prodMk measurable_const
  · refine hnr.prodMk (measurable_to_bool ?_)
    have hset : MeasurableSet {a | (CycScheme.sStar P sc (st a) (o a) : ℝ≥0∞) =
        CycScheme.hGl sc (st a).1 (CycScheme.cur P (st a))} :=
      measurableSet_eq_fun (measurable_coe_nnreal_ennreal.comp hs) (measurable_hGl hst)
    convert hset using 1
    ext a
    simp

/-- The environment scheme (a): the update is measurable. -/
theorem CycScheme.measurable_upd (P : CycPlan I d β) (sc : ℝ≥0∞) :
    Measurable fun q : CycScheme.State I d × Outcome (CycS I d β) => CycScheme.upd P sc q.1 q.2 :=
  measurable_upd' (P := P) (sc := sc) measurable_fst measurable_snd

/-- The environment scheme (a): `η ↦ (ρ_j(η), ε_j(η))` is measurable. -/
theorem CycScheme.measurable_stateAt {U : Type*} [MeasurableSpace U] (P : CycPlan I d β)
    (sc : ℝ≥0∞) (k : ℕ) : Measurable (CycScheme.stateAt (U := U) P sc k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (CycScheme.measurable_upd P sc).comp
      ((ih.comp (Hist.measurable_init k)).prodMk (Hist.measurable_last k))

/-! ### The probe -/

omit [MeasurableSingletonClass I] [Countable I] [Fact (0 < β)] in
theorem CycScheme.probeA_mem_iff (P : CycPlan I d β) (st : CycScheme.State I d)
    (x : I × Edge d) :
    x ∈ CycScheme.probeA P st ↔ st.2 = false ∧ x.1 = (CycScheme.cur P st).data.copy ∧
      Edge.Mem (CycScheme.cur P st).pos x.2 := by
  unfold CycScheme.probeA
  cases hb : st.2
  · simp [mem_edgesAt]
  · simp

open scoped Classical in
omit [MeasurableSingletonClass I] [Countable I] in
theorem CycScheme.probeR_apply (P : CycPlan I d β) (sc : ℝ≥0∞) (st : CycScheme.State I d)
    (ι : I) (e : Edge d) (θ : AddCircle β) :
    CycScheme.probeR P sc st (ι, (e, θ)) =
      if st.2 = false ∧ ι = (CycScheme.cur P st).data.copy ∧ Edge.Mem (CycScheme.cur P st).pos e ∧
          circS (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS (ι, e) θ ≤
            (CycScheme.hOf P sc st : ℝ)
      then ENNReal.ofReal (circS (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS (ι, e) θ)
      else ⊤ := by
  unfold CycScheme.probeR
  rw [cycSegR_apply]
  unfold segR
  have hσ := (CycScheme.cur P st).frontS_cases
  have hX := circX_sinv (β := β) (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS hσ (ι, e) θ
  have hpos : 0 < circS (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS (ι, e) θ := by
    unfold circS
    split_ifs
    · exact (ElboimSly.Circle.rep_mem _).1
    · exact (ElboimSly.Circle.rep_mem _).1
  have hiff : ((ι, e) ∈ CycScheme.probeA P st ∧
      θ ∈ segImg (circX (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS)
        (circS (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS) (CycScheme.hOf P sc st)
        (ι, e) ∧ ((((ι, e), θ) : (I × Edge d) × AddCircle β) ∉ (cycEquiv.symm ⁻¹' (∅ : Set (CycS I d β))))) ↔
      (st.2 = false ∧ ι = (CycScheme.cur P st).data.copy ∧ Edge.Mem (CycScheme.cur P st).pos e ∧
          circS (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS (ι, e) θ ≤
            (CycScheme.hOf P sc st : ℝ)) := by
    rw [CycScheme.probeA_mem_iff]
    simp only [segImg, mem_ofPred_eq, hX, hpos, true_and, preimage_empty, mem_empty_iff_false,
      not_false_eq_true, and_true, and_assoc]
  by_cases hc : st.2 = false ∧ ι = (CycScheme.cur P st).data.copy ∧
      Edge.Mem (CycScheme.cur P st).pos e ∧
      circS (CycScheme.cur P st).frontT (CycScheme.cur P st).frontS (ι, e) θ ≤
        (CycScheme.hOf P sc st : ℝ)
  · rw [ite_eq_left (hiff.2 hc), ite_eq_left hc]
  · rw [ite_eq_right (fun h => hc (hiff.1 h)), ite_eq_right hc]

/-- The raw probe is jointly measurable in the state and the point. -/
theorem CycScheme.measurable_probeR (P : CycPlan I d β) (sc : ℝ≥0∞) :
    Measurable fun q : CycScheme.State I d × CycS I d β => CycScheme.probeR P sc q.1 q.2 := by
  classical
  have hst : Measurable fun q : CycScheme.State I d × CycS I d β => q.1 := measurable_fst
  have hE := measurable_cur (P := P) hst
  rcases isEmpty_or_nonempty (I × Edge d) with hemp | ⟨⟨e0⟩⟩
  · intro s _
    have : (fun q : CycScheme.State I d × CycS I d β => CycScheme.probeR P sc q.1 q.2) ⁻¹' s =
        ∅ := by
      ext q; exact (IsEmpty.false (q.2.1, q.2.2.1)).elim
    rw [this]; exact MeasurableSet.empty
  have hy : Measurable fun q : CycScheme.State I d × CycS I d β => q.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hval : Measurable fun q : CycScheme.State I d × CycS I d β =>
      ENNReal.ofReal (circS (CycScheme.cur P q.1).frontT (CycScheme.cur P q.1).frontS
        (q.2.1, q.2.2.1) q.2.2.2) :=
    ENNReal.measurable_ofReal.comp (measurable_circS_front hE hy e0
      (fun q => (q.2.1, q.2.2.1)))
  have hset : MeasurableSet {q : CycScheme.State I d × CycS I d β |
      q.1.2 = false ∧ q.2.1 = (CycScheme.cur P q.1).data.copy ∧
      Edge.Mem (CycScheme.cur P q.1).pos q.2.2.1 ∧
      circS (CycScheme.cur P q.1).frontT (CycScheme.cur P q.1).frontS (q.2.1, q.2.2.1) q.2.2.2 ≤
        (CycScheme.hOf P sc q.1 : ℝ)} := by
    refine (measurable_snd.comp measurable_fst (measurableSet_singleton false)).inter
      ((measurableSet_eq_fun (measurable_fst.comp measurable_snd)
        (measurable_entry_copy.comp hE)).inter (MeasurableSet.inter ?_ ?_))
    · have : Measurable fun q : CycScheme.State I d × CycS I d β =>
          ((CycScheme.cur P q.1).pos, q.2.2.1) :=
        (measurable_pos.comp hE).prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
      exact this (Set.to_countable {z : (Fin d → ℤ) × Edge d | Edge.Mem z.1 z.2}).measurableSet
    · exact measurableSet_le (measurable_circS_front hE hy e0 (fun q => (q.2.1, q.2.2.1)))
        (measurable_coe_nnreal_real.comp ((measurable_hOf hst).comp measurable_id))
  have : (fun q : CycScheme.State I d × CycS I d β => CycScheme.probeR P sc q.1 q.2) =
      fun q => if q ∈ {q : CycScheme.State I d × CycS I d β |
        q.1.2 = false ∧ q.2.1 = (CycScheme.cur P q.1).data.copy ∧
        Edge.Mem (CycScheme.cur P q.1).pos q.2.2.1 ∧
        circS (CycScheme.cur P q.1).frontT (CycScheme.cur P q.1).frontS (q.2.1, q.2.2.1)
          q.2.2.2 ≤ (CycScheme.hOf P sc q.1 : ℝ)}
        then ENNReal.ofReal (circS (CycScheme.cur P q.1).frontT (CycScheme.cur P q.1).frontS
          (q.2.1, q.2.2.1) q.2.2.2) else ⊤ := by
    funext q
    rcases q with ⟨st, ι, e, θ⟩
    exact CycScheme.probeR_apply P sc st ι e θ
  rw [this]
  exact Measurable.ite hset hval measurable_const

end ElboimSly.Cyclic

end
