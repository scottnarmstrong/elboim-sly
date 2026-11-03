/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDef
public import ElboimSly.Foundations.Cyclic.CycRecMeasA
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import Mathlib

/-!
# Measurability of the environment scheme, part 1: the horizon

The environment scheme (a), measurability: "`w`, `ς`, `Λ` and `h_cap, h_dl, h_gl` are
measurable functions of `ρ`. So is `h_fr`: it is the minimum, over the finitely many classes of
`Ring(ρ)` with `e' ∋ w`, of the representative in `(0, β]`."

All statements are for an arbitrary measurable space `α` and a measurable family of states
`st : α → State I d`, so they compose with the projections used in `measurable_upd`.

The inf `h_fr` over the known rings is rewritten as a countable inf over the indices
`n = ⟨k, a⟩` of `CycRec.ringAt` (`hFr_eq_iInf`); this is the "finitely many classes".
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
variable {α : Type*} [MeasurableSpace α]

/-! ### Scalars -/

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_time : Measurable (CycEntry.time : CycEntry I d → ℝ≥0) :=
  ENNReal.measurable_toNNReal.comp measurable_entry_len'

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_pos : Measurable (CycEntry.pos : CycEntry I d → Fin d → ℤ) :=
  measurable_fn_at (fun E : CycEntry I d => E.path) measurable_entry_path _ measurable_time

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_cnt_time : Measurable fun E : CycEntry I d => E.path.cnt E.time :=
  measurable_cnt_at (P := fun E : CycEntry I d => E.path) measurable_entry_path measurable_time

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_lastJump : Measurable (CycEntry.lastJump : CycEntry I d → ℝ≥0∞) :=
  measurable_index measurable_cnt_time (fun n => measurable_entry_jt n)

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_frontScalar :
    Measurable fun E : CycEntry I d => (E.data.phase + E.data.sgn * (E.time : ℝ), E.data.sgn) :=
  (measurable_entry_phase.add (measurable_entry_sgn.mul
    (measurable_coe_nnreal_real.comp measurable_time))).prodMk measurable_entry_sgn

/-- `circS` for constant data `(t₀, σ₀)`, jointly measurable in `(t₀, σ₀, y)`. -/
theorem measurable_circS_scalar {E : Type*} [MeasurableSpace E] (e : E) :
    Measurable fun q : ℝ × ℝ × AddCircle β => circS (fun _ : E => q.1) (fun _ => q.2.1) e q.2.2 := by
  unfold circS
  have hc : Measurable fun q : ℝ × ℝ × AddCircle β => ((q.1 : ℝ) : AddCircle β) :=
    AddCircle.measurable_mk'.comp measurable_fst
  have hy : Measurable fun q : ℝ × ℝ × AddCircle β => q.2.2 := measurable_snd.comp measurable_snd
  exact Measurable.ite (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
    (ElboimSly.Circle.measurable_rep.comp (hy.sub hc)) (ElboimSly.Circle.measurable_rep.comp (hc.sub hy))

omit [MeasurableSingletonClass I] [Countable I] in
/-- `circS` for the front data of a measurable family of entries (it does not depend on the
edge argument, since the front data are constant in `e`). -/
theorem measurable_circS_front {E : α → CycEntry I d} (hE : Measurable E) {y : α → AddCircle β}
    (hy : Measurable y) (e0 : I × Edge d) (e : α → I × Edge d) :
    Measurable fun a => circS (E a).frontT (E a).frontS (e a) (y a) := by
  have hs := measurable_frontScalar.comp hE
  have hg : Measurable fun a => (((E a).data.phase + (E a).data.sgn * ((E a).time : ℝ)),
      (E a).data.sgn, y a) := (measurable_fst.comp hs).prodMk ((measurable_snd.comp hs).prodMk hy)
  exact (measurable_circS_scalar (β := β) e0).comp hg

/-! ### The horizon -/

section Horizon

variable (P : CycPlan I d β) (sc : ℝ≥0∞)

omit [MeasurableSingletonClass I] [Countable I] in
omit [MeasurableSpace I] in
theorem hFr_eq_iInf (e0 : Edge d) (junk : CycEntry I d) (ρ : CycRec I d) (E : CycEntry I d) :
    CycScheme.hFr β ρ E = ⨅ n : ℕ,
      (open scoped Classical in
      if ρ.ringIdx junk n ∧ (ρ.ringAt (β := β) e0 junk n).1 = E.data.copy ∧
          Edge.Mem E.pos (ρ.ringAt (β := β) e0 junk n).2.1 then
        ENNReal.ofReal (circS E.frontT E.frontS ((ρ.ringAt (β := β) e0 junk n).1,
          (ρ.ringAt (β := β) e0 junk n).2.1) (ρ.ringAt (β := β) e0 junk n).2.2)
      else ⊤) := by
  classical
  unfold CycScheme.hFr
  refine le_antisymm (le_iInf fun n => ?_) (le_iInf₂ fun x hx => ?_)
  · by_cases h : ρ.ringIdx junk n ∧ (ρ.ringAt (β := β) e0 junk n).1 = E.data.copy ∧
        Edge.Mem E.pos (ρ.ringAt (β := β) e0 junk n).2.1
    · have hmem : ρ.ringAt (β := β) e0 junk n ∈ ρ.ringSet β :=
        (CycRec.mem_ringSet_iff e0 junk ρ _).2 ⟨n, h.1, rfl⟩
      refine (iInf₂_le _ hmem).trans ?_
      rw [ite_eq_left ⟨h.2.1, h.2.2⟩, ite_eq_left h]
    · rw [ite_eq_right h]; exact le_top
  · obtain ⟨n, hn, rfl⟩ := (CycRec.mem_ringSet_iff e0 junk ρ x).1 hx
    refine (iInf_le _ n).trans ?_
    by_cases h : (ρ.ringAt (β := β) e0 junk n).1 = E.data.copy ∧
        Edge.Mem E.pos (ρ.ringAt (β := β) e0 junk n).2.1
    · rw [ite_eq_left ⟨hn, h⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h]

omit [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] in
theorem hFr_of_isEmpty [IsEmpty (Edge d)] (ρ : CycRec I d) (E : CycEntry I d) :
    CycScheme.hFr β ρ E = ⊤ := by
  unfold CycScheme.hFr
  refine top_le_iff.1 (le_iInf₂ fun x _ => ?_)
  exact (IsEmpty.false x.2.1).elim

theorem measurable_hFr {ρ : α → CycRec I d} {E : α → CycEntry I d} (hρ : Measurable ρ)
    (hE : Measurable E) : Measurable fun a => CycScheme.hFr β (ρ a) (E a) := by
  classical
  rcases isEmpty_or_nonempty (Edge d) with hemp | ⟨⟨e0⟩⟩
  · simp only [hFr_of_isEmpty]; exact measurable_const
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a0⟩⟩
  · intro s _
    have : (fun a => CycScheme.hFr β (ρ a) (E a)) ⁻¹' s = ∅ := Set.eq_empty_of_isEmpty _
    rw [this]; exact MeasurableSet.empty
  set junk := E a0 with hjunk
  obtain ⟨i0⟩ : Nonempty I := ⟨(E a0).data.copy⟩
  have : Nonempty (CycEntry I d) := ⟨junk⟩
  have : (fun a => CycScheme.hFr β (ρ a) (E a)) = fun a => ⨅ n : ℕ,
      (if (ρ a).ringIdx junk n ∧ ((ρ a).ringAt (β := β) e0 junk n).1 = (E a).data.copy ∧
          Edge.Mem (E a).pos ((ρ a).ringAt (β := β) e0 junk n).2.1 then
        ENNReal.ofReal (circS (E a).frontT (E a).frontS (((ρ a).ringAt (β := β) e0 junk n).1,
          ((ρ a).ringAt (β := β) e0 junk n).2.1) ((ρ a).ringAt (β := β) e0 junk n).2.2)
      else ⊤) := funext fun a => hFr_eq_iInf e0 junk (ρ a) (E a)
  rw [this]
  refine Measurable.iInf fun n => ?_
  have hat : Measurable fun a => (ρ a).ringAt (β := β) e0 junk n :=
    (measurable_ringAt e0 junk n).comp hρ
  have hcopy : Measurable fun a => (E a).data.copy := measurable_entry_copy.comp hE
  have hposm : Measurable fun a => (E a).pos := measurable_pos.comp hE
  have hed : Measurable fun a => ((ρ a).ringAt (β := β) e0 junk n).2.1 :=
    (measurable_fst.comp measurable_snd).comp hat
  refine Measurable.ite ?_ ?_ measurable_const
  · refine (hρ (measurableSet_ringIdx junk n)).inter
      ((measurableSet_eq_fun (measurable_fst.comp hat) hcopy).inter ?_)
    have hpair : Measurable fun a => ((E a).pos, ((ρ a).ringAt (β := β) e0 junk n).2.1) :=
      hposm.prodMk hed
    exact hpair (Set.to_countable {z : (Fin d → ℤ) × Edge d | Edge.Mem z.1 z.2}).measurableSet
  · exact ENNReal.measurable_ofReal.comp (measurable_circS_front hE
      ((measurable_snd.comp measurable_snd).comp hat) (i0, e0) _)

variable {P} {sc} {st : α → CycScheme.State I d}

omit [MeasurableSingletonClass I] [Countable I] [Fact (0 < β)] in
theorem measurable_cur (hst : Measurable st) : Measurable fun a => CycScheme.cur P (st a) :=
  (measurable_lastEntry P.junk).comp (measurable_fst.comp hst)

omit [Fact (0 < β)] in
omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_hCap {E : α → CycEntry I d} (hE : Measurable E) :
    Measurable fun a => CycScheme.hCap β (E a) := by
  have hT : Measurable fun a => ((E a).time : ℝ) :=
    measurable_coe_nnreal_real.comp (measurable_time.comp hE)
  have hf : Measurable fun a => (⌊((E a).time : ℝ) / β⌋₊ : ℝ) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (Nat.measurable_floor.comp (hT.div_const β))
  exact ENNReal.measurable_ofReal.comp ((measurable_const.mul (hf.add_const 1)).sub hT)

omit [Fact (0 < β)] in
omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_hDl (hst : Measurable st) :
    Measurable fun a => CycScheme.hDl P (st a).1 (CycScheme.cur P (st a)) := by
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  have hE := measurable_cur (P := P) hst
  have hρ : Measurable fun a => (st a).1 := measurable_fst.comp hst
  have hj : Measurable fun a => (CycScheme.cur P (st a)).lastJump := measurable_lastJump.comp hE
  have hr : Measurable fun a => (((CycScheme.cur P (st a)).lastJump.toNNReal : ℝ≥0)) :=
    ENNReal.measurable_toNNReal.comp hj
  have hres : Measurable fun a => (st a).1.restrictLast (CycScheme.cur P (st a)).lastJump.toNNReal :=
    measurable_restrictLast.comp (hρ.prodMk hr)
  exact (hj.add (P.measurable_dlOf.comp hres)).sub
    (measurable_coe_nnreal_ennreal.comp (measurable_time.comp hE))

omit [MeasurableSingletonClass I] [Countable I] [Fact (0 < β)] in
theorem measurable_hGl (hst : Measurable st) :
    Measurable fun a => CycScheme.hGl sc (st a).1 (CycScheme.cur P (st a)) := by
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  have hE := measurable_cur (P := P) hst
  have hρ : Measurable fun a => (st a).1 := measurable_fst.comp hst
  exact (measurable_const.sub (CycRec.measurable_total.comp hρ)).sub
    (measurable_coe_nnreal_ennreal.comp (measurable_time.comp hE))

theorem measurable_hAll (hst : Measurable st) :
    Measurable fun a => CycScheme.hAll P sc (st a) := by
  have hE := measurable_cur (P := P) hst
  have hρ : Measurable fun a => (st a).1 := measurable_fst.comp hst
  exact ((measurable_hFr hρ hE).min (measurable_hCap hE)).min
    ((measurable_hDl hst).min (measurable_hGl hst))

theorem measurable_hOf (hst : Measurable st) :
    Measurable fun a => CycScheme.hOf P sc (st a) := by
  unfold CycScheme.hOf
  exact Measurable.ite (measurable_snd.comp hst (measurableSet_singleton true)) measurable_const
    (ENNReal.measurable_toNNReal.comp (measurable_hAll hst))

theorem measurable_sStar {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) : Measurable fun a => CycScheme.sStar P sc (st a) (o a) :=
  ENNReal.measurable_toNNReal.comp ((measurable_fst.comp ho).min
    (measurable_coe_nnreal_ennreal.comp (measurable_hOf hst)))

end Horizon

end ElboimSly.Cyclic

end
