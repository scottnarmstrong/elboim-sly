/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeMeas1
public import Mathlib

/-!
# Measurability of the environment scheme, part 2: forced and fresh events

The environment scheme (a), measurability: "The fresh-event test is measurable by
Dirac masses (b) and measurability of record functionals (a), and stop tests are equalities of measurable
functions."

* `measurableSet_mem_ringSet`: `{a | x a ∈ Ring(ρ a)}`;
* `forcedEdge_eq_some_iff`, `freshEdge_eq_some_iff` and their measurable level sets;
* `measurable_newV`: the new value of the path at `r + s*`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
variable {α : Type*} [MeasurableSpace α]

/-! ### Atoms -/

theorem measurable_prod_sum {S U γ : Type*} [MeasurableSpace S] [MeasurableSpace U]
    [MeasurableSpace γ] (F : α × (S ⊕ U) → γ)
    (h1 : Measurable fun p : α × S => F (p.1, Sum.inl p.2))
    (h2 : Measurable fun p : α × U => F (p.1, Sum.inr p.2)) : Measurable F := by
  have : F = Sum.elim (fun p : α × S => F (p.1, Sum.inl p.2))
      (fun p : α × U => F (p.1, Sum.inr p.2)) ∘ (MeasurableEquiv.prodSumDistrib α S U) := by
    funext p
    rcases p with ⟨a, x | u⟩ <;> rfl
  rw [this]
  exact (Measurable.sumElim h1 h2).comp (MeasurableEquiv.prodSumDistrib α S U).measurable

theorem measurableSet_atom_cond {S : Type*} [MeasurableSpace S] {Y : α → S ⊕ Unit}
    (hY : Measurable Y) {T : Set (α × S)} (hT : MeasurableSet T) :
    MeasurableSet {a | ∃ x, Y a = Sum.inl x ∧ (a, x) ∈ T} := by
  classical
  let F : α × (S ⊕ Unit) → Bool := fun p =>
    Sum.elim (fun x => if (p.1, x) ∈ T then true else false) (fun _ => false) p.2
  have hF : Measurable F := by
    refine measurable_prod_sum F ?_ ?_
    · have : (fun p : α × S => F (p.1, Sum.inl p.2)) =
          fun p => if p ∈ T then true else false := rfl
      rw [this]
      exact Measurable.ite hT measurable_const measurable_const
    · exact measurable_const
  have : {a | ∃ x, Y a = Sum.inl x ∧ (a, x) ∈ T} = (fun a => F (a, Y a)) ⁻¹' {true} := by
    ext a
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    rcases hYa : Y a with x | u
    · simp [F]
    · simp [F]
  rw [this]
  exact (hF.comp (measurable_id.prodMk hY)) (measurableSet_singleton true)

/-! ### Membership in the known rings -/

omit [Fact (0 < β)] in
theorem measurableSet_mem_ringSet (junk : CycEntry I d) {ρ : α → CycRec I d}
    {x : α → I × RingSpace d β} (hρ : Measurable ρ) (hx : Measurable x) :
    MeasurableSet {a | x a ∈ (ρ a).ringSet β} := by
  rcases isEmpty_or_nonempty (Edge d) with hemp | ⟨⟨e0⟩⟩
  · have : {a | x a ∈ (ρ a).ringSet β} = ∅ := by
      ext a; exact (IsEmpty.false (x a).2.1).elim
    rw [this]; exact MeasurableSet.empty
  have : Nonempty (CycEntry I d) := ⟨junk⟩
  have : {a | x a ∈ (ρ a).ringSet β} = ⋃ n : ℕ, {a | (ρ a).ringIdx junk n} ∩
      {a | x a = (ρ a).ringAt (β := β) e0 junk n} := by
    ext a
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [CycRec.mem_ringSet_iff e0 junk]
  rw [this]
  exact MeasurableSet.iUnion fun n => (hρ (measurableSet_ringIdx junk n)).inter
    (measurableSet_eq_fun hx ((measurable_ringAt e0 junk n).comp hρ))

theorem measurableSet_mem_region {ρ : α → CycRec I d} {x : α → I × RingSpace d β}
    (hρ : Measurable ρ) (hx : Measurable x) :
    MeasurableSet {a | x a ∈ (ρ a).region β} :=
  (hρ.prodMk hx) CycRec.measurableSet_region_all

/-! ### The least edge -/

theorem edgeEnc_injective : Function.Injective (edgeEnc (d := d)) :=
  (Encodable.ofCountable (Edge d)).encode_injective

theorem leastEdge_eq_some_iff {Q : Edge d → Prop} {e : Edge d} :
    leastEdge Q = some e ↔ Q e ∧ ∀ e', Q e' → edgeEnc e ≤ edgeEnc e' := by
  classical
  unfold leastEdge
  constructor
  · intro h
    split_ifs at h with hex
    cases h
    exact hex.choose_spec
  · intro h
    have hex : ∃ e, Q e ∧ ∀ e', Q e' → edgeEnc e ≤ edgeEnc e' := ⟨e, h⟩
    rw [dite_eq_left hex]
    exact congrArg some (edgeEnc_injective (le_antisymm (hex.choose_spec.2 e h.1)
      (h.2 _ hex.choose_spec.1)))

/-! ### Forced and fresh edges -/

section Events

variable {P : CycPlan I d β} {sc : ℝ≥0∞} {st : α → CycScheme.State I d}

theorem measurableSet_forcedEdge_eq {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) (e : Edge d) :
    MeasurableSet {a | CycScheme.forcedEdge P (st a) (CycScheme.sStar P sc (st a) (o a)) =
      some e} := by
  have hE := measurable_cur (P := P) hst
  have hρ : Measurable fun a => (st a).1 := measurable_fst.comp hst
  have hs := measurable_sStar (P := P) (sc := sc) hst ho
  have hclock : Measurable fun a => (CycScheme.cur P (st a)).data.clock β
      ((CycScheme.cur P (st a)).time + CycScheme.sStar P sc (st a) (o a)) :=
    measurable_clock.comp (hE.prodMk ((measurable_time.comp hE).add hs))
  have hQ : ∀ e' : Edge d, MeasurableSet {a | Edge.Mem (CycScheme.cur P (st a)).pos e' ∧
      ((CycScheme.cur P (st a)).data.copy, (e', (CycScheme.cur P (st a)).data.clock β
        ((CycScheme.cur P (st a)).time + CycScheme.sStar P sc (st a) (o a)))) ∈
          (st a).1.ringSet β} := by
    intro e'
    refine MeasurableSet.inter ?_ ?_
    · exact (measurable_pos.comp hE) (Set.to_countable {w : Fin d → ℤ | Edge.Mem w e'}).measurableSet
    · refine measurableSet_mem_ringSet P.junk hρ ?_
      exact (measurable_entry_copy.comp hE).prodMk (measurable_const.prodMk hclock)
  have : {a | CycScheme.forcedEdge P (st a) (CycScheme.sStar P sc (st a) (o a)) = some e} =
      {a | Edge.Mem (CycScheme.cur P (st a)).pos e ∧
      ((CycScheme.cur P (st a)).data.copy, (e, (CycScheme.cur P (st a)).data.clock β
        ((CycScheme.cur P (st a)).time + CycScheme.sStar P sc (st a) (o a)))) ∈
          (st a).1.ringSet β} ∩ ⋂ e' : Edge d, ({a | Edge.Mem (CycScheme.cur P (st a)).pos e' ∧
      ((CycScheme.cur P (st a)).data.copy, (e', (CycScheme.cur P (st a)).data.clock β
        ((CycScheme.cur P (st a)).time + CycScheme.sStar P sc (st a) (o a)))) ∈
          (st a).1.ringSet β}ᶜ ∪ {_a | edgeEnc e ≤ edgeEnc e'}) := by
    ext a
    simp only [CycScheme.forcedEdge, leastEdge_eq_some_iff, mem_ofPred_eq, mem_inter_iff,
      mem_iInter, mem_union, mem_compl_iff]
    refine and_congr Iff.rfl (forall_congr' fun e' => ?_)
    tauto
  rw [this]
  exact (hQ e).inter (MeasurableSet.iInter fun e' => (hQ e').compl.union (MeasurableSet.const _))

theorem freshEdge_eq_some_iff (st : CycScheme.State I d) (o : Outcome (CycS I d β)) (e : Edge d) :
    CycScheme.freshEdge P sc st o = some e ↔ ∃ x, (cycSeq I d β).atomMap o.2 = Sum.inl x ∧
      ((0 < o.1 ∧ o.1 ≤ (CycScheme.hOf P sc st : ℝ≥0∞) ∧ x.1 = (CycScheme.cur P st).data.copy ∧
        x.2.2 = (CycScheme.cur P st).data.clock β ((CycScheme.cur P st).time +
          CycScheme.sStar P sc st o) ∧ Edge.Mem (CycScheme.cur P st).pos x.2.1 ∧
        x ∉ st.1.region β) ∧ x.2.1 = e) := by
  classical
  unfold CycScheme.freshEdge
  rcases hY : (cycSeq I d β).atomMap o.2 with x | u
  · dsimp only
    split_ifs with hc
    · simp only [Option.some.injEq, Sum.inl.injEq]
      constructor
      · intro h; exact ⟨x, rfl, hc, h⟩
      · rintro ⟨y, rfl, _, h⟩; exact h
    · simp only [false_iff]
      rintro ⟨y, hxy, h, _⟩
      cases Sum.inl.inj hxy
      exact hc h
  · simp

theorem measurableSet_freshEdge_eq {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) (e : Edge d) :
    MeasurableSet {a | CycScheme.freshEdge P sc (st a) (o a) = some e} := by
  classical
  have hE := measurable_cur (P := P) hst
  have hρ : Measurable fun a => (st a).1 := measurable_fst.comp hst
  have hs := measurable_sStar (P := P) (sc := sc) hst ho
  have hY : Measurable fun a => (cycSeq I d β).atomMap (o a).2 :=
    (cycSeq I d β).measurable_atomMap.comp (measurable_snd.comp ho)
  have hclock : Measurable fun a => (CycScheme.cur P (st a)).data.clock β
      ((CycScheme.cur P (st a)).time + CycScheme.sStar P sc (st a) (o a)) :=
    measurable_clock.comp (hE.prodMk ((measurable_time.comp hE).add hs))
  have hC : MeasurableSet {p : α × CycS I d β |
      (0 < (o p.1).1 ∧ (o p.1).1 ≤ (CycScheme.hOf P sc (st p.1) : ℝ≥0∞) ∧
      p.2.1 = (CycScheme.cur P (st p.1)).data.copy ∧
      p.2.2.2 = (CycScheme.cur P (st p.1)).data.clock β
        ((CycScheme.cur P (st p.1)).time + CycScheme.sStar P sc (st p.1) (o p.1)) ∧
      Edge.Mem (CycScheme.cur P (st p.1)).pos p.2.2.1 ∧ p.2 ∉ (st p.1).1.region β) ∧
      p.2.2.1 = e} := by
    have h1 : MeasurableSet {p : α × CycS I d β | 0 < (o p.1).1} :=
      measurableSet_lt measurable_const ((measurable_fst.comp ho).comp measurable_fst)
    have h2 : MeasurableSet {p : α × CycS I d β |
        (o p.1).1 ≤ (CycScheme.hOf P sc (st p.1) : ℝ≥0∞)} :=
      measurableSet_le ((measurable_fst.comp ho).comp measurable_fst)
        (measurable_coe_nnreal_ennreal.comp ((measurable_hOf hst).comp measurable_fst))
    have h3 : MeasurableSet {p : α × CycS I d β |
        p.2.1 = (CycScheme.cur P (st p.1)).data.copy} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_snd)
        ((measurable_entry_copy.comp hE).comp measurable_fst)
    have h4 : MeasurableSet {p : α × CycS I d β | p.2.2.2 =
        (CycScheme.cur P (st p.1)).data.clock β
          ((CycScheme.cur P (st p.1)).time + CycScheme.sStar P sc (st p.1) (o p.1))} :=
      measurableSet_eq_fun (measurable_snd.comp (measurable_snd.comp measurable_snd))
        (hclock.comp measurable_fst)
    have h5 : MeasurableSet {p : α × CycS I d β |
        Edge.Mem (CycScheme.cur P (st p.1)).pos p.2.2.1} := by
      have : Measurable fun p : α × CycS I d β => ((CycScheme.cur P (st p.1)).pos, p.2.2.1) :=
        ((measurable_pos.comp hE).comp measurable_fst).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd))
      exact this (Set.to_countable {z : (Fin d → ℤ) × Edge d | Edge.Mem z.1 z.2}).measurableSet
    have h6 : MeasurableSet {p : α × CycS I d β | p.2 ∉ (st p.1).1.region β} :=
      (measurableSet_mem_region (ρ := fun p : α × CycS I d β => (st p.1).1)
        (x := fun p => p.2) (hρ.comp measurable_fst) measurable_snd).compl
    have h7 : MeasurableSet {p : α × CycS I d β | p.2.2.1 = e} :=
      (measurable_fst.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton e)
    exact (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6))))).inter h7
  have := measurableSet_atom_cond hY hC
  convert this using 1
  ext a
  simp only [freshEdge_eq_some_iff, mem_ofPred_eq]

open scoped Classical in
theorem newV_eq_iff (st : CycScheme.State I d) (o : Outcome (CycS I d β)) (z : Fin d → ℤ) :
    CycScheme.newV P sc st o = z ↔
      (∃ e, ((CycScheme.sStar P sc st o : ℝ≥0∞) = CycScheme.hFr β st.1 (CycScheme.cur P st) ∧
          CycScheme.forcedEdge P st (CycScheme.sStar P sc st o) = some e) ∧
        edgeOther (CycScheme.cur P st).pos e = z) ∨
      ((∀ e, ¬ ((CycScheme.sStar P sc st o : ℝ≥0∞) = CycScheme.hFr β st.1 (CycScheme.cur P st) ∧
          CycScheme.forcedEdge P st (CycScheme.sStar P sc st o) = some e)) ∧
        ((∃ e, CycScheme.freshEdge P sc st o = some e ∧ edgeOther (CycScheme.cur P st).pos e = z) ∨
          ((∀ e, CycScheme.freshEdge P sc st o ≠ some e) ∧ (CycScheme.cur P st).pos = z))) := by
  unfold CycScheme.newV
  by_cases hF : (CycScheme.sStar P sc st o : ℝ≥0∞) = CycScheme.hFr β st.1 (CycScheme.cur P st)
  · rcases hf : CycScheme.forcedEdge P st (CycScheme.sStar P sc st o) with _ | e1
    · rcases hr : CycScheme.freshEdge P sc st o with _ | e2 <;> simp [hF]
    · simp [hF]
  · rcases hr : CycScheme.freshEdge P sc st o with _ | e2 <;> simp [hF]

variable (P sc) in
theorem measurable_newV {o : α → Outcome (CycS I d β)} (hst : Measurable st)
    (ho : Measurable o) : Measurable fun a => CycScheme.newV P sc (st a) (o a) := by
  refine measurable_to_countable' fun z => ?_
  have hE := measurable_cur (P := P) hst
  have hρ : Measurable fun a => (st a).1 := measurable_fst.comp hst
  have hs := measurable_sStar (P := P) (sc := sc) hst ho
  have hFc : MeasurableSet {a | (CycScheme.sStar P sc (st a) (o a) : ℝ≥0∞) =
      CycScheme.hFr β (st a).1 (CycScheme.cur P (st a))} :=
    measurableSet_eq_fun (measurable_coe_nnreal_ennreal.comp hs) (measurable_hFr hρ hE)
  have hW : ∀ e : Edge d, MeasurableSet {a | edgeOther (CycScheme.cur P (st a)).pos e = z} :=
    fun e => (measurable_pos.comp hE)
      (Set.to_countable {w : Fin d → ℤ | edgeOther w e = z}).measurableSet
  have hP : MeasurableSet {a | (CycScheme.cur P (st a)).pos = z} :=
    (measurable_pos.comp hE) (measurableSet_singleton z)
  have hSF : ∀ e : Edge d, MeasurableSet {a | (CycScheme.sStar P sc (st a) (o a) : ℝ≥0∞) =
      CycScheme.hFr β (st a).1 (CycScheme.cur P (st a)) ∧
      CycScheme.forcedEdge P (st a) (CycScheme.sStar P sc (st a) (o a)) = some e} :=
    fun e => hFc.inter (measurableSet_forcedEdge_eq hst ho e)
  have hSR := measurableSet_freshEdge_eq (P := P) (sc := sc) hst ho
  have : (fun a => CycScheme.newV P sc (st a) (o a)) ⁻¹' {z} =
      (⋃ e : Edge d, {a | (CycScheme.sStar P sc (st a) (o a) : ℝ≥0∞) =
        CycScheme.hFr β (st a).1 (CycScheme.cur P (st a)) ∧
        CycScheme.forcedEdge P (st a) (CycScheme.sStar P sc (st a) (o a)) = some e} ∩
        {a | edgeOther (CycScheme.cur P (st a)).pos e = z}) ∪
      ((⋂ e : Edge d, {a | (CycScheme.sStar P sc (st a) (o a) : ℝ≥0∞) =
        CycScheme.hFr β (st a).1 (CycScheme.cur P (st a)) ∧
        CycScheme.forcedEdge P (st a) (CycScheme.sStar P sc (st a) (o a)) = some e}ᶜ) ∩
      ((⋃ e : Edge d, {a | CycScheme.freshEdge P sc (st a) (o a) = some e} ∩
        {a | edgeOther (CycScheme.cur P (st a)).pos e = z}) ∪
      ((⋂ e : Edge d, {a | CycScheme.freshEdge P sc (st a) (o a) = some e}ᶜ) ∩
        {a | (CycScheme.cur P (st a)).pos = z}))) := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, newV_eq_iff, mem_union, mem_iUnion, mem_inter_iff,
      mem_ofPred_eq, mem_iInter, mem_compl_iff, ne_eq]
  rw [this]
  exact (MeasurableSet.iUnion fun e => (hSF e).inter (hW e)).union
    ((MeasurableSet.iInter fun e => (hSF e).compl).inter
      ((MeasurableSet.iUnion fun e => (hSR e).inter (hW e)).union
        ((MeasurableSet.iInter fun e => (hSR e).compl).inter hP)))

end Events

end ElboimSly.Cyclic

end
