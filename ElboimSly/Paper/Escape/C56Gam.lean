/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Tube
public import ElboimSly.Paper.Escape.C56Rel
public import Mathlib

/-!
# The joint events `E^a ∩ E^d` as a measurable set of `(parameters, path)`

ES22 Claim 5.6, phase `i`.  The parameters are the start `x = W_v(T)` and the time
`a' = T = ζ_{i-1}`; the path is the coupled walk `W̃`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ}

/-- The parametric tube set. -/
def tubeFam (F : ℝ → ℝ → Fin (k + 2) → ℝ) (Tf : ℝ → ℝ) (R R' : ℝ) :
    Set (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) :=
  {z | z.2 ∈ tubeRat z.1.1 (F z.1.2) R R' (Tf z.1.2)}

theorem measurable_normEval (F : ℝ → ℝ → Fin (k + 2) → ℝ)
    (hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) {r : ℝ → ℝ} (hr : Measurable r) :
    Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) =>
      ‖escCast (z.1.1 + z.2.fn (r z.1.2).toNNReal) - F z.1.2 (r z.1.2)‖) := by
  have hh : Measurable (fun p : ℝ × ((Fin (k + 2) → ℤ) × (Fin (k + 2) → ℤ)) =>
      ‖escCast (p.2.1 + p.2.2) - F p.1 (r p.1)‖) := by
    have h1 : Measurable (fun a : ℝ => F a (r a)) := hF.comp (measurable_id.prodMk hr)
    let g : ((Fin (k + 2) → ℤ) × (Fin (k + 2) → ℤ)) → ℝ → ℝ :=
      fun xy a => ‖escCast (xy.1 + xy.2) - F a (r a)‖
    have hg : ∀ xy, Measurable (g xy) := fun xy => (measurable_const.sub h1).norm
    exact measurable_from_prod_countable_left
      (f := fun p : ℝ × ((Fin (k + 2) → ℤ) × (Fin (k + 2) → ℤ)) => g p.2 p.1) hg
  have h1 : Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have h2 : Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have h3 : Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) =>
      z.2.fn (r z.1.2).toNNReal) := by
    have := measurable_fn_at (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) => z.2)
      measurable_snd (fun z => (r z.1.2).toNNReal) ((hr.comp h1).real_toNNReal)
    exact this
  have hφ := h1.prodMk (h2.prodMk h3)
  have hc := hh.comp hφ
  convert hc using 1
  funext z
  rfl

theorem measurableSet_tubeFam (F : ℝ → ℝ → Fin (k + 2) → ℝ)
    (hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) {Tf : ℝ → ℝ} (hT : Measurable Tf)
    (R R' : ℝ) : MeasurableSet (tubeFam (k := k) F Tf R R') := by
  have hq : ∀ (q : ℚ) (c : ℝ) (cond : ℝ → Prop), MeasurableSet {a : ℝ | cond a} →
      MeasurableSet {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
        cond z.1.2 → ‖escCast (z.1.1 + z.2.fn (q : ℝ).toNNReal) - F z.1.2 q‖ ≤ c} := by
    intro q c cond hcond
    have h1 := measurable_normEval F hF (r := fun _ => (q : ℝ)) measurable_const
    have h2 : MeasurableSet {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
        ‖escCast (z.1.1 + z.2.fn (q : ℝ).toNNReal) - F z.1.2 q‖ ≤ c} :=
      measurableSet_le h1 measurable_const
    have h3 : MeasurableSet {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
        cond z.1.2} := (measurable_snd.comp measurable_fst) hcond
    exact (h3.compl.union h2).congr (by ext z; simp only [mem_union, mem_compl_iff, mem_ofPred_eq]; tauto)
  have hend : ∀ c : ℝ, MeasurableSet {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
      ‖escCast (z.1.1 + z.2.fn (Tf z.1.2).toNNReal) - F z.1.2 (Tf z.1.2)‖ ≤ c} := fun c =>
    measurableSet_le (measurable_normEval F hF hT) measurable_const
  have e : tubeFam (k := k) F Tf R R' =
      (⋂ q : ℚ, {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
        (0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Tf z.1.2) →
          ‖escCast (z.1.1 + z.2.fn (q : ℝ).toNNReal) - F z.1.2 q‖ ≤ R}) ∩
      ({z | ‖escCast (z.1.1 + z.2.fn (Tf z.1.2).toNNReal) - F z.1.2 (Tf z.1.2)‖ ≤ R} ∩
      ((⋂ q : ℚ, {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
        (Tf z.1.2 / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Tf z.1.2) →
          ‖escCast (z.1.1 + z.2.fn (q : ℝ).toNNReal) - F z.1.2 q‖ ≤ R'}) ∩
      {z | ‖escCast (z.1.1 + z.2.fn (Tf z.1.2).toNNReal) - F z.1.2 (Tf z.1.2)‖ ≤ R'})) := by
    ext z
    simp only [tubeFam, tubeRat, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_imp]
  rw [e]
  refine MeasurableSet.inter
    (MeasurableSet.iInter fun q => hq q R (fun a => 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Tf a) ?_)
    (MeasurableSet.inter (hend R) (MeasurableSet.inter
      (MeasurableSet.iInter fun q => hq q R' (fun a => Tf a / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ Tf a) ?_)
      (hend R')))
  · by_cases h : 0 ≤ (q : ℝ)
    · simp only [h, true_and]; exact measurableSet_le measurable_const hT
    · simp [h]
  · exact (measurableSet_le (hT.div_const 2) measurable_const).inter
      (measurableSet_le measurable_const hT)

/-- The parametric set `E^d`: the horizon is `Tf a'`. -/
def relFam (β : ℝ) (Tf : ℝ → ℝ) :
    Set (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) :=
  {z | z.2 ∈ relPathSet β (Tf z.1.2)}

theorem measurable_scaleIndex : Measurable (fun T : ℝ => (scaleIndex T : ℝ)) := by
  have h : Measurable (fun T : ℝ => scaleIndex T) := by
    unfold scaleIndex
    have h1 : Measurable (fun T : ℝ => ⌈Real.logb 4 T⌉₊) :=
      Nat.measurable_ceil.comp (Real.measurable_log.div_const (Real.log 4))
    exact (measurable_of_countable (fun n : ℕ => n - 1)).comp h1
  exact measurable_from_nat.comp h

theorem measurableSet_relFam {β : ℝ} (hβ : 0 < β) {Tf : ℝ → ℝ} (hT : Measurable Tf) :
    MeasurableSet (relFam (k := k) β Tf) := by
  have : Fact (0 < β) := ⟨hβ⟩
  have h1 : Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hTz : Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) => Tf z.1.2) :=
    hT.comp h1
  -- closing times
  have hclose : MeasurableSet {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
      closesBy β (Tf z.1.2) z.2} := by
    have e : {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
        closesBy β (Tf z.1.2) z.2} = ⋃ i : ℕ,
        ({z | 1 ≤ i ∧ i ≤ ⌊Tf z.1.2 / β⌋₊} ∩ {z | z.2.fn (((i : ℝ) * β).toNNReal) = 0}) := by
      ext z; simp [closesBy, and_assoc]
    rw [e]
    refine MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ ?_
    · by_cases hi : 1 ≤ i
      · simp only [hi, true_and]
        exact measurableSet_le measurable_const (Nat.measurable_floor.comp (hTz.div_const β))
      · simp [hi]
    · exact (measurable_snd (CPath.measurable_eval _ (measurableSet_singleton _)))
  -- relaxed measure
  have hw : Measurable fun p : (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) × ℝ =>
      cpR p.1.2 p.2 :=
    measurable_fn_at (fun p : (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) × ℝ => p.1.2)
      (measurable_snd.comp measurable_fst) _ measurable_snd.real_toNNReal
  have key := measurableSet_isRelaxedTimeWrt (β := β)
    (Ω := ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ))
    (fun z r => cpR z.2 r) (fun _ _ => 0) hw measurable_const (fun z s => cpRc z.2 s)
  have hS : MeasurableSet {p : (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) × ℝ |
      p.2 ∈ Icc 0 (Tf p.1.1.2) ∧ IsRelaxedTimeWrt β (cpR p.1.2) 0 p.2} := by
    have hI : MeasurableSet {p : (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) × ℝ |
        p.2 ∈ Icc 0 (Tf p.1.1.2)} := by
      have a1 : MeasurableSet {p : (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) × ℝ |
          0 ≤ p.2} := measurableSet_le measurable_const measurable_snd
      have a2 : MeasurableSet {p : (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) × ℝ |
          p.2 ≤ Tf p.1.1.2} :=
        measurableSet_le measurable_snd (hT.comp (measurable_snd.comp (measurable_fst.comp
          measurable_fst)))
      exact a1.inter a2
    exact hI.inter key
  have hvol := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hS
  have hc : Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) =>
      ENNReal.ofReal ((9 / 10 + 1 / (scaleIndex (Tf z.1.2) : ℝ)) * Tf z.1.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have : Measurable (fun z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) =>
        (scaleIndex (Tf z.1.2) : ℝ)) := measurable_scaleIndex.comp hTz
    exact ((measurable_const.add (measurable_const.div this))).mul hTz
  have hrel : MeasurableSet {z : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
      relMeasureOK β (Tf z.1.2) z.2} := measurableSet_le hc hvol
  exact hclose.union hrel

end ElboimSly.Paper.Escape

end
