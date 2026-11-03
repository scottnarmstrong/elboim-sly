/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.NaturalCouplingLaw
public import ElboimSly.Paper.Step.CfAe
public import ElboimSly.Foundations.SRW.StrongMarkovMain
public import Mathlib

/-!
# The driving filtration, the driven walk at stopping times

The driven regenerated walk (a), ES22 Lemma 4.1 (independence).

For an admissible filtration `F` of an SRW `Y` and an offset `a`:
* `stepShiftFilt hF a` is `𝒢_t = F (a + t)`; `stepShiftStop a S = S + a` turns a `𝒢`-stopping
  time into an `F`-stopping time, and `𝒢_S ≤ F_{S + a}`;
* `measurable_stepReg_adapted`: `W = W_reg^{θ_a Y}` is `𝒢`-adapted;
* `stepReg_strong_markov`: the strong Markov law of the driven walk at a stopping time.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

theorem measurable_regenFrom_comp' {Ω' : Type*} [MeasurableSpace Ω'] {d : ℕ} {b : ℝ≥0}
    (hb : 0 < b) {f : Ω' → PathSpace d} (hreg : ∀ ω, IsRegPath (f ω)) (hf : Measurable f)
    (s : ℝ≥0) : Measurable fun ω => drivenRegenFrom b (f ω) s := by
  have h2 : Measurable fun ω => (⟨f ω, hreg ω⟩ : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}) :=
    hf.subtype_mk
  have h3 := measurable_drivenRegenFrom_subtype (d := d) hb s
  have h4 := h3.comp h2
  exact h4

theorem measurable_pi_of' {Ω' : Type*} [MeasurableSpace Ω'] {d : ℕ} (f : Ω' → PathSpace d)
    (h : ∀ v, Measurable fun ω => f ω v) : Measurable f :=
  measurable_pi_iff.2 h

theorem measurable_sub_of'{Ω' : Type*} [MeasurableSpace Ω'] {d : ℕ} {f g : Ω' → Fin d → ℤ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω - g ω :=
  hf.sub hg

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

/-- `𝒢_t = F_{a + t}`. -/
def stepShiftFilt (hF : IsAdmissible P Y F) (a : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq t := F (a + t)
  mono' _ _ h := hF.mono (add_le_add_right h a)
  le' _t := hF.le _

/-- A `𝒢`-stopping time `S` gives the `F`-stopping time `S + a`. -/
def stepShiftStop (a : ℝ≥0) (S : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => S ω + ((a : ℝ≥0) : WithTop ℝ≥0)

omit mΩ in
theorem stepShiftStop_le_iff (a : ℝ≥0) (S : Ω → WithTop ℝ≥0) (ω : Ω) (j : ℝ≥0) :
    stepShiftStop a S ω ≤ WithTop.some j ↔ a ≤ j ∧ S ω ≤ WithTop.some (j - a) := by
  unfold stepShiftStop
  cases hS : S ω using WithTop.recTopCoe with
  | top =>
    have h1 : (⊤ : WithTop ℝ≥0) + ((a : ℝ≥0) : WithTop ℝ≥0) = ⊤ := WithTop.top_add _
    have h2 : ∀ x : ℝ≥0, ¬ (⊤ : WithTop ℝ≥0) ≤ WithTop.some x := fun x h =>
      WithTop.coe_ne_top (top_le_iff.1 h)
    rw [h1]
    exact ⟨fun h => absurd h (h2 j), fun h => absurd h.2 (h2 _)⟩
  | coe s =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    constructor
    · intro h
      have ha : a ≤ j := le_trans le_add_self h
      exact ⟨ha, by rw [le_tsub_iff_right ha]; exact h⟩
    · rintro ⟨h1, h2⟩
      rwa [le_tsub_iff_right h1] at h2

omit mΩ in
theorem stepShiftStop_set (a : ℝ≥0) (S : Ω → WithTop ℝ≥0) (j : ℝ≥0) :
    {ω | stepShiftStop a S ω ≤ WithTop.some j} =
      if a ≤ j then {ω | S ω ≤ WithTop.some (j - a)} else ∅ := by
  ext ω
  have := stepShiftStop_le_iff a S ω j
  split_ifs with h
  · exact ⟨fun hh => (this.1 hh).2, fun hh => this.2 ⟨h, hh⟩⟩
  · exact ⟨fun hh => absurd (this.1 hh).1 h, fun hh => hh.elim⟩

theorem isStoppingTime_stepShiftStop (hF : IsAdmissible P Y F) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) :
    IsStoppingTime hF.filtration (stepShiftStop a S) := by
  intro j
  show MeasurableSet[F j] {ω | stepShiftStop a S ω ≤ WithTop.some j}
  rw [stepShiftStop_set]
  split_ifs with h
  · have := hS (j - a)
    have e : a + (j - a) = j := add_tsub_cancel_of_le h
    have h' : MeasurableSet[F (a + (j - a))] {ω | S ω ≤ WithTop.some (j - a)} := this
    rwa [e] at h'
  · exact @MeasurableSet.empty _ (F j)

theorem measurableSet_stepShiftStop (hF : IsAdmissible P Y F) (a : ℝ≥0) {S : Ω → WithTop ℝ≥0}
    (hS : IsStoppingTime (stepShiftFilt hF a) S) {A : Set Ω}
    (hA : MeasurableSet[hS.measurableSpace] A) :
    MeasurableSet[(isStoppingTime_stepShiftStop hF a hS).measurableSpace] A := by
  refine ⟨(iSup_le fun t => le_iSup (fun t => (hF.filtration : Filtration ℝ≥0 mΩ) t) (a + t))
    A hA.1, fun j => ?_⟩
  have h1 := hA.2 (j - a)
  show MeasurableSet[F j] (A ∩ {ω | stepShiftStop a S ω ≤ WithTop.some j})
  rw [stepShiftStop_set]
  split_ifs with h
  · have e' : a + (j - a) = j := add_tsub_cancel_of_le h
    have h1' : MeasurableSet[F (a + (j - a))] (A ∩ {ω | S ω ≤ WithTop.some (j - a)}) := h1
    rwa [e'] at h1'
  · simp only [inter_empty]
    exact @MeasurableSet.empty _ (F j)

/-- `W = W_reg^{θ_a Y}` is adapted to `𝒢_t = F_{a+t}`. -/
theorem measurable_stepReg_adapted {β : ℝ} [Fact (0 < β)] (hF : IsAdmissible P Y F)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a s : ℝ≥0) :
    Measurable[F (a + s)] fun ω => stepReg β (stepShift a (Y ω)) s := by
  have hcoord : ∀ v : ℝ≥0, Measurable[F (a + s)] fun ω => stepWin a s (Y ω) v := fun v =>
    @measurable_sub_of' Ω (F (a + s)) d _ _
      (hF.adapted _ _ (add_le_add_right (min_le_right v s) a)) (hF.adapted _ _ le_self_add)
  have hpi : Measurable[F (a + s)] fun ω => stepWin a s (Y ω) :=
    @measurable_pi_of' Ω (F (a + s)) d (fun ω => stepWin a s (Y ω)) hcoord
  have h : Measurable[F (a + s)] fun ω => drivenRegenFrom β.toNNReal (stepWin a s (Y ω)) s :=
    @measurable_regenFrom_comp' Ω (F (a + s)) d _ toNNReal_pos' _
      (fun ω => (isDrivingPath_stepWin (hYp ω) a s).toIsRegPath) hpi s
  have heq : (fun ω => stepReg β (stepShift a (Y ω)) s) =
      fun ω => drivenRegenFrom β.toNNReal (stepWin a s (Y ω)) s := by
    funext ω
    have hx : IsDrivingPath (shiftPath (Y ω) a) := isDrivingPath_shiftPath (hYp ω) a
    have hxy : ∀ v ≤ s, shiftPath (Y ω) a v = stepWin a s (Y ω) v := by
      intro v hv
      simp only [stepWin, SRW.stopPath, SRW.theta, shiftPath, min_eq_left hv]
    exact drivenRegenFrom_causal toNNReal_pos' hx (isDrivingPath_stepWin (hYp ω) a s) hxy le_rfl
  rw [heq]
  exact h

end ElboimSly.Paper.Step
