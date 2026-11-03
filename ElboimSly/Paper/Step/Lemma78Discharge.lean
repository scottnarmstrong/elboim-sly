/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Adapt
public import ElboimSly.Paper.Step.Lemma78CoupleMain
public import Mathlib

/-!
# W_2 after zeta_i, given ℱ^+_zeta_i with the typing data discharged

Measurability (stopping times), w_2 after zeta_i, given ℱ^+_zeta_i.

* `step78_isStoppingTime_T`: if `Z` is an `(ℱ⁺_t)`-stopping time then `t'_n + Z` is a stopping time
  of the exploration filtration `(ℱ^{𝔭₈}_s)`.
* `step78_measurable_delta`: the walk datum `(1, W₂(ζ), q + ζ, +1)` is `ℱ_T`-measurable
  (paths (c)).
* `step78_couple_zeta`: w_2 after zeta_i, given ℱ^+_zeta_i for `Z = ζ_i`, with no stopping-time or measurability
  hypothesis; the standing data are `1 ≤ d`, `1 < β` (the regime) and the independence structure of
  Plan-level coupling after a stopping time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS Unit d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr) (h𝒢 : 𝒢₀ ≤ mΩ)

theorem measurable_fn_at_aux {α V : Type*} {m : MeasurableSpace α} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (P : α → CPath V) (hP : Measurable P) (g : α → ℝ≥0) (hg : Measurable g) :
    Measurable fun a => (P a).fn (g a) :=
  measurable_fn_at P hP g hg

theorem measurable_ite_aux {α γ : Type*} {m : MeasurableSpace α} [MeasurableSpace γ]
    {p : α → Prop} [DecidablePred p] {f g : α → γ} (hp : MeasurableSet {a | p a})
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => if p x then f x else g x :=
  Measurable.ite hp hf hg

/-- A stopping time of `(ℱ⁺_t)` shifted by `t'_n` is a stopping time of `(ℱ^{𝔭₈}_s)`. -/
theorem step78_isStoppingTime_T {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) :
    IsStoppingTime (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr)
      (step78T Tn Z) := by
  intro s
  by_cases hs : Tn ≤ s
  · have e : {ω | step78T Tn Z ω ≤ (s : WithTop ℝ≥0)} =
        {ω | Z ω ≤ ((s - Tn : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, step78T]
      cases hz : Z ω with
      | top =>
        rw [WithTop.add_top]
        exact ⟨fun h => absurd h (WithTop.not_top_le_coe _),
          fun h => absurd h (WithTop.not_top_le_coe _)⟩
      | coe a =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, le_tsub_iff_left hs]
    rw [e]
    have h := hZ (s - Tn)
    exact (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr).mono
      (le_of_eq (add_tsub_cancel_of_le hs)) _ h
  · have e : {ω | step78T Tn Z ω ≤ (s : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      refine lt_of_lt_of_le ?_ (le_add_of_nonneg_right bot_le)
      exact WithTop.coe_lt_coe.2 (not_le.1 hs)
    rw [e]
    exact @MeasurableSet.empty _ (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr s)

/-- The walk datum `δ = (1, W₂(ζ), q + ζ, +1)` is `ℱ_T`-measurable. -/
theorem step78_measurable_delta {Z : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr)
      (step78T Tn Z)) :
    Measurable[hT.measurableSpace] (step78Delta N u q Z) := by
  classical
  set P := step78Plan d β u q Tn with hP
  have hRf : ∀ s, Measurable[cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr s]
      fun ω => CycRec.trunc s (P.envFinal (cycNgood N ω)) :=
    measurable_trunc_multiFilt P 𝒢₀ h𝒢 Pr (measurable_envFinal_cycNgood P hN.measurable)
  have hrec := measurable_cycRecStop hRf hT
  have hsr : Measurable[hT.measurableSpace] (ElboimSly.SRW.stopReal (step78T Tn Z)) :=
    measurable_stopReal_stop hT
  have hζ : Measurable[hT.measurableSpace] (fun ω => ElboimSly.SRW.stopReal Z ω) := by
    have e : (fun ω => ElboimSly.SRW.stopReal Z ω) =
        fun ω => ElboimSly.SRW.stopReal (step78T Tn Z) ω - Tn := by
      funext ω
      simp only [ElboimSly.SRW.stopReal, step78T]
      cases hz : Z ω with
      | top => rw [WithTop.add_top]; simp
      | coe a =>
        show a = (Tn + a) - Tn
        exact (add_tsub_cancel_left Tn a).symm
    rw [e]
    exact hsr.sub_const _
  have hne : MeasurableSet[hT.measurableSpace] {ω | step78T Tn Z ω ≠ ⊤} :=
    measurableSet_ne_top hT
  have hG : Measurable[hT.measurableSpace] fun ω =>
      ((cycRecStop P (cycNgood N) (step78T Tn Z) ω).coord P.junk 1).path.fn
        (ElboimSly.SRW.stopReal Z ω) :=
    measurable_fn_at_aux (m := hT.measurableSpace)
      (fun ω => ((cycRecStop P (cycNgood N) (step78T Tn Z) ω).coord P.junk 1).path)
      (measurable_entry_path.comp ((CycRec.measurable_coord P.junk 1).comp hrec)) _ hζ
  have hW : Measurable[hT.measurableSpace] fun ω =>
      ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) u q (ElboimSly.SRW.stopReal Z ω : ℝ) := by
    have e : (fun ω => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) u q
        (ElboimSly.SRW.stopReal Z ω : ℝ)) = fun ω =>
        if step78T Tn Z ω ≠ ⊤ then
          ((cycRecStop P (cycNgood N) (step78T Tn Z) ω).coord P.junk 1).path.fn
            (ElboimSly.SRW.stopReal Z ω) else u := by
      funext ω
      by_cases hZ : Z ω = ⊤
      · have h1 : step78T Tn Z ω = ⊤ := by unfold step78T; rw [hZ]; exact WithTop.add_top _
        have h2 : ElboimSly.SRW.stopReal Z ω = 0 := by
          unfold ElboimSly.SRW.stopReal; rw [hZ]; rfl
        rw [ite_eq_right (by simp [h1]), h2]
        simpa using cycWalk_zero ((cycGood_cycNgood N ω) ()) u q
      · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hZ
        have hT' : step78T Tn Z ω = ((Tn + a : ℝ≥0) : WithTop ℝ≥0) := by
          unfold step78T; rw [← ha]; rfl
        have h1 : step78T Tn Z ω ≠ ⊤ := by rw [hT']; exact WithTop.coe_ne_top
        rw [ite_eq_left h1]
        have hs : ElboimSly.SRW.stopReal Z ω = a := by
          unfold ElboimSly.SRW.stopReal; rw [← ha]; rfl
        have hs2 : ElboimSly.SRW.stopReal (step78T Tn Z) ω = Tn + a := by
          unfold ElboimSly.SRW.stopReal; rw [hT']; rfl
        simp only [cycRecStop, hs, hs2]
        exact (step78_trunc_coord_one u q Tn (cycGood_cycNgood N ω) _ a).symm
    rw [e]
    exact measurable_ite_aux (m := hT.measurableSpace) hne hG measurable_const
  unfold step78Delta step78Datum
  exact measurable_const.prodMk (hW.prodMk ((measurable_const.add hζ.coe_nnreal_real).prodMk
    measurable_const))

end ElboimSly.Paper.Step

end
