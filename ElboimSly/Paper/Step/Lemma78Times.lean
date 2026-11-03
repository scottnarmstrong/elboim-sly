/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Stop

/-!
# Measurability of the times of Lemma 7.8

Measurability, first sentence: `ζ_i, ζ''_i, ζ'_i` are stopping times of the
filtration `f` (= `(ℱ⁺_t)`) once `W₂` is adapted and right-continuous with finitely many events,
and `V` is `ℱ⁺_0`-measurable (as a countable family of events `{x ∈ V}`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- The standing structural hypotheses on the frame `(f, W₂, V)` of Lemma 7.8. -/
structure Step78Frame (D : Step78Data d Ω) (f : Filtration ℝ≥0 m) : Prop where
  hd : 1 ≤ d
  hβ : 1 < D.β
  hw : ∀ t, Measurable[f t] (D.w t)
  hrc : ∀ ω t, ∀ᶠ u in 𝓝[≥] t, D.w u ω = D.w t ω
  hfin : ∀ ω, StepEventsFiniteW (stepExt fun s => D.w s ω) (fun _ => ((0 : ℝ≥0) : ℝ))
  hV : ∀ x, MeasurableSet[f 0] {ω | x ∈ D.V ω}

namespace Step78Data

variable {D : Step78Data d Ω} {f : Filtration ℝ≥0 m}

theorem path_coe (ω : Ω) (t : ℝ≥0) : D.path ω (t : ℝ) = D.w t ω := by
  simp [Step78Data.path, stepExt]

theorem measurableSet_exists_mem (hF : Step78Frame D f) (t : ℝ≥0)
    (Q : (Fin d → ℤ) → (Fin d → ℤ) → Prop) :
    MeasurableSet[f t] {ω | ∃ v ∈ D.V ω, Q (D.w t ω) v} := by
  have : {ω | ∃ v ∈ D.V ω, Q (D.w t ω) v} =
      ⋃ x : Fin d → ℤ, {ω | x ∈ D.V ω} ∩ (D.w t ⁻¹' {y | Q y x}) := by
    ext ω; simp
  rw [this]
  refine MeasurableSet.iUnion fun x => ?_
  refine (f.mono (bot_le : (0 : ℝ≥0) ≤ t) _ (hF.hV x)).inter ?_
  exact hF.hw t (Set.Countable.measurableSet (Set.to_countable _))

theorem measurable_near2 (hF : Step78Frame D f) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | (t : ℝ) ∈ D.nearSet2 ω} := by
  have := measurableSet_exists_mem hF t (fun y v => ‖y - v‖ ≤ (19 / 10 : ℝ) ^ D.n)
  convert this using 2
  ext ω
  simp [Step78Data.nearSet2, path_coe]

theorem measurable_near1 (hF : Step78Frame D f) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | (t : ℝ) ∈ D.nearSet1 ω} := by
  have := measurableSet_exists_mem hF t (fun y v => ‖y - v‖ ≤ 1)
  convert this using 2
  ext ω
  simp [Step78Data.nearSet1, path_coe]

theorem measurable_far (hF : Step78Frame D f) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | (t : ℝ) ∈ D.farSet ω} := by
  have h1 := measurableSet_stepRelaxed_adapted (by linarith [hF.hβ]) f D.w (fun _ _ => 0)
    hF.hw hF.hrc (fun _ => measurable_const) t
  have h2 := (measurableSet_exists_mem hF t (fun y v => ‖y - v‖ < D.ρ)).compl
  have : {ω | (t : ℝ) ∈ D.farSet ω} =
      {ω | IsRelaxedTimeWrt D.β (stepExt fun s => D.w s ω) (((fun _ _ => (0 : ℝ≥0)) t ω : ℝ≥0) : ℝ)
          t} ∩ {ω | ∃ v ∈ D.V ω, ‖D.w t ω - v‖ < D.ρ}ᶜ := by
    ext ω
    simp [Step78Data.farSet, Step78Data.relaxed, stepRelaxedSetOf, stepRelaxedSet, path_coe,
      not_exists, not_lt]
  rw [this]
  exact h1.inter h2

theorem locIco_near2 (hF : Step78Frame D f) (ω : Ω) : IsLocIco (D.nearSet2 ω) :=
  isLocIco_path_pred (hF.hfin ω) (fun y => ∃ v ∈ D.V ω, ‖y - v‖ ≤ (19 / 10 : ℝ) ^ D.n)

theorem locIco_near1 (hF : Step78Frame D f) (ω : Ω) : IsLocIco (D.nearSet1 ω) :=
  isLocIco_path_pred (hF.hfin ω) (fun y => ∃ v ∈ D.V ω, ‖y - v‖ ≤ 1)

theorem locIco_far (hF : Step78Frame D f) (ω : Ω) : IsLocIco (D.farSet ω) := by
  have h1 : IsLocIco (D.relaxed ω) :=
    isLocIco_stepRelaxedSet' hF.hd hF.hβ (hF.hfin ω)
  have h2 := isLocIco_path_pred (hF.hfin ω) (fun y => ∀ v ∈ D.V ω, D.ρ ≤ ‖y - v‖)
  exact h1.inter h2

theorem treg_le_iff (hF : Step78Frame D f) (ω : Ω) (t : ℝ≥0) :
    D.treg ω ≤ t ↔ ∃ m : ℕ, 1 ≤ m ∧ ((m : ℝ) * D.β).toNNReal ≤ t ∧
      D.w ((m : ℝ) * D.β).toNNReal ω = D.u := by
  have hβ0 : 0 < D.β := by linarith [hF.hβ]
  constructor
  · intro h
    have hex : ∃ m : ℕ, 1 ≤ m ∧ D.w ((m : ℝ) * D.β).toNNReal ω = D.u := by
      by_contra hno
      have : D.treg ω = ⊤ := by
        simp only [Step78Data.treg, iInf_eq_top]
        intro m hm
        exact absurd ⟨m, hm⟩ hno
      rw [this] at h
      exact absurd h (WithTop.not_top_le_coe _)
    classical
    let m₀ := Nat.find hex
    have hm₀ : 1 ≤ m₀ ∧ D.w ((m₀ : ℝ) * D.β).toNNReal ω = D.u := Nat.find_spec hex
    refine ⟨m₀, hm₀.1, ?_, hm₀.2⟩
    refine WithTop.coe_le_coe.1 (le_trans ?_ h)
    refine le_iInf₂ fun m hm => ?_
    have hle : m₀ ≤ m := Nat.find_min' hex hm
    refine WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal ?_)
    have : (m₀ : ℝ) ≤ m := by exact_mod_cast hle
    nlinarith
  · rintro ⟨m, hm1, hmt, hmw⟩
    exact le_trans (iInf₂_le m ⟨hm1, hmw⟩) (WithTop.coe_le_coe.2 hmt)

theorem isStoppingTime_treg (hF : Step78Frame D f) : IsStoppingTime f D.treg := by
  intro t
  have : {ω | D.treg ω ≤ t} = ⋃ m : ℕ, ⋃ (_ : 1 ≤ m ∧ ((m : ℝ) * D.β).toNNReal ≤ t),
      {ω | D.w ((m : ℝ) * D.β).toNNReal ω = D.u} := by
    ext ω
    simp only [mem_ofPred_eq, treg_le_iff hF, mem_iUnion, exists_prop]
    tauto
  rw [this]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun hm => ?_
  refine f.mono hm.2 _ ?_
  exact hF.hw _ (Set.Countable.measurableSet (Set.to_countable ({D.u} : Set (Fin d → ℤ))))

theorem isStoppingTime_thit (hF : Step78Frame D f) {R : Ω → WithTop ℝ≥0}
    (hR : IsStoppingTime f R) : IsStoppingTime f (D.thit R) :=
  isStoppingTime_stepThit' hF.hβ f D.w (fun _ _ => 0) hF.hw (fun _ => measurable_const)
    hF.hfin hR

theorem isStoppingTime_nextZeta (hF : Step78Frame D f) {R : Ω → WithTop ℝ≥0}
    (hR : IsStoppingTime f R) : IsStoppingTime f (D.nextZeta R) :=
  (isStoppingTime_const f D.T).min
    (isStoppingTime_step78FirstGe f (measurable_far hF) (locIco_far hF) hR)

theorem isStoppingTime_zetaP' (hF : Step78Frame D f) {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime f Z) : IsStoppingTime f (D.zetaP' Z) := by
  refine hZ.max ((isStoppingTime_const f D.T).min ?_)
  refine ((isStoppingTime_thit hF hZ).min (isStoppingTime_treg hF)).min ?_
  exact (isStoppingTime_step78FirstGe f (measurable_near1 hF) (locIco_near1 hF) hZ).min
    (isStoppingTime_step78FirstGe f (measurable_near2 hF) (locIco_near2 hF)
      (isStoppingTime_add_nnreal f hZ D.gap))

/-- Measurability: `ζ'_i` and `ζ_i` are stopping times. -/
theorem isStoppingTime_zp_zeta (hF : Step78Frame D f) (i : ℕ) :
    IsStoppingTime f (D.zp i) ∧ IsStoppingTime f (D.zeta i) := by
  have hzp : ∀ i, IsStoppingTime f (D.zp i) := by
    intro i
    induction i with
    | zero => exact isStoppingTime_const f 0
    | succ i ih =>
      exact isStoppingTime_zetaP' hF (isStoppingTime_nextZeta hF ih)
  refine ⟨hzp i, ?_⟩
  cases i with
  | zero => exact isStoppingTime_const f 0
  | succ i => exact isStoppingTime_nextZeta hF (hzp i)

end Step78Data

end ElboimSly.Paper.Step

end
