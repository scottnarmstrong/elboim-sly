/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.AdmitsBMCoupling
public import ElboimSly.Foundations.SRW.CountableReduction
public import Mathlib

/-!
# Measurability of the failure event of an (H4) coupling

For `p = (w, b) ∈ WalkPath d T × C(ℝ≥0, ℝᵈ)` the supremum over `t ∈ [0,T]` of
`‖w t - σ b t‖` equals the supremum over the rational times and `T`
(`iSup_failTime_eq`), because `w` is right-constant between its finitely many jump times and `b`
is continuous. Hence the failure event of `AdmitsBMCoupling` is measurable
(`measurableSet_failEvent`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW

variable {d : ℕ} {T : ℝ≥0}

/-- The integrand of the failure event of `AdmitsBMCoupling`. -/
noncomputable def failTime (σ : ℝ) (p : WalkPath d T × C(ℝ≥0, Fin d → ℝ))
    (t : Set.Icc (0 : ℝ≥0) T) : ℝ≥0∞ :=
  ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • p.2 (t : ℝ≥0)‖

/-- Rational times in `[0,T]` together with `T`. -/
def failTimes (T : ℝ≥0) : Set (Set.Icc (0 : ℝ≥0) T) :=
  {q | (q : ℝ≥0) = T ∨ (q : ℝ≥0) ∈ Set.range ratNN}

theorem failTimes_countable (T : ℝ≥0) : (failTimes T).Countable := by
  have h : ({T} ∪ Set.range ratNN : Set ℝ≥0).Countable :=
    (Set.countable_singleton _).union (Set.countable_range _)
  exact h.preimage Subtype.val_injective

theorem measurable_failTime (σ : ℝ) (t : Set.Icc (0 : ℝ≥0) T) :
    Measurable (failTime (d := d) σ · t) := by
  unfold failTime
  have h1 : Measurable fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) =>
      (fun i => ((p.1.1 t i : ℤ) : ℝ)) :=
    measurable_pi_iff.2 fun i => (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp
      (show Measurable fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.1.1 t i from
        (measurable_pi_apply i).comp ((measurable_pi_apply t).comp
          (measurable_subtype_coe.comp measurable_fst)))
  have h2 : Measurable fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.2 (t : ℝ≥0) :=
    (ContinuousMap.measurable_eval _).comp measurable_snd
  exact ENNReal.measurable_ofReal.comp (h1.sub (h2.const_smul σ)).norm

theorem failTime_le_iSup (σ : ℝ) (p : WalkPath d T × C(ℝ≥0, Fin d → ℝ))
    (t : Set.Icc (0 : ℝ≥0) T) : failTime σ p t ≤ ⨆ q : failTimes T, failTime σ p q := by
  rcases eq_or_lt_of_le t.2.2 with htT | htT
  · exact le_iSup (fun q : failTimes T => failTime σ p q) ⟨t, Or.inl htT⟩
  obtain ⟨F, hF⟩ := p.1.2
  classical
  -- no jump time in `(t, u0)`
  obtain ⟨u0, hu0t, hu0T, hu0F⟩ : ∃ u0 : ℝ≥0, (t : ℝ≥0) < u0 ∧ u0 ≤ T ∧
      ∀ r ∈ F, (t : ℝ≥0) < r → u0 ≤ r := by
    rcases (F.filter fun r => (t : ℝ≥0) < r).eq_empty_or_nonempty with hE | hne
    · refine ⟨T, htT, le_rfl, fun r hr htr => ?_⟩
      exfalso
      have : r ∈ F.filter fun r => (t : ℝ≥0) < r := Finset.mem_filter.2 ⟨hr, htr⟩
      rw [hE] at this; simp at this
    · obtain ⟨m, hm, hmin⟩ := (F.filter fun r => (t : ℝ≥0) < r).exists_min_image id hne
      refine ⟨min T m, lt_min htT (Finset.mem_filter.1 hm).2, min_le_left _ _,
        fun r hr htr => (min_le_right _ _).trans (hmin r (Finset.mem_filter.2 ⟨hr, htr⟩))⟩
  set v : Fin d → ℝ := fun i => ((p.1.1 t i : ℤ) : ℝ) with hv
  set h : ℝ≥0 → ℝ := fun s => ‖v - σ • p.2 s‖ with hh
  have hcont : Continuous h := by
    have := p.2.continuous
    fun_prop
  -- values at times in `(t, u0)`
  have hq : ∀ q : Set.Icc (0 : ℝ≥0) T, (t : ℝ≥0) < q → (q : ℝ≥0) < u0 →
      failTime σ p q = ENNReal.ofReal (h q) := by
    intro q h1 h2
    have : p.1.1 t = p.1.1 q := hF t q h1.le (fun r hr ⟨a, b⟩ => by
      have := hu0F r hr a
      exact absurd (lt_of_le_of_lt b h2) (not_lt.2 this))
    unfold failTime
    simp only [hh, hv, this]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont.continuousAt (ε : ℝ) (by exact_mod_cast hε)
  obtain ⟨r, hr1, hr2⟩ := exists_ratNN_btwn (lt_min hu0t (lt_add_of_pos_right (t : ℝ≥0)
    (show (0 : ℝ≥0) < ⟨δ, hδ.le⟩ from hδ)))
  have hqT : ratNN r ≤ T := (hr2.trans_le (min_le_left _ _)).le.trans hu0T
  set q : Set.Icc (0 : ℝ≥0) T := ⟨ratNN r, zero_le, hqT⟩
  have hqm : q ∈ failTimes T := Or.inr ⟨r, rfl⟩
  have hdist : dist (ratNN r) (t : ℝ≥0) < δ := by
    rw [NNReal.dist_eq]
    have := hr2.trans_le (min_le_right _ _)
    have h3 : ((ratNN r : ℝ≥0) : ℝ) < (t : ℝ) + δ := by exact_mod_cast this
    rw [abs_lt]; constructor <;> linarith [hr1.le, (show ((t : ℝ≥0) : ℝ) ≤ ((ratNN r : ℝ≥0) : ℝ) from by exact_mod_cast hr1.le)]
  have hd := hδ' hdist
  rw [Real.dist_eq] at hd
  have hle : h t ≤ h (ratNN r) + ε := by
    have := (abs_lt.1 hd).1
    linarith
  calc failTime σ p t = ENNReal.ofReal (h t) := rfl
    _ ≤ ENNReal.ofReal (h (ratNN r) + ε) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (h (ratNN r)) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = failTime σ p q + ε := by
        have hfq : failTime σ p q = ENNReal.ofReal (h (ratNN r)) :=
          hq q hr1 (hr2.trans_le (min_le_left _ _))
        rw [hfq, ENNReal.ofReal_coe_nnreal]
    _ ≤ _ := by
        gcongr
        exact le_iSup (fun q : failTimes T => failTime σ p q) ⟨q, hqm⟩

theorem iSup_failTime_eq (σ : ℝ) (p : WalkPath d T × C(ℝ≥0, Fin d → ℝ)) :
    (⨆ t : Set.Icc (0 : ℝ≥0) T, failTime σ p t) = ⨆ q : failTimes T, failTime σ p q :=
  le_antisymm (iSup_le fun t => failTime_le_iSup σ p t)
    (iSup_le fun q => le_iSup (fun t : Set.Icc (0 : ℝ≥0) T => failTime σ p t) q)

theorem measurableSet_failEvent (σ ε : ℝ) :
    MeasurableSet {p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) |
      ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) T, failTime σ p t} := by
  have : {p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) |
      ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) T, failTime σ p t} =
      {p | ENNReal.ofReal ε ≤ ⨆ q : failTimes T, failTime σ p q} := by
    ext p; simp only [Set.mem_ofPred_eq, iSup_failTime_eq]
  rw [this]
  have : Countable (failTimes T) := (failTimes_countable T).to_subtype
  exact measurableSet_le measurable_const (Measurable.iSup fun q => measurable_failTime σ q.1)

end ElboimSly.Paper

end
