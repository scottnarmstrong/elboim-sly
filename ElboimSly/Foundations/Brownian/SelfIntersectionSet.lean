/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Measurability

import Mathlib

/-!
# The separation set of a Brownian path and its measurability

ES22 Claim 9.4 (Step 0), larger lag and scaled paths; the form used in ES22 S8 (a).

`sepSet B σ L t ω` is the set `T_L(σ B)` of times `s ∈ [0,t]` such that `‖σ B(s) - σ B(s')‖ ≤ 1`
for some `s' ∈ [0, s - L]` (written `s' + L ≤ s`, so that no truncated subtraction occurs).
The set `{(s, ω) :...}` is jointly measurable, and so `ω ↦ Leb (sepSet.)` is measurable.

The deterministic lemmas here reduce quantifiers over real times to quantifiers over countable
sets of times, which is what makes the events of the proof measurable for the filtration.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- Rational times `≤ a` approximate any time `≤ a`. -/
lemma exists_ratTimes_le_near {a u : ℝ≥0} (hu : u ≤ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ ratTimes, q ≤ a ∧ dist q u < ε := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | hpos
  · refine ⟨0, ⟨0, by simp⟩, zero_le, ?_⟩
    rw [← h0]; simpa using hε
  · have he : 0 < Real.toNNReal ε := Real.toNNReal_pos.2 hε
    obtain ⟨q, hq, h1, h2⟩ := exists_ratTimes_btwn (tsub_lt_self hpos he)
    refine ⟨q, hq, h2.le.trans hu, ?_⟩
    rw [NNReal.dist_eq, abs_lt]
    have h3 : (q : ℝ) < u := by exact_mod_cast h2
    have h4 : ((u - Real.toNNReal ε : ℝ≥0) : ℝ) < q := by exact_mod_cast h1
    rw [NNReal.coe_sub_def] at h4
    have h5 : (Real.toNNReal ε : ℝ) = ε := Real.coe_toNNReal _ hε.le
    rw [h5] at h4
    constructor
    · linarith [le_max_left ((u : ℝ) - ε) 0]
    · linarith

/-- A minimum over `[0,a]` is `≤ c` iff it is approximated from above by rational times. -/
lemma exists_le_iff_rat {E : Type*} [SeminormedAddCommGroup E] {w : ℝ≥0 → E}
    (hw : Continuous w) (x : E) (a : ℝ≥0) (c : ℝ) :
    (∃ u ≤ a, ‖x - w u‖ ≤ c) ↔
      ∀ n : ℕ, ∃ q ∈ ratTimes, q ≤ a ∧ ‖x - w q‖ < c + 1 / ((n : ℝ) + 1) := by
  constructor
  · rintro ⟨u, hu, hc⟩ n
    have hcont : ContinuousAt (fun v => ‖x - w v‖) u :=
      (continuous_const.sub hw).norm.continuousAt
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨q, hq, hqa, hqd⟩ := exists_ratTimes_le_near hu hδ
    refine ⟨q, hq, hqa, ?_⟩
    have h1 := hball hqd
    rw [Real.dist_eq] at h1
    have h2 := (abs_lt.1 h1).2
    linarith
  · intro h
    obtain ⟨u, hu, hmin⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) a)).exists_isMinOn
      ⟨0, le_rfl, (zero_le : (0:ℝ≥0) ≤ a)⟩ (f := fun v => ‖x - w v‖)
      (continuous_const.sub hw).norm.continuousOn
    refine ⟨u, hu.2, ?_⟩
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, -, hqa, hlt⟩ := h n
    have := isMinOn_iff.1 hmin q ⟨zero_le, hqa⟩
    linarith

/-- A continuous bound on `[0,a]` holds iff it holds on the countable set `denseSub [0,a]`. -/
lemma forall_le_iff_denseSub {f : ℝ≥0 → ℝ} (hf : Continuous f) (a : ℝ≥0) (c : ℝ) :
    (∀ u ≤ a, f u ≤ c) ↔ ∀ u ∈ denseSub (Set.Icc 0 a), f u ≤ c := by
  constructor
  · intro h u hu
    exact h u (denseSub_subset _ hu).2
  · intro h u hu
    have hcl : IsClosed {v | f v ≤ c} := isClosed_le hf continuous_const
    have h1 : closure (denseSub (Set.Icc (0 : ℝ≥0) a)) ⊆ {v | f v ≤ c} :=
      closure_minimal (fun v hv => h v hv) hcl
    exact h1 (subset_closure_denseSub (Set.ordConnected_Icc) ⟨zero_le, hu⟩)

/-- Oscillation bounds on close pairs of an interval hold iff they hold on a countable dense set. -/
lemma forall_closePairs_iff {E : Type*} [SeminormedAddCommGroup E] {w : ℝ≥0 → E}
    (hw : Continuous w) {J : Set ℝ≥0} (hJ : J.OrdConnected) (h : ℝ≥0) (ρ : ℝ) :
    (∀ p ∈ closePairs J h, ‖w p.1 - w p.2‖ ≤ ρ) ↔
      ∀ p ∈ closePairs (denseSub J) h, ‖w p.1 - w p.2‖ ≤ ρ := by
  constructor
  · intro H p hp
    exact H p (closePairs_mono (denseSub_subset J) h hp)
  · intro H p hp
    have hcl : IsClosed {q : ℝ≥0 × ℝ≥0 | ‖w q.1 - w q.2‖ ≤ ρ} :=
      isClosed_le ((hw.comp continuous_fst).sub (hw.comp continuous_snd)).norm continuous_const
    have h1 : closure (closePairs (denseSub J) h) ⊆ {q : ℝ≥0 × ℝ≥0 | ‖w q.1 - w q.2‖ ≤ ρ} :=
      closure_minimal (fun q hq => H q hq) hcl
    exact h1 (closePairs_subset_closure hJ h hp)

/-- Larger lag and scaled paths; the form used in ES22 S8. The set `T_L(σ B)` of times `s ≤ t` having an earlier time `s'`, at
least `L` before `s`, with `‖σ B(s) - σ B(s')‖ ≤ 1`. -/
def sepSet (B : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ) (L t : ℝ≥0) (ω : Ω) : Set ℝ≥0 :=
  {s | s ≤ t ∧ ∃ s', s' + L ≤ s ∧ ‖σ • B s ω - σ • B s' ω‖ ≤ 1}

/-- ES22 Claim 9.4, Step 0. The set of `(s, ω)` with a separated close
time is jointly measurable. -/
theorem measurableSet_sep [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) (σ : ℝ)
    (L : ℝ≥0) :
    MeasurableSet {p : ℝ≥0 × Ω | ∃ s', s' + L ≤ p.1 ∧ ‖σ • B p.1 p.2 - σ • B s' p.2‖ ≤ 1} := by
  have hU := hB.measurable_uncurry
  have e : {p : ℝ≥0 × Ω | ∃ s', s' + L ≤ p.1 ∧ ‖σ • B p.1 p.2 - σ • B s' p.2‖ ≤ 1} =
      ⋂ n : ℕ, ⋃ q ∈ ratTimes, {p : ℝ≥0 × Ω | q + L ≤ p.1 ∧
        ‖σ • B p.1 p.2 - σ • B q p.2‖ < 1 + 1 / ((n : ℝ) + 1)} := by
    ext ⟨s, ω⟩
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
    have hc : Continuous fun u => σ • B u ω := (hB.continuous_zero ω).1.const_smul σ
    constructor
    · rintro ⟨s', hs', hn⟩
      have hLs : L ≤ s := le_trans le_add_self hs'
      have := (exists_le_iff_rat hc (σ • B s ω) (s - L) 1).1 ⟨s', (le_tsub_iff_right hLs).2 hs', hn⟩
      intro n
      obtain ⟨q, hq, hqa, hlt⟩ := this n
      exact ⟨q, hq, (le_tsub_iff_right hLs).1 hqa, hlt⟩
    · intro H
      have h0 := H 0
      obtain ⟨q0, -, hq0, -⟩ := h0
      have hLs : L ≤ s := le_trans le_add_self hq0
      obtain ⟨u, hu, hn⟩ := (exists_le_iff_rat hc (σ • B s ω) (s - L) 1).2 (fun n => by
        obtain ⟨q, hq, hqs, hlt⟩ := H n
        exact ⟨q, hq, (le_tsub_iff_right hLs).2 hqs, hlt⟩)
      exact ⟨u, (le_tsub_iff_right hLs).1 hu, hn⟩
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.biUnion ratTimes_countable fun q _ => ?_
  have h1 : Measurable fun p : ℝ≥0 × Ω => B p.1 p.2 := hU
  have h2 : Measurable fun p : ℝ≥0 × Ω => B q p.2 := (hB.measurable q).comp measurable_snd
  have hA : MeasurableSet {p : ℝ≥0 × Ω | q + L ≤ p.1} := measurableSet_le measurable_const measurable_fst
  have hN : Measurable fun p : ℝ≥0 × Ω => ‖σ • B p.1 p.2 - σ • B q p.2‖ :=
    ((h1.const_smul σ).sub (h2.const_smul σ)).norm
  exact hA.inter (measurableSet_lt hN measurable_const)

/-- ES22 Claim 9.4 (Step 0), larger lag and scaled paths; the form used in ES22 S8 (a). The Lebesgue measure
`|T_L(σ B)|` is measurable. -/
theorem measurable_sepVol [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) (σ : ℝ)
    (L t : ℝ≥0) : Measurable fun ω => nnLebesgue (sepSet B σ L t ω) := by
  have := measurable_occupation (measurableSet_sep hB σ L) t
  convert this using 2 with ω
  congr 1
  ext s
  simp only [sepSet, mem_ofPred_eq, mem_Icc, zero_le, true_and]

end ElboimSly.Brownian
