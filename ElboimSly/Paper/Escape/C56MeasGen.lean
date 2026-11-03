/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.RelaxedStopping
public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# Measurable path predicates on `CPath`

For a right-continuous path `p` (a `CPath`), a condition `ψ(p(s), s)` that is closed in `s`,
holding for all `s ∈ [a, b]`, may be tested on the rationals of `[a, b]` and at `b`. Hence the set
of `(p, a, b)` satisfying it is measurable.  This is the countable reduction used in the proof of
First relaxed times are relaxed and are stopping times (c) and in the measurability of the events `ℬ_i` of ES22 Claim 5.6.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- The real extension `r ↦ p(r⁺)` of a path. -/
def cpR (p : CPath V) (r : ℝ) : V := p.fn r.toNNReal

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem cpRc (p : CPath V) (r : ℝ) : ∃ ε > 0, ∀ s' ∈ Ico r (r + ε), cpR p s' = cpR p r := by
  by_cases hr : r < 0
  · refine ⟨-r, by linarith, fun s' hs' => ?_⟩
    have h1 : s'.toNNReal = 0 := Real.toNNReal_of_nonpos (by linarith [hs'.2])
    have h2 : r.toNNReal = 0 := Real.toNNReal_of_nonpos hr.le
    simp only [cpR, h1, h2]
  · push Not at hr
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p.rc r.toNNReal)
    refine ⟨(u' : ℝ) - r, ?_, fun s' hs' => ?_⟩
    · have : (r.toNNReal : ℝ) < u' := by exact_mod_cast hu'
      rw [Real.coe_toNNReal _ hr] at this
      linarith
    · have hs'0 : 0 ≤ s' := hr.trans hs'.1
      exact hsub ⟨Real.toNNReal_le_toNNReal hs'.1, by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs'0]; linarith [hs'.2]⟩

/-- The path predicate "for all `s ∈ [a, b]`, `ψ (p s) s`" as a set of triples. -/
def forallBetween (ψ : V → ℝ → Prop) : Set (CPath V × ℝ × ℝ) :=
  {z | ∀ s : ℝ, z.2.1 ≤ s → s ≤ z.2.2 → ψ (z.1.fn s.toNNReal) s}

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem forallBetween_eq (ψ : V → ℝ → Prop) (hcl : ∀ x, IsClosed {s | ψ x s}) :
    forallBetween ψ =
      (⋂ q : ℚ, {z : CPath V × ℝ × ℝ | z.2.1 ≤ q → (q : ℝ) ≤ z.2.2 →
        ψ (z.1.fn (q : ℝ).toNNReal) q}) ∩
      {z | z.2.1 ≤ z.2.2 → ψ (z.1.fn z.2.2.toNNReal) z.2.2} := by
  ext z
  simp only [forallBetween, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  constructor
  · intro h
    exact ⟨fun q h1 h2 => h q h1 h2, fun hab => h _ hab le_rfl⟩
  · rintro ⟨h1, h2⟩ s hs1 hs2
    rcases hs2.eq_or_lt with rfl | hlt
    · exact h2 hs1
    · obtain ⟨ε, hε, hconst⟩ := cpRc z.1 s
      set e := min (s + ε) z.2.2 with he
      have hse : s < e := lt_min (by linarith) hlt
      have hsub : Ioo s e ∩ range ((↑) : ℚ → ℝ) ⊆ {u | ψ (cpR z.1 s) u} := by
        rintro u ⟨⟨hu1, hu2⟩, q, rfl⟩
        have := h1 q (hs1.trans hu1.le) (hu2.le.trans (min_le_right _ _))
        have hc : cpR z.1 q = cpR z.1 s :=
          hconst q ⟨hu1.le, lt_of_lt_of_le hu2 (min_le_left _ _)⟩
        have h' : ψ (cpR z.1 q) q := this
        rw [hc] at h'
        exact h'
      have hcl' := hcl (cpR z.1 s)
      have hmem : s ∈ closure (Ioo s e) := by
        rw [closure_Ioo hse.ne]; exact left_mem_Icc.2 hse.le
      have hdense : Ioo s e ⊆ closure (Ioo s e ∩ range ((↑) : ℚ → ℝ)) :=
        Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
      have : closure (Ioo s e) ⊆ {u | ψ (cpR z.1 s) u} := by
        refine closure_minimal ?_ hcl'
        intro u hu
        exact (closure_minimal hsub hcl') (hdense hu)
      exact this hmem

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- The endpoint predicate `ψ (p b, b)` as a set of triples. -/
theorem mem_forallBetween_of_rat (ψ : V → ℝ → Prop) (hcl : ∀ x, IsClosed {s | ψ x s})
    (p : CPath V) (a b : ℝ)
    (h1 : ∀ q : ℚ, a ≤ (q : ℝ) → (q : ℝ) ≤ b → ψ (p.fn (q : ℝ).toNNReal) q)
    (h2 : a ≤ b → ψ (p.fn b.toNNReal) b) :
    ∀ s : ℝ, a ≤ s → s ≤ b → ψ (p.fn s.toNNReal) s := by
  have hmem : (p, a, b) ∈ forallBetween ψ := by
    rw [forallBetween_eq ψ hcl]
    exact ⟨mem_iInter.2 fun q => h1 q, h2⟩
  exact hmem

theorem measurableSet_endpoint (ψ : V → ℝ → Prop) (hm : ∀ x, MeasurableSet {s | ψ x s}) :
    MeasurableSet {z : CPath V × ℝ × ℝ | ψ (z.1.fn z.2.2.toNNReal) z.2.2} := by
  have hev : Measurable fun z : CPath V × ℝ × ℝ => z.1.fn z.2.2.toNNReal :=
    measurable_fn_at (fun z : CPath V × ℝ × ℝ => z.1) measurable_fst _
      (measurable_snd.comp measurable_snd).real_toNNReal
  have hm' : MeasurableSet {p : V × ℝ | ψ p.1 p.2} := by
    have : {p : V × ℝ | ψ p.1 p.2} = ⋃ x : V, {x} ×ˢ {s | ψ x s} := by
      ext ⟨x, s⟩; simp
    rw [this]
    exact MeasurableSet.iUnion fun x => (measurableSet_singleton x).prod (hm x)
  exact (hev.prodMk (measurable_snd.comp measurable_snd)) hm'

theorem measurableSet_forallBetween (ψ : V → ℝ → Prop) (hcl : ∀ x, IsClosed {s | ψ x s}) :
    MeasurableSet (forallBetween ψ) := by
  rw [forallBetween_eq ψ hcl]
  refine MeasurableSet.inter (MeasurableSet.iInter fun q => ?_) ?_
  · have hev : Measurable fun z : CPath V × ℝ × ℝ => z.1.fn (q : ℝ).toNNReal :=
      (CPath.measurable_eval _).comp measurable_fst
    have hm : MeasurableSet {x : V | ψ x q} := (Set.to_countable _).measurableSet
    have h1 : MeasurableSet {z : CPath V × ℝ × ℝ | ψ (z.1.fn (q : ℝ).toNNReal) q} :=
      hev hm
    have h2 : MeasurableSet {z : CPath V × ℝ × ℝ | z.2.1 ≤ q} :=
      measurableSet_le (measurable_fst.comp measurable_snd) measurable_const
    have h3 : MeasurableSet {z : CPath V × ℝ × ℝ | (q : ℝ) ≤ z.2.2} :=
      measurableSet_le measurable_const (measurable_snd.comp measurable_snd)
    exact ((h2.inter h3).compl.union h1).congr (by
      ext z; simp only [mem_union, mem_compl_iff, mem_inter_iff, mem_ofPred_eq]; tauto)
  · have h1 := measurableSet_endpoint ψ fun x => (hcl x).measurableSet
    have h2 : MeasurableSet {z : CPath V × ℝ × ℝ | z.2.1 ≤ z.2.2} :=
      measurableSet_le (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
    exact (h2.compl.union h1).congr (by
      ext z; simp only [mem_union, mem_compl_iff, mem_ofPred_eq]; tauto)

end ElboimSly.Paper.Escape

end
