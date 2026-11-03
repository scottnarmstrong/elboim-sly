/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasJump

/-!
# `τ_jump` is a stopping time (measurability part)

Measurability (c).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m}
  {w : Ω → ℝ → Fin d → ℤ}

theorem AdaptedCyclic.measurableSet_ne (h : AdaptedCyclic f w) {s₁ s₂ : ℝ} (h1 : 0 ≤ s₁)
    (h2 : 0 ≤ s₂) {t : ℝ≥0} (h1t : s₁ ≤ t) (h2t : s₂ ≤ t) :
    MeasurableSet[f t] {ω | w ω s₁ ≠ w ω s₂} := by
  have := ((h.measurable_at h1 h1t).prodMk (h.measurable_at h2 h2t))
    (Set.to_countable {p : (Fin d → ℤ) × (Fin d → ℤ) | p.1 ≠ p.2}).measurableSet
  exact this

theorem AdaptedCyclic.measurableSet_jumpIn (h : AdaptedCyclic f w) {a p : ℝ} (ha : 0 ≤ a)
    (hap : a ≤ p) {t : ℝ≥0} (hpt : p ≤ t) : MeasurableSet[f t] {ω | JumpIn (w ω) a p} := by
  have hset : {ω | JumpIn (w ω) a p} = {ω | w ω p ≠ w ω a} ∪
      ⋃ q : {q : ℚ // a < (q : ℝ) ∧ (q : ℝ) < p}, {ω | w ω q ≠ w ω a} := by
    ext ω
    simp only [JumpIn, mem_ofPred_eq, mem_union, mem_iUnion]
    constructor
    · rintro (h1 | ⟨q, h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨⟨q, h1, h2⟩, h3⟩
    · rintro (h1 | ⟨q, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨q.1, q.2.1, q.2.2, h3⟩
  rw [hset]
  refine (h.measurableSet_ne (ha.trans hap) ha hpt (hap.trans hpt)).union
    (MeasurableSet.iUnion fun q => ?_)
  exact h.measurableSet_ne (ha.trans q.2.1.le) ha (q.2.2.le.trans hpt) (hap.trans hpt)

theorem cutPts_countable (a b : ℝ) : (cutPts a b).Countable := by
  refine ((Set.countable_singleton b).union (Set.countable_range (fun q : ℚ => (q : ℝ)))).mono ?_
  rintro p (rfl | ⟨q, -, -, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨q, rfl⟩

theorem cutPts_bounds {a b p : ℝ} (hab : a ≤ b) (hp : p ∈ cutPts a b) : a ≤ p ∧ p ≤ b := by
  rcases hp with rfl | ⟨q, h1, h2, rfl⟩
  · exact ⟨hab, le_rfl⟩
  · exact ⟨h1.le, h2.le⟩

theorem AdaptedCyclic.measurableSet_jGE (h : AdaptedCyclic f w) {t : ℝ≥0} :
    ∀ (k : ℕ) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ t → MeasurableSet[f t] {ω | JGE (w ω) k a b} := by
  intro k
  induction k with
  | zero => intros; simp only [JGE, ofPred_true]; exact @MeasurableSet.univ Ω (f t)
  | succ k ih =>
    intro a b ha hab hbt
    have hset : {ω | JGE (w ω) (k + 1) a b} =
        ⋃ p ∈ cutPts a b, ({ω | JumpIn (w ω) a p} ∩ {ω | JGE (w ω) k p b}) := by
      ext ω
      simp only [JGE, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    rw [hset]
    exact MeasurableSet.biUnion (cutPts_countable a b) fun p hp =>
      (h.measurableSet_jumpIn ha (cutPts_bounds hab hp).1 ((cutPts_bounds hab hp).2.trans hbt)).inter
        (ih p b (ha.trans (cutPts_bounds hab hp).1) (cutPts_bounds hab hp).2 hbt)

/-- Measurability (c): `τ_jump(L)` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_pathTjump (h : AdaptedCyclic f w) {L : ℝ} (hL : 0 < L) :
    IsStoppingTime f (fun ω => pathTjump (w ω) L) := by
  intro i
  have hset : {ω | pathTjump (w ω) L ≤ (i : WithTop ℝ≥0)} =
      ⋃ t ∈ rationalTimes i, {ω | JGE (w ω) ⌈L⌉₊ (max (t - 1) 0) t} := by
    ext ω
    have := pathTjump_le_iff_rational (h.path ω) hL (T := (i : ℝ)) (NNReal.coe_nonneg i)
    simp only [ENNReal.ofReal_coe_nnreal] at this
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    refine this.trans (exists_congr fun t => and_congr_right fun ht => ?_)
    obtain ⟨ht0, -⟩ := rationalTimes_pos ht
    rw [jGE_iff (h.path ω) (le_max_right _ _) (max_le (by linarith) ht0.le),
      ← cycJumpCount_max_zero, Nat.ceil_le]
  have key : MeasurableSet[f i] (⋃ t ∈ rationalTimes i,
      {ω | JGE (w ω) ⌈L⌉₊ (max (t - 1) 0) t}) :=
    MeasurableSet.biUnion (rationalTimes_countable _) fun t ht =>
      h.measurableSet_jGE _ _ _ (le_max_right _ _)
        (max_le (by linarith [(rationalTimes_pos ht).1]) (rationalTimes_pos ht).1.le)
        (rationalTimes_pos ht).2
  exact (congrArg (MeasurableSet[f i]) hset).mpr key

end ElboimSly.Paper
