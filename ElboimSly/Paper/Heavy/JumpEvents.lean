/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.FastDisplacement

/-!
# The event `J_w(a, b] ≥ k` through countably many evaluations

Measurability (c) (jump counts), using paths (a).

`JGE k a b w` is defined by recursion on `k` through evaluations of `w` at `a`, `b`, and rational
times in `(a, b)` only; `jGE_iff` shows `JGE k a b w ↔ k ≤ J_w(a, b]` for a cyclic path and
`0 ≤ a ≤ b`.
-/

@[expose] public section

open Filter Topology Set

namespace ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

/-- The evaluation form of "`w` jumps in `(a, p]`": `w p ≠ w a` or `w q ≠ w a` for a rational
`q ∈ (a, p)`. -/
def JumpIn (w : ℝ → Fin d → ℤ) (a p : ℝ) : Prop :=
  w p ≠ w a ∨ ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < p ∧ w q ≠ w a

/-- The cut points `{b} ∪ (ℚ ∩ (a, b))`. -/
def cutPts (a b : ℝ) : Set ℝ := {b} ∪ {p | ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b ∧ p = q}

/-- `J_w(a, b] ≥ k`, expressed through evaluations at `a`, `b` and rationals. -/
def JGE (w : ℝ → Fin d → ℤ) : ℕ → ℝ → ℝ → Prop
  | 0, _, _ => True
  | k + 1, a, b => ∃ p ∈ cutPts a b, JumpIn w a p ∧ JGE w k p b

theorem cycJumpCount_union (hw : IsCyclicPath w) {a p b : ℝ} (hap : a ≤ p) (hpb : p ≤ b) :
    cycJumpCount w a p + cycJumpCount w p b = cycJumpCount w a b := by
  unfold cycJumpCount
  have f1 : (cycJumpSet w ∩ Ioc a p).Finite := (hw.fin p).subset fun x hx => ⟨hx.1, hx.2.2⟩
  have f2 : (cycJumpSet w ∩ Ioc p b).Finite := (hw.fin b).subset fun x hx => ⟨hx.1, hx.2.2⟩
  have hd : Disjoint (cycJumpSet w ∩ Ioc a p) (cycJumpSet w ∩ Ioc p b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2.2 (not_le.2 hx'.2.1)
  rw [← Set.ncard_union_eq hd f1 f2, ← Set.inter_union_distrib_left, Ioc_union_Ioc_eq_Ioc hap hpb]

theorem one_le_cycJumpCount_of_ne (hw : IsCyclicPath w) {a p : ℝ} (ha : 0 ≤ a) (hap : a ≤ p)
    (h : w p ≠ w a) : 1 ≤ cycJumpCount w a p := by
  by_contra hc
  have h0 : cycJumpCount w a p = 0 := by omega
  have hfin : (cycJumpSet w ∩ Ioc a p).Finite := (hw.fin p).subset fun x hx => ⟨hx.1, hx.2.2⟩
  have hemp : cycJumpSet w ∩ Ioc a p = ∅ := by
    unfold cycJumpCount at h0
    exact (Set.ncard_eq_zero hfin).1 h0
  exact h (hw.eq_of_no_jump ha hap fun u hu hj => by
    have : u ∈ cycJumpSet w ∩ Ioc a p := ⟨hj, hu⟩
    rw [hemp] at this; exact this)

theorem one_le_cycJumpCount_of_jumpIn (hw : IsCyclicPath w) {a p : ℝ} (ha : 0 ≤ a) (hap : a ≤ p)
    (h : JumpIn w a p) : 1 ≤ cycJumpCount w a p := by
  rcases h with h | ⟨q, hq1, hq2, hq⟩
  · exact one_le_cycJumpCount_of_ne hw ha hap h
  · have := one_le_cycJumpCount_of_ne hw ha hq1.le hq
    have h2 : cycJumpCount w a q ≤ cycJumpCount w a p := by
      have := cycJumpCount_union hw hq1.le hq2.le
      omega
    omega

/-- The first discontinuity in `(a, b]` changes the value of `w` relative to `a`. -/
theorem ne_of_first_jump (hw : IsCyclicPath w) {a b r : ℝ} (ha : 0 ≤ a)
    (hr : r ∈ cycJumpSet w ∩ Ioc a b)
    (hmin : ∀ x ∈ cycJumpSet w ∩ Ioc a b, r ≤ x) : w r ≠ w a := by
  have e1 : ∀ᶠ u in 𝓝[<] r, ∑ i, |w r i - w u i| = 1 := hw.jump_size r hr.1
  have e2 : ∀ᶠ u in 𝓝[<] r, a < u ∧ u < r := by
    filter_upwards [Ioo_mem_nhdsLT hr.2.1] with u hu using hu
  obtain ⟨u, hu1, hau, hur⟩ := (e1.and e2).exists
  have hwu : w u = w a := by
    refine hw.eq_of_no_jump ha hau.le fun x hx hxj => ?_
    have := hmin x ⟨hxj, hx.1, hx.2.trans (hur.le.trans hr.2.2)⟩
    exact absurd (hx.2.trans_lt hur) (not_lt.2 this)
  intro heq
  rw [← hwu] at heq
  simp [heq] at hu1

theorem jGE_of_le (hw : IsCyclicPath w) : ∀ (k : ℕ) (a b : ℝ), 0 ≤ a → a ≤ b →
    k ≤ cycJumpCount w a b → JGE w k a b := by
  intro k
  induction k with
  | zero => intros; trivial
  | succ k ih =>
    intro a b ha hab hk
    set S := cycJumpSet w ∩ Ioc a b with hS
    have hfin : S.Finite := (hw.fin b).subset fun x hx => ⟨hx.1, hx.2.2⟩
    have hcard : k + 1 ≤ S.ncard := hk
    have hne : S.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro h; rw [h] at hcard; simp at hcard
    obtain ⟨r1, hr1S, hr1min⟩ := Set.exists_min_image S id hfin hne
    have hr1min' : ∀ x ∈ S, r1 ≤ x := fun x hx => hr1min x hx
    have hne1 : w r1 ≠ w a := ne_of_first_jump hw ha hr1S hr1min'
    have hr1a : a < r1 := hr1S.2.1
    have hr1b : r1 ≤ b := hr1S.2.2
    obtain ⟨u1, hu1, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc r1 (ha.trans hr1a.le))
    have hu1' : r1 < u1 := mem_Ioi.1 hu1
    by_cases hS' : (S \ {r1}).Nonempty
    · have hfin' : (S \ {r1}).Finite := hfin.sdiff
      obtain ⟨r2, hr2S, hr2min⟩ := Set.exists_min_image (S \ {r1}) id hfin' hS'
      have hr12 : r1 < r2 := lt_of_le_of_ne (hr1min' r2 hr2S.1) (fun h => hr2S.2 (by simp [h]))
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r1 < min r2 u1 from lt_min hr12 hu1')
      have hwq : w q = w r1 := hsub ⟨hq1.le, hq2.trans_le (min_le_right _ _)⟩
      have hqr2 : (q : ℝ) < r2 := hq2.trans_le (min_le_left _ _)
      have hr2b : r2 ≤ b := hr2S.1.2.2
      refine ⟨q, Or.inr ⟨q, hr1a.trans hq1, hqr2.trans_le hr2b, rfl⟩, Or.inl (by rwa [hwq]),
        ih q b (ha.trans (hr1a.trans hq1).le) (hqr2.le.trans hr2b) ?_⟩
      have hsub' : S \ {r1} ⊆ cycJumpSet w ∩ Ioc (q : ℝ) b := by
        intro x hx
        exact ⟨hx.1.1, hqr2.trans_le (hr2min x hx), hx.1.2.2⟩
      have h1 := Set.ncard_le_ncard hsub' ((hw.fin b).subset fun x hx => ⟨hx.1, hx.2.2⟩)
      have h2 := Set.ncard_sdiff_singleton_add_one hr1S hfin
      unfold cycJumpCount
      omega
    · have hSeq : S \ {r1} = ∅ := Set.not_nonempty_iff_eq_empty.1 hS'
      have hS1 : S.ncard = 1 := by
        have h2 := Set.ncard_sdiff_singleton_add_one hr1S hfin
        rw [hSeq] at h2; simpa using h2.symm
      have hk0 : k = 0 := by omega
      subst hk0
      refine ⟨b, Or.inl rfl, ?_, trivial⟩
      rcases hr1b.eq_or_lt with h | h
      · exact Or.inl (by rw [← h]; exact hne1)
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r1 < min b u1 from lt_min h hu1')
        refine Or.inr ⟨q, hr1a.trans hq1, hq2.trans_le (min_le_left _ _), ?_⟩
        rwa [hsub ⟨hq1.le, hq2.trans_le (min_le_right _ _)⟩]

theorem le_of_jGE (hw : IsCyclicPath w) : ∀ (k : ℕ) (a b : ℝ), 0 ≤ a → a ≤ b →
    JGE w k a b → k ≤ cycJumpCount w a b := by
  intro k
  induction k with
  | zero => intros; exact Nat.zero_le _
  | succ k ih =>
    rintro a b ha hab ⟨p, hp, hj, hrest⟩
    have hpb : p ≤ b ∧ a ≤ p := by
      rcases hp with rfl | ⟨q, hq1, hq2, rfl⟩
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hq2.le, hq1.le⟩
    have h1 := one_le_cycJumpCount_of_jumpIn hw ha hpb.2 hj
    have h2 := ih p b (ha.trans hpb.2) hpb.1 hrest
    have h3 := cycJumpCount_union hw hpb.2 hpb.1
    omega

/-- For a cyclic path and `0 ≤ a ≤ b`: `JGE k a b w ↔ k ≤ J_w(a, b]`. -/
theorem jGE_iff (hw : IsCyclicPath w) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) :
    JGE w k a b ↔ k ≤ cycJumpCount w a b :=
  ⟨le_of_jGE hw k a b ha hab, jGE_of_le hw k a b ha hab⟩

end ElboimSly.Paper
