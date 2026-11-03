/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.JumpEvents
public import Mathlib

/-!
# Time shifts and measurable jump-count events

Supporting material for fast jumping is unlikely (supplement).

* `JGE_congr`: `JGE w k a b` only depends on `w` on `[a, b]`.
* `jgeSet k a b`: the measurable set of paths `f : ℝ≥0 → ℤᵈ` with `JGE (f ∘ toNNReal) k a b`.
* `shiftPath w a`: the path `s ↦ w (a + s) - w a`, a cyclic path if `w` is, with
  `J_{shiftPath w a}(0, b] = J_w(a, a + b]` (`cycJumpCount_shiftPath`).
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly.Paper

variable {d : ℕ}

theorem cutPts_mem_bounds {a b p : ℝ} (hab : a ≤ b) (hp : p ∈ cutPts a b) : a ≤ p ∧ p ≤ b := by
  rcases hp with rfl | ⟨q, h1, h2, rfl⟩
  · exact ⟨hab, le_rfl⟩
  · exact ⟨h1.le, h2.le⟩

theorem JumpIn_congr_aux {w w' : ℝ → Fin d → ℤ} {a p : ℝ} (h : ∀ x ∈ Icc a p, w x = w' x)
    (hap : a ≤ p) (hj : JumpIn w a p) : JumpIn w' a p := by
  have ha := h a ⟨le_rfl, hap⟩
  have hp := h p ⟨hap, le_rfl⟩
  rcases hj with h1 | ⟨q, hq1, hq2, hq3⟩
  · left; rwa [← ha, ← hp]
  · right
    exact ⟨q, hq1, hq2, by rwa [← ha, ← h q ⟨hq1.le, hq2.le⟩]⟩

/-- `JGE w k a b` depends only on the values of `w` on `[a, b]`. -/
theorem JGE_congr {w w' : ℝ → Fin d → ℤ} (k : ℕ) :
    ∀ a b : ℝ, a ≤ b → (∀ x ∈ Icc a b, w x = w' x) → (JGE w k a b ↔ JGE w' k a b) := by
  induction k with
  | zero => intros; simp [JGE]
  | succ k ih =>
    intro a b hab h
    simp only [JGE]
    refine exists_congr fun p => and_congr_right fun hp => ?_
    obtain ⟨h1, h2⟩ := cutPts_mem_bounds hab hp
    have hc : ∀ x ∈ Icc a p, w x = w' x := fun x hx => h x ⟨hx.1, hx.2.trans h2⟩
    have hrest := ih p b h2 (fun x hx => h x ⟨h1.trans hx.1, hx.2⟩)
    constructor
    · rintro ⟨hj, hg⟩
      exact ⟨JumpIn_congr_aux hc h1 hj, hrest.1 hg⟩
    · rintro ⟨hj, hg⟩
      exact ⟨JumpIn_congr_aux (fun x hx => (hc x hx).symm) h1 hj, hrest.2 hg⟩

/-- The set of paths on `[0, ∞)` with `JGE (f ∘ toNNReal) k a b`. -/
def jgeSet (d : ℕ) (k : ℕ) (a b : ℝ) : Set (ℝ≥0 → Fin d → ℤ) :=
  {f | JGE (fun s : ℝ => f s.toNNReal) k a b}

theorem measurableSet_ne_eval (x y : ℝ≥0) :
    MeasurableSet {f : ℝ≥0 → Fin d → ℤ | f x ≠ f y} := by
  have := measurableSet_eq_fun
    (measurable_pi_apply (X := fun _ : ℝ≥0 => Fin d → ℤ) x)
    (measurable_pi_apply (X := fun _ : ℝ≥0 => Fin d → ℤ) y)
  exact this.compl

theorem measurableSet_jumpIn (a p : ℝ) :
    MeasurableSet {f : ℝ≥0 → Fin d → ℤ | JumpIn (fun s : ℝ => f s.toNNReal) a p} := by
  have : {f : ℝ≥0 → Fin d → ℤ | JumpIn (fun s : ℝ => f s.toNNReal) a p} =
      {f | f p.toNNReal ≠ f a.toNNReal} ∪
        ⋃ q : ℚ, {f | a < (q : ℝ) ∧ (q : ℝ) < p ∧ f (q : ℝ).toNNReal ≠ f a.toNNReal} := by
    ext f
    simp [JumpIn]
  rw [this]
  refine (measurableSet_ne_eval _ _).union (MeasurableSet.iUnion fun q => ?_)
  by_cases h : a < (q : ℝ) ∧ (q : ℝ) < p
  · have : {f : ℝ≥0 → Fin d → ℤ | a < (q : ℝ) ∧ (q : ℝ) < p ∧
        f (q : ℝ).toNNReal ≠ f a.toNNReal} = {f | f (q : ℝ).toNNReal ≠ f a.toNNReal} := by
      ext f; simp [h.1, h.2]
    rw [this]; exact measurableSet_ne_eval _ _
  · have : {f : ℝ≥0 → Fin d → ℤ | a < (q : ℝ) ∧ (q : ℝ) < p ∧
        f (q : ℝ).toNNReal ≠ f a.toNNReal} = ∅ := by
      ext f; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun ⟨h1, h2, _⟩ => h ⟨h1, h2⟩
    rw [this]; exact MeasurableSet.empty

theorem measurableSet_jgeSet (k : ℕ) : ∀ a b : ℝ, MeasurableSet (jgeSet d k a b) := by
  induction k with
  | zero => intro a b; simp [jgeSet, JGE]
  | succ k ih =>
    intro a b
    have hc : (cutPts a b).Countable := by
      refine ((Set.countable_singleton b).union
        (Set.countable_range (fun q : ℚ => (q : ℝ)))).mono ?_
      rintro p (rfl | ⟨q, -, -, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨q, rfl⟩
    have : jgeSet d (k + 1) a b = ⋃ p ∈ cutPts a b,
        ({f | JumpIn (fun s : ℝ => f s.toNNReal) a p} ∩ jgeSet d k p b) := by
      ext f; simp only [jgeSet, JGE, mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
    rw [this]
    exact MeasurableSet.biUnion hc fun p _ => (measurableSet_jumpIn a p).inter (ih p b)

/-- The shifted path `s ↦ w (a + max s 0) - w a`. -/
def shiftPath (w : ℝ → Fin d → ℤ) (a : ℝ) : ℝ → Fin d → ℤ := fun s => w (a + max s 0) - w a

theorem tendsto_add_nhdsLT (a r : ℝ) : Tendsto (fun u => a + u) (𝓝[<] r) (𝓝[<] (a + r)) :=
  tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add continuous_id).tendsto r).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun u hu => by
      have : u < r := hu
      show a + u < a + r
      linarith⟩

theorem tendsto_sub_nhdsLT (a r : ℝ) : Tendsto (fun v => v - a) (𝓝[<] (a + r)) (𝓝[<] r) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
  · have h : Continuous fun v : ℝ => v - a := continuous_id.sub continuous_const
    have := (h.tendsto (a + r)).mono_left (nhdsWithin_le_nhds (s := Iio (a + r)))
    simpa using this
  · have : u < a + r := hu
    show u - a < r
    linarith

theorem mem_cycJumpSet_shiftPath {w : ℝ → Fin d → ℤ} {a r : ℝ} (ha : 0 ≤ a) :
    r ∈ cycJumpSet (shiftPath w a) ↔ 0 < r ∧ a + r ∈ cycJumpSet w := by
  constructor
  · rintro ⟨hr, hn⟩
    refine ⟨hr, by linarith, fun hev => hn ?_⟩
    have := (tendsto_add_nhdsLT a r).eventually hev
    filter_upwards [this, Ioo_mem_nhdsLT hr] with u hu hu0
    simp only [shiftPath, max_eq_left hu0.1.le, max_eq_left hr.le]
    rw [hu]
  · rintro ⟨hr, h0, hn⟩
    refine ⟨hr, fun hev => hn ?_⟩
    have := (tendsto_sub_nhdsLT a r).eventually hev
    filter_upwards [this, Ioo_mem_nhdsLT (show a < a + r by linarith)] with v hv hv0
    simp only [shiftPath, max_eq_left (show 0 ≤ v - a by linarith [hv0.1]),
      max_eq_left hr.le, add_sub_cancel] at hv
    exact sub_left_inj.1 hv

/-- A time shift of a cyclic path is a cyclic path. -/
theorem isCyclicPath_shiftPath {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {a : ℝ} (ha : 0 ≤ a) :
    IsCyclicPath (ElboimSly.Paper.Heavy.shiftPath w a) where
  zero := by simp [ElboimSly.Paper.Heavy.shiftPath]
  rc s hs := by
    have ht : Tendsto (fun u => a + u) (𝓝[≥] s) (𝓝[≥] (a + s)) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add continuous_id).tendsto s).mono_left
        nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun u hu => by
          have : s ≤ u := hu
          show a + s ≤ a + u
          linarith⟩
    filter_upwards [ht.eventually (hw.rc (a + s) (by linarith)), self_mem_nhdsWithin] with u hu hu0
    have hu0' : 0 ≤ u := hs.trans hu0
    simp only [ElboimSly.Paper.Heavy.shiftPath, max_eq_left hu0', max_eq_left hs]
    rw [hu]
  fin T := by
    refine ((hw.fin (a + T)).image (fun v => v - a)).subset ?_
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    obtain ⟨h0, h1⟩ := (mem_cycJumpSet_shiftPath ha).1 hr1
    have hrT : r ≤ T := hr2
    exact ⟨a + r, ⟨h1, by show a + r ≤ a + T; linarith⟩, by ring⟩
  jump_size r hr := by
    obtain ⟨h0, h1⟩ := (mem_cycJumpSet_shiftPath ha).1 hr
    have := (tendsto_add_nhdsLT a r).eventually (hw.jump_size _ h1)
    filter_upwards [this, Ioo_mem_nhdsLT h0] with u hu hu0
    simp only [ElboimSly.Paper.Heavy.shiftPath, max_eq_left hu0.1.le, max_eq_left h0.le]
    simpa using hu

theorem cycJumpCount_shiftPath (w : ℝ → Fin d → ℤ) (a b : ℝ) (ha : 0 ≤ a) :
    cycJumpCount (shiftPath w a) 0 b = cycJumpCount w a (a + b) := by
  unfold cycJumpCount
  have : cycJumpSet w ∩ Ioc a (a + b) =
      (fun u => a + u) '' (cycJumpSet (shiftPath w a) ∩ Ioc 0 b) := by
    ext v
    constructor
    · rintro ⟨hv, hv1, hv2⟩
      exact ⟨v - a, ⟨(mem_cycJumpSet_shiftPath ha).2 ⟨by linarith, by simpa using hv⟩,
        by linarith, by linarith⟩, by ring⟩
    · rintro ⟨u, ⟨hu, hu1, hu2⟩, rfl⟩
      exact ⟨((mem_cycJumpSet_shiftPath ha).1 hu).2, by linarith, by linarith⟩
  rw [this, Set.ncard_image_of_injective _ (add_right_injective a)]

end ElboimSly.Paper.Heavy
