/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.JumpCount
public import ElboimSly.Paper.Heavy.Taufast

/-!
# Pathwise consequences of `τ_fast` and `τ_jump`

Pathwise consequences of tfast and heavyJ (a), (b), (c) (supplement).

* `pathTjump_le_pathTfast`: `τ_jump(w; L) ≤ τ_fast(w; L)`.
* `norm_sub_lt_of_lt_pathTfast`: `‖w u' - w u‖ < L ⌈u' - u⌉` before `τ_fast`.
* `jumpCount_lt_of_lt_pathTjump`: `J_w(u, u'] < L ⌈u' - u⌉` before `τ_jump`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

/-- Chain argument: a bound on windows of length `≤ 1` propagates to `L ⌈v - u⌉`. -/
theorem chain_bound (F : ℝ → ℝ → ℝ) (L : ℝ) (hL : 0 < L) (P : ℝ → Prop)
    (hsub : ∀ u r v, 0 ≤ u → u ≤ r → r ≤ v → F u v ≤ F u r + F r v)
    (hmono : ∀ u v, u ≤ v → P v → P u)
    (hbase : ∀ u v, 0 ≤ u → u < v → v - u ≤ 1 → P v → F u v < L) :
    ∀ (m : ℕ) (u v : ℝ), 0 ≤ u → u < v → v - u ≤ m → P v → F u v < L * m := by
  intro m
  induction m with
  | zero => intro u v _ huv h; simp at h; linarith
  | succ m ih =>
    intro u v hu huv hm hP
    push_cast
    by_cases h1 : v - u ≤ 1
    · have := hbase u v hu huv h1 hP
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    · push Not at h1
      have hur : u < v - 1 := by linarith
      have hr0 : 0 ≤ v - 1 := by linarith
      have a1 := ih u (v - 1) hu hur (by push_cast at hm; linarith) (hmono _ _ (by linarith) hP)
      have a2 := hbase (v - 1) v hr0 (by linarith) (by linarith) hP
      have a3 := hsub u (v - 1) v hu hur.le (by linarith)
      nlinarith

/-- The `ℓ¹` displacement bounds the sup-norm displacement. -/
theorem norm_le_sum_abs (x : Fin d → ℤ) : ‖x‖ ≤ ((∑ i, |x i| : ℤ) : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have : |x i| ≤ ∑ j, |x j| := Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  simpa [Int.norm_eq_abs] using (by exact_mod_cast this : ((|x i| : ℤ) : ℝ) ≤ ((∑ j, |x j| : ℤ) : ℝ))

theorem IsCyclicPath.norm_sub_le_jumpCount (hw : IsCyclicPath w) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : ‖w b - w a‖ ≤ (cycJumpCount w a b : ℝ) := by
  refine (norm_le_sum_abs _).trans ?_
  have := hw.norm1_le_jumpCount _ a b ha hab rfl
  exact_mod_cast this

theorem cycJumpCount_mono_left (hw : IsCyclicPath w) {a a' b : ℝ} (h : a ≤ a') :
    cycJumpCount w a' b ≤ cycJumpCount w a b :=
  Set.ncard_le_ncard (inter_subset_inter_right _ (Ioc_subset_Ioc_left h))
    ((hw.fin b).subset fun _x hx => ⟨hx.1, hx.2.2⟩)

theorem cycJumpCount_add_le (hw : IsCyclicPath w) {u r v : ℝ} (_h1 : u ≤ r) (_h2 : r ≤ v) :
    cycJumpCount w u v ≤ cycJumpCount w u r + cycJumpCount w r v := by
  have f1 : (cycJumpSet w ∩ Ioc u r).Finite := (hw.fin r).subset fun x hx => ⟨hx.1, hx.2.2⟩
  have f2 : (cycJumpSet w ∩ Ioc r v).Finite := (hw.fin v).subset fun x hx => ⟨hx.1, hx.2.2⟩
  have hsub : cycJumpSet w ∩ Ioc u v ⊆ (cycJumpSet w ∩ Ioc u r) ∪ (cycJumpSet w ∩ Ioc r v) := by
    intro x hx
    rcases le_or_gt x r with hxr | hxr
    · exact Or.inl ⟨hx.1, hx.2.1, hxr⟩
    · exact Or.inr ⟨hx.1, hxr, hx.2.2⟩
  exact (Set.ncard_le_ncard hsub (f1.union f2)).trans (Set.ncard_union_le _ _)

/-- Pathwise consequences of tfast and heavyJ (a). -/
theorem pathTjump_le_pathTfast (hw : IsCyclicPath w) (L : ℝ) :
    pathTjump w L ≤ pathTfast w L := by
  unfold pathTjump pathTfast
  refine le_iInf₂ fun t ht => iInf₂_le t ?_
  obtain ⟨ht0, s, hs1, hs2, hL⟩ := ht
  refine ⟨ht0, ?_⟩
  have h0 : 0 ≤ max s 0 := le_max_right _ _
  have h1 : max s 0 ≤ t := max_le hs2 ht0.le
  have h2 := hw.norm_sub_le_jumpCount h0 h1
  have h3 : cycJumpCount w (t - 1) t ≥ cycJumpCount w (max s 0) t :=
    cycJumpCount_mono_left hw (hs1.trans (le_max_left _ _))
  have : (cycJumpCount w (max s 0) t : ℝ) ≤ cycJumpCount w (t - 1) t := by exact_mod_cast h3
  linarith

/-- Pathwise consequences of tfast and heavyJ (b). -/
theorem norm_sub_lt_of_lt_pathTfast (_hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) {u u' : ℝ}
    (hu : 0 ≤ u) (huu : u < u') (h : ENNReal.ofReal u' < pathTfast w L) :
    ‖w u' - w u‖ < L * ⌈u' - u⌉₊ := by
  refine chain_bound (fun a b => ‖w b - w a‖) L hL (fun v => ENNReal.ofReal v < pathTfast w L)
    ?_ ?_ ?_ ⌈u' - u⌉₊ u u' hu huu (Nat.le_ceil _) h
  · intro a r v _ _ _
    have := norm_sub_le_norm_sub_add_norm_sub (w v) (w r) (w a)
    show ‖w v - w a‖ ≤ ‖w r - w a‖ + ‖w v - w r‖
    linarith
  · intro a v hav hv
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hav) hv
  · intro a v ha hav hv1 hP
    by_contra hge
    push Not at hge
    have hmem : v ∈ {t : ℝ | 0 < t ∧ ∃ s : ℝ, t - 1 ≤ s ∧ s ≤ t ∧ L ≤ ‖w t - w (max s 0)‖} :=
      ⟨by linarith, a, by linarith, hav.le, by rwa [max_eq_left ha]⟩
    exact absurd (iInf₂_le (f := fun t (_ : t ∈ _) => ENNReal.ofReal t) v hmem |>.trans_lt hP)
      (lt_irrefl _)

/-- Pathwise consequences of tfast and heavyJ (c). -/
theorem jumpCount_lt_of_lt_pathTjump (hw : IsCyclicPath w) {L : ℝ} (hL : 0 < L) {u u' : ℝ}
    (hu : 0 ≤ u) (huu : u < u') (h : ENNReal.ofReal u' < pathTjump w L) :
    (cycJumpCount w u u' : ℝ) < L * ⌈u' - u⌉₊ := by
  refine chain_bound (fun a b => (cycJumpCount w a b : ℝ)) L hL
    (fun v => ENNReal.ofReal v < pathTjump w L) ?_ ?_ ?_ ⌈u' - u⌉₊ u u' hu huu (Nat.le_ceil _) h
  · intro a r v _ h1 h2
    exact_mod_cast cycJumpCount_add_le hw h1 h2
  · intro a v hav hv
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hav) hv
  · intro a v ha hav hv1 hP
    by_contra hge
    push Not at hge
    have h3 : (cycJumpCount w (v - 1) v : ℝ) ≥ cycJumpCount w a v := by
      exact_mod_cast cycJumpCount_mono_left hw (by linarith : v - 1 ≤ a)
    have hmem : v ∈ {t : ℝ | 0 < t ∧ L ≤ (cycJumpCount w (t - 1) t : ℝ)} :=
      ⟨by linarith, by linarith⟩
    exact absurd (iInf₂_le (f := fun t (_ : t ∈ _) => ENNReal.ofReal t) v hmem |>.trans_lt hP)
      (lt_irrefl _)

end ElboimSly.Paper
