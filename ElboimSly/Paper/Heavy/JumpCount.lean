/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.CyclicPath
public import Mathlib

/-!
# Pathwise jump counting for cyclic paths

Supporting material for pathwise consequences of tfast and heavyJ (supplement).

* `IsCyclicPath.eq_of_no_jump`: a cyclic path without discontinuities in `(a, b]` is constant on it.
* `IsCyclicPath.norm1_le_jumpCount`: `‖w b - w a‖₁ ≤ J_w(a, b]`, since each jump has `ℓ¹`-size `1`.
-/

@[expose] public section

open Filter Topology Set

namespace ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

/-- A cyclic path with no discontinuity in `(a, b]` is constant on `[a, b]`. -/
theorem IsCyclicPath.eq_of_no_jump (hw : IsCyclicPath w) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ u ∈ Ioc a b, u ∉ cycJumpSet w) : w b = w a := by
  have hc : ContinuousOn w (Icc a b) := by
    intro x hx
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    rcases eq_or_lt_of_le hx.1 with hxa | hxa
    · subst hxa
      exact (hw.rc a ha).filter_mono (nhdsWithin_mono a (fun y hy => hy.1))
    · have hxj : x ∉ cycJumpSet w := h x ⟨hxa, hx.2⟩
      have hx0 : 0 < x := lt_of_le_of_lt ha hxa
      have hl : ∀ᶠ u in 𝓝[<] x, w u = w x := by
        by_contra hcon
        exact hxj ⟨hx0, hcon⟩
      have : ∀ᶠ u in 𝓝 x, w u = w x := by
        rw [← nhdsLT_sup_nhdsGE x, eventually_sup]
        exact ⟨hl, hw.rc x hx0.le⟩
      exact nhdsWithin_le_nhds this
  exact (isPreconnected_Icc.constant hc ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩ : w b = w a)

/-- Each discontinuity has `ℓ¹`-size `1`, so the `ℓ¹` displacement is at most the jump count. -/
theorem IsCyclicPath.norm1_le_jumpCount (hw : IsCyclicPath w) :
    ∀ (n : ℕ) (a b : ℝ), 0 ≤ a → a ≤ b → (cycJumpSet w ∩ Ioc a b).ncard = n →
      ∑ i, |w b i - w a i| ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b ha hab hn
  set S := cycJumpSet w ∩ Ioc a b with hS
  have hfin : S.Finite := (hw.fin b).subset fun x hx => ⟨hx.1, hx.2.2⟩
  by_cases hne : S.Nonempty
  · obtain ⟨r, hrS, hrmax⟩ := Set.exists_max_image S id hfin hne
    have hra : a < r := hrS.2.1
    have hrb : r ≤ b := hrS.2.2
    set S' := S \ {r} with hS'
    have hfin' : S'.Finite := hfin.sdiff
    have hcard' : S'.ncard + 1 = n := by
      rw [← hn]
      have := Set.ncard_sdiff_singleton_add_one hrS hfin
      simpa [hS'] using this
    have hlt : ∀ x ∈ S', x < r := fun x hx =>
      lt_of_le_of_ne (hrmax x hx.1) (by simpa using hx.2)
    have e1 : ∀ᶠ u in 𝓝[<] r, ∑ i, |w r i - w u i| = 1 := hw.jump_size r hrS.1
    have e2 : ∀ᶠ u in 𝓝[<] r, a < u ∧ u < r := by
      filter_upwards [Ioo_mem_nhdsLT hra] with u hu using hu
    have e3 : ∀ᶠ u in 𝓝[<] r, ∀ x ∈ S', x < u := by
      rw [Filter.eventually_all_finite hfin']
      intro x hx
      filter_upwards [Ioo_mem_nhdsLT (hlt x hx)] with u hu using hu.1
    obtain ⟨u, hu1, hu2, hu3⟩ := (e1.and (e2.and e3)).exists
    obtain ⟨hau, hur⟩ := hu2
    have hsub : cycJumpSet w ∩ Ioc a u ⊆ S' := by
      intro x hx
      refine ⟨⟨hx.1, hx.2.1, hx.2.2.trans (hur.le.trans hrb)⟩, ?_⟩
      simp only [mem_singleton_iff]
      exact ne_of_lt (lt_of_le_of_lt hx.2.2 hur)
    have hm : (cycJumpSet w ∩ Ioc a u).ncard ≤ S'.ncard := Set.ncard_le_ncard hsub hfin'
    have ih' := ih (cycJumpSet w ∩ Ioc a u).ncard (by omega) a u ha hau.le rfl
    have hbr : w b = w r := by
      refine hw.eq_of_no_jump (ha.trans hra.le) hrb fun x hx hxj => ?_
      have : x ∈ S := ⟨hxj, hra.trans hx.1, hx.2⟩
      exact absurd (hrmax x this) (not_le.2 hx.1)
    rw [hbr]
    calc ∑ i, |w r i - w a i|
        ≤ ∑ i, (|w r i - w u i| + |w u i - w a i|) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := abs_add_le (w r i - w u i) (w u i - w a i)
          simpa using this
      _ = ∑ i, |w r i - w u i| + ∑ i, |w u i - w a i| := Finset.sum_add_distrib
      _ ≤ 1 + ((cycJumpSet w ∩ Ioc a u).ncard : ℤ) := by rw [hu1]; gcongr
      _ ≤ n := by omega
  · have hn0 : n = 0 := by
      rw [← hn]; simp [Set.not_nonempty_iff_eq_empty.1 hne]
    have : w b = w a := by
      refine hw.eq_of_no_jump ha hab fun x hx hxj => hne ⟨x, hxj, hx⟩
    simp [this, hn0]

end ElboimSly.Paper
