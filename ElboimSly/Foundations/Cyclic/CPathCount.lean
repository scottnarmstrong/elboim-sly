/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPath
import Mathlib

/-!
# Counting the jumps of a path

Paths (a): `n_s` is measurable.

Proof route. A right-continuous path with no discontinuity in `(x, y]` is constant on `[x, y]`
(`const_of_no_disc`); with exactly one it differs at the two ends. Hence for a fine dyadic grid of
`(0, s]` the number of grid cells on which the path changes value is the number of jumps; the
grid counts are measurable, and an eventually constant sequence of `ℕ`-valued maps has a measurable
limit.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*}

/-- A right-continuous path with no discontinuity in `(x, y]` is constant on `[x, y]`. -/
theorem const_of_no_disc {f : ℝ≥0 → V} (rc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s) {x y : ℝ≥0}
    (hxy : x ≤ y) (h : ∀ s ∈ Ioc x y, s ∉ CDisc f) : ∀ u ∈ Icc x y, f u = f x := by
  set S : Set ℝ≥0 := {u | u ∈ Icc x y ∧ ∀ v ∈ Icc x u, f v = f x} with hS
  have hxS : x ∈ S := ⟨⟨le_rfl, hxy⟩, fun v hv => by rw [le_antisymm hv.2 hv.1]⟩
  have hbdd : BddAbove S := ⟨y, fun u hu => hu.1.2⟩
  set s0 := sSup S with hs0
  have hxs0 : x ≤ s0 := le_csSup hbdd hxS
  have hs0y : s0 ≤ y := csSup_le ⟨x, hxS⟩ fun u hu => hu.1.2
  have hbelow : ∀ v, x ≤ v → v < s0 → f v = f x := by
    intro v hxv hv
    obtain ⟨u, huS, hvu⟩ := exists_lt_of_lt_csSup ⟨x, hxS⟩ hv
    exact huS.2 v ⟨hxv, hvu.le⟩
  have hfs0 : f s0 = f x := by
    rcases hxs0.lt_or_eq with hxlt | hxeq
    · have hnd := h s0 ⟨hxlt, hs0y⟩
      simp only [CDisc, Set.mem_ofPred_eq, not_and, not_not] at hnd
      have hev := hnd (lt_of_le_of_lt bot_le hxlt)
      have hev2 : ∀ᶠ u in 𝓝[<] s0, f u = f x := by
        filter_upwards [Ioo_mem_nhdsLT hxlt] with u hu using hbelow u hu.1.le hu.2
      have : (𝓝[<] s0).NeBot := nhdsLT_neBot_of_exists_lt ⟨x, hxlt⟩
      obtain ⟨u, hu1, hu2⟩ := (hev.and hev2).exists
      rw [← hu1, hu2]
    · rw [← hxeq]
  have hs0S : s0 ∈ S := by
    refine ⟨⟨hxs0, hs0y⟩, fun v hv => ?_⟩
    rcases hv.2.lt_or_eq with hlt | heq
    · exact hbelow v hv.1 hlt
    · rw [heq]; exact hfs0
  have hs0eq : s0 = y := by
    by_contra hne
    have hlt : s0 < y := lt_of_le_of_ne hs0y hne
    obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (rc s0)
    obtain ⟨w, hw1, hw2⟩ := exists_between (lt_min (show s0 < u' from hu') hlt)
    have hwS : w ∈ S := by
      refine ⟨⟨hxs0.trans hw1.le, hw2.le.trans (min_le_right _ _)⟩, fun v hv => ?_⟩
      rcases le_or_gt v s0 with hv0 | hv0
      · exact hs0S.2 v ⟨hv.1, hv0⟩
      · rw [hsub ⟨hv0.le, lt_of_le_of_lt hv.2 (hw2.trans_le (min_le_left _ _))⟩, hfs0]
    exact absurd (le_csSup hbdd hwS) (not_le.mpr hw1)
  intro u hu
  rw [hs0eq] at hs0S
  exact hs0S.2 u hu

theorem eq_of_no_disc {f : ℝ≥0 → V} (rc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s) {x y : ℝ≥0}
    (hxy : x ≤ y) (h : ∀ s ∈ Ioc x y, s ∉ CDisc f) : f y = f x :=
  const_of_no_disc rc hxy h y ⟨hxy, le_rfl⟩

/-- Exactly one discontinuity in `(x, y]` makes `f x ≠ f y`. -/
theorem ne_of_one_disc {f : ℝ≥0 → V} (rc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s) {x y r : ℝ≥0}
    (hxr : x < r) (hry : r ≤ y) (hr : r ∈ CDisc f)
    (hother : ∀ s ∈ Ioc x y, s ∈ CDisc f → s = r) : f x ≠ f y := by
  have h1 : ∀ u, x ≤ u → u < r → f u = f x := by
    intro u hxu hur
    refine const_of_no_disc rc hxu (fun s hs hd => ?_) u ⟨hxu, le_rfl⟩
    have := hother s ⟨lt_of_lt_of_le hs.1 le_rfl, hs.2.trans (hur.le.trans hry)⟩ hd
    exact absurd (this ▸ hs.2) (not_le.mpr hur)
  have h2 : f r ≠ f x := by
    intro heq
    apply hr.2
    have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨x, hxr⟩
    filter_upwards [Ioo_mem_nhdsLT hxr] with u hu
    rw [h1 u hu.1.le hu.2, heq]
  have h3 : f y = f r := by
    refine eq_of_no_disc rc hry (fun s hs hd => ?_)
    exact absurd (hother s ⟨hxr.trans hs.1, hs.2⟩ hd) (ne_of_gt hs.1)
  rw [h3]
  exact h2.symm

/-- The grid points `s j / N`. -/
noncomputable def gpt (s : ℝ≥0) (N j : ℕ) : ℝ≥0 := s * j / N

theorem coe_gpt (s : ℝ≥0) (N j : ℕ) : (gpt s N j : ℝ) = (s : ℝ) * j / N := by
  simp [gpt]

/-- The cell index of a point. -/
noncomputable def cellIdx (s : ℝ≥0) (N : ℕ) (r : ℝ≥0) : ℕ := ⌈(r : ℝ) * N / s⌉₊ - 1

theorem cell_iff {s r : ℝ≥0} (hs : 0 < s) (hr : 0 < r) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (gpt s N j < r ∧ r ≤ gpt s N (j + 1)) ↔ cellIdx s N r = j := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < (r : ℝ) * N / s := by positivity
  have hc : 1 ≤ ⌈(r : ℝ) * N / s⌉₊ := Nat.ceil_pos.mpr hx
  unfold cellIdx
  rw [← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, coe_gpt, coe_gpt]
  have e1 : (s : ℝ) * j / N < r ↔ (j : ℝ) < r * N / s := by
    rw [div_lt_iff₀ hNr, lt_div_iff₀ hsr]; constructor <;> intro h <;> nlinarith
  have e2 : (r : ℝ) ≤ s * ((j + 1 : ℕ) : ℝ) / N ↔ (r : ℝ) * N / s ≤ ((j + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hNr, div_le_iff₀ hsr]; constructor <;> intro h <;> nlinarith
  rw [e1, e2]
  have : ⌈(r : ℝ) * N / s⌉₊ - 1 = j ↔ ⌈(r : ℝ) * N / s⌉₊ = j + 1 := by omega
  rw [this, Nat.ceil_eq_iff (by omega)]
  simp

open Classical in
/-- The number of grid cells on which the path changes value. -/
noncomputable def gcount (f : ℝ≥0 → V) (s : ℝ≥0) (m : ℕ) : ℕ :=
  ((Finset.range (2 ^ m)).filter fun j => f (gpt s (2 ^ m) j) ≠ f (gpt s (2 ^ m) (j + 1))).card

theorem gcount_eq {f : ℝ≥0 → V} (rc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s) {s : ℝ≥0} (hs : 0 < s)
    {m : ℕ} (hD : (CDisc f ∩ Iic s).Finite)
    (hmesh : ∀ r ∈ CDisc f ∩ Iic s, ∀ r' ∈ CDisc f ∩ Iic s, r < r' →
      (s : ℝ) / (2 ^ m : ℕ) < (r' : ℝ) - r) :
    gcount f s m = (CDisc f ∩ Iic s).ncard := by
  classical
  set N := 2 ^ m with hNdef
  have hN : 0 < N := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Set.ncard_eq_toFinset_card _ hD]
  set Df := hD.toFinset
  have hmemD : ∀ r, r ∈ Df ↔ r ∈ CDisc f ∩ Iic s := fun r => hD.mem_toFinset
  have hstep : ∀ j : ℕ, ((gpt s N (j + 1) : ℝ≥0) : ℝ) - gpt s N j = s / N := by
    intro j; rw [coe_gpt, coe_gpt]; push_cast; ring
  have hinj : Set.InjOn (cellIdx s N) (Df : Set ℝ≥0) := by
    intro r hr r' hr' heq
    by_contra hne
    wlog hlt : r < r' generalizing r r'
    · exact this hr' hr heq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    have hr0 : 0 < r := ((hmemD r).mp hr).1.1
    have hr0' : 0 < r' := ((hmemD r').mp hr').1.1
    have c1 := (cell_iff hs hr0 hN (cellIdx s N r)).mpr rfl
    have c2 := (cell_iff hs hr0' hN (cellIdx s N r)).mpr heq.symm
    have := hmesh r ((hmemD r).mp hr) r' ((hmemD r').mp hr') hlt
    have a1 : ((gpt s N (cellIdx s N r) : ℝ≥0) : ℝ) < r := by exact_mod_cast c1.1
    have a2 : (r' : ℝ) ≤ ((gpt s N (cellIdx s N r + 1) : ℝ≥0) : ℝ) := by exact_mod_cast c2.2
    have := hstep (cellIdx s N r)
    linarith
  have himg : (Finset.range N).filter (fun j => f (gpt s N j) ≠ f (gpt s N (j + 1))) =
      Df.image (cellIdx s N) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hne⟩
      by_contra hno
      push Not at hno
      apply hne
      refine (eq_of_no_disc rc (x := gpt s N j) (y := gpt s N (j + 1)) ?_ ?_).symm
      · rw [← NNReal.coe_le_coe]; rw [coe_gpt, coe_gpt]
        push_cast; apply div_le_div_of_nonneg_right _ hNr.le
        nlinarith [s.2]
      · intro r hr hd
        have hrs : r ≤ s := by
          refine hr.2.trans ?_
          rw [← NNReal.coe_le_coe, coe_gpt]
          have : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
          rw [div_le_iff₀ hNr]; nlinarith [s.2]
        have hrD : r ∈ Df := (hmemD r).mpr ⟨hd, hrs⟩
        exact hno r hrD ((cell_iff hs hd.1 hN j).mp ⟨hr.1, hr.2⟩)
    · rintro ⟨r, hr, rfl⟩
      have hrD := (hmemD r).mp hr
      have hr0 : 0 < r := hrD.1.1
      have hrs : r ≤ s := hrD.2
      have hc := (cell_iff hs hr0 hN (cellIdx s N r)).mpr rfl
      have hjN : cellIdx s N r < N := by
        unfold cellIdx
        have : ⌈(r : ℝ) * N / s⌉₊ ≤ N := by
          apply Nat.ceil_le.mpr
          rw [div_le_iff₀ (by exact_mod_cast hs)]
          have : (r : ℝ) ≤ s := by exact_mod_cast hrs
          nlinarith
        omega
      refine ⟨hjN, ne_of_one_disc rc (r := r) hc.1 hc.2 hrD.1 (fun s' hs' hd => ?_)⟩
      have hs'le : s' ≤ s := by
        refine hs'.2.trans ?_
        rw [← NNReal.coe_le_coe, coe_gpt]
        have : ((cellIdx s N r + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hjN
        rw [div_le_iff₀ hNr]; nlinarith [s.2]
      by_contra hne
      have hs'D : s' ∈ CDisc f ∩ Iic s := ⟨hd, hs'le⟩
      have hb1 : ((gpt s N (cellIdx s N r) : ℝ≥0) : ℝ) < s' := by exact_mod_cast hs'.1
      have hb2 : (s' : ℝ) ≤ ((gpt s N (cellIdx s N r + 1) : ℝ≥0) : ℝ) := by exact_mod_cast hs'.2
      have ha1 : ((gpt s N (cellIdx s N r) : ℝ≥0) : ℝ) < r := by exact_mod_cast hc.1
      have ha2 : (r : ℝ) ≤ ((gpt s N (cellIdx s N r + 1) : ℝ≥0) : ℝ) := by exact_mod_cast hc.2
      have hst := hstep (cellIdx s N r)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hmesh s' hs'D r hrD hlt; linarith
      · have := hmesh r hrD s' hs'D hlt; linarith
  unfold gcount
  rw [himg, Finset.card_image_of_injOn hinj]

theorem eventually_mesh {s : ℝ≥0} {D : Set ℝ≥0} (hD : D.Finite) :
    ∀ᶠ m : ℕ in atTop, ∀ r ∈ D, ∀ r' ∈ D, r < r' → (s : ℝ) / (2 ^ m : ℕ) < (r' : ℝ) - r := by
  have hT : Tendsto (fun m : ℕ => (s : ℝ) / ((2 ^ m : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (s : ℝ)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
  rw [Filter.eventually_all_finite hD]
  intro r hr
  rw [Filter.eventually_all_finite hD]
  intro r' hr'
  by_cases hlt : r < r'
  · have : (0 : ℝ) < (r' : ℝ) - r := by
      have : (r : ℝ) < r' := by exact_mod_cast hlt
      linarith
    filter_upwards [hT.eventually_lt_const this] with m hm _ using hm
  · exact Filter.Eventually.of_forall fun m h => absurd h hlt

/-- The number of discontinuities in `(0, s]`. -/
noncomputable def CPath.cnt {V : Type*} (p : CPath V) (s : ℝ≥0) : ℕ :=
  (CDisc p.fn ∩ Iic s).ncard

theorem eventually_gcount (p : CPath V) (s : ℝ≥0) :
    ∀ᶠ m : ℕ in atTop, gcount p.fn s m = p.cnt s := by
  rcases eq_or_ne s 0 with h0 | hs0
  · subst h0
    have : CDisc p.fn ∩ Iic 0 = ∅ := by
      ext r; simp only [CDisc, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2; exact absurd h2 (not_le.mpr h1.1)
    refine Filter.Eventually.of_forall fun m => ?_
    simp only [CPath.cnt, this, Set.ncard_empty, gcount, gpt, zero_mul, zero_div, ne_eq,
      not_true_eq_false, Finset.filter_false, Finset.card_empty]
  · have hs : 0 < s := pos_iff_ne_zero.mpr hs0
    filter_upwards [eventually_mesh (s := s) (p.fin s)] with m hm
    exact gcount_eq p.rc hs (p.fin s) hm

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

theorem measurable_gcount (s : ℝ≥0) (m : ℕ) : Measurable (fun p : CPath V => gcount p.fn s m) := by
  classical
  have : (fun p : CPath V => gcount p.fn s m) = fun p =>
      ∑ j ∈ Finset.range (2 ^ m), if p.fn (gpt s (2 ^ m) j) ≠ p.fn (gpt s (2 ^ m) (j + 1))
        then 1 else 0 := by
    funext p; simp [gcount, Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact Measurable.ite (measurableSet_eq_fun (CPath.measurable_eval _)
    (CPath.measurable_eval _)).compl measurable_const measurable_const

theorem CPath.measurable_cnt (s : ℝ≥0) : Measurable (fun p : CPath V => p.cnt s) := by
  refine measurable_of_tendsto_metrizable' (f := fun m (p : CPath V) => gcount p.fn s m) atTop
    (fun m => measurable_gcount s m) (tendsto_pi_nhds.mpr fun p => ?_)
  exact tendsto_nhds_of_eventually_eq (eventually_gcount p s)

end ElboimSly.Cyclic

end
