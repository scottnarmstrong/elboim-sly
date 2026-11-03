/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStructure
public import ElboimSly.Paper.Induction.RelaxedMeasWrt
public import ElboimSly.Paper.Base.Progressive
public import Mathlib

/-!
# Relaxed times are adapted

Structure of relaxed times; stopping times (d), first sentence: `1{t ∈ 𝒯}` is `𝒢_t`-measurable.

Paths are indexed by `ℝ≥0`. `stepExt g` is the extension of `g : ℝ≥0 → V` to `ℝ` by `g 0` on the
negative half-line; `IsRelaxedTimeWrt` for `0 ≤ a ≤ t` only reads the path on `[a, t]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- Extension of a path on `ℝ≥0` to `ℝ`. -/
def stepExt {V : Type*} (g : ℝ≥0 → V) : ℝ → V := fun r => g r.toNNReal

/-- `IsRelaxedTimeWrt` only reads the path on `[a, t]`. -/
theorem isRelaxedTimeWrt_congr_le {β : ℝ} (hβ : 0 < β) {w w' : ℝ → Fin d → ℤ} {a t : ℝ}
    (h : ∀ s, 0 ≤ s → s ≤ t → w s = w' s) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    IsRelaxedTimeWrt β w a t ↔ IsRelaxedTimeWrt β w' a t := by
  have hv : visitedSet w a t = visitedSet w' a t :=
    Set.image_congr fun s hs => h s (ha.trans hs.1) hs.2
  have hp : 0 ≤ β ^ (3 * indDelta d) := (Real.rpow_pos_of_pos hβ _).le
  unfold IsRelaxedTimeWrt IsHeavy
  simp only [hv, h t ht le_rfl]
  refine and_congr Iff.rfl (forall_congr' fun s => ?_)
  by_cases hs : a ≤ s
  · simp only [hs, true_implies]
    refine imp_congr_right fun hst => ?_
    have hst' : s ≤ t := by linarith
    rw [h s (ha.trans hs) hst']
  · simp [hs]

/-- Right-continuity of a `ℝ≥0`-indexed path with plateaus gives plateaus of the clipped real
extension `r ↦ g (min r.toNNReal t)`. -/
theorem clip_plateau {V : Type*} {g : ℝ≥0 → V} (hrc : ∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s)
    (t : ℝ≥0) (s : ℝ) :
    ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), g (min s'.toNNReal t) = g (min s.toNNReal t) := by
  by_cases hs : s < 0
  · refine ⟨-s, by linarith, fun s' hs' => ?_⟩
    have h1 : s'.toNNReal = 0 := Real.toNNReal_of_nonpos (by linarith [hs'.2])
    have h2 : s.toNNReal = 0 := Real.toNNReal_of_nonpos hs.le
    rw [h1, h2]
  · push Not at hs
    by_cases hst : (t : ℝ) ≤ s
    · refine ⟨1, one_pos, fun s' hs' => ?_⟩
      have h1 : t ≤ s'.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hs.trans hs'.1)]
        exact hst.trans hs'.1
      have h2 : t ≤ s.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs]; exact hst
      rw [min_eq_right h1, min_eq_right h2]
    · push Not at hst
      obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hrc s.toNNReal)
      refine ⟨(u' : ℝ) - s, by
        have : (s.toNNReal : ℝ) < u' := by exact_mod_cast hu'
        rw [Real.coe_toNNReal _ hs] at this
        linarith, fun s' hs' => ?_⟩
      have hs'0 : 0 ≤ s' := hs.trans hs'.1
      have hxs : min s.toNNReal t = s.toNNReal := min_eq_left (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs]; exact hst.le)
      rw [hxs]
      have hle : s.toNNReal ≤ min s'.toNNReal t :=
        le_min (Real.toNNReal_le_toNNReal hs'.1) (by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs]; exact hst.le)
      have hlt : min s'.toNNReal t < u' := by
        refine lt_of_le_of_lt (min_le_left _ _) ?_
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs'0]
        linarith [hs'.2]
      exact hsub ⟨hle, hlt⟩

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A right-continuous adapted lattice path is jointly measurable in `(ω, r)` on the clipped real
line, with respect to `𝒢_t ⊗ Borel`. -/
theorem measurable_clip_joint (f : Filtration ℝ≥0 m) (w : ℝ≥0 → Ω → Fin d → ℤ)
    (hw : ∀ t, Measurable[f t] (w t)) (hrc : ∀ ω t, ∀ᶠ u in 𝓝[≥] t, w u ω = w t ω) (t : ℝ≥0) :
    @Measurable (Ω × ℝ) _ (@Prod.instMeasurableSpace Ω ℝ (f t) _) _
      (fun p : Ω × ℝ => w (min p.2.toNNReal t) p.1) := by
  let : MeasurableSpace Ω := f t
  have hprog := Base.isStronglyProgressive_of_rc f w hw hrc t
  have hm := hprog.measurable
  have hmap : Measurable fun p : Ω × ℝ =>
      ((⟨min p.2.toNNReal t, min_le_right _ _⟩ : Set.Iic t), p.1) :=
    (Measurable.subtype_mk (measurable_snd.real_toNNReal.min measurable_const)).prodMk
      measurable_fst
  exact hm.comp hmap

/-- Sections of the measurable set of measurability of relaxed times. -/
theorem measurableSet_relaxed_section {Ω' : Type*} [MeasurableSpace Ω'] {β : ℝ} (hβ : 0 < β)
    (W : Ω' → ℝ → Fin d → ℤ) (a : Ω' → ℝ) (t : ℝ)
    (hW : Measurable fun p : Ω' × ℝ => W p.1 p.2) (ha : Measurable a)
    (hrc : ∀ ω s, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), W ω s' = W ω s) :
    MeasurableSet {ω | IsRelaxedTimeWrt β (W ω) (a ω) t} := by
  have : Fact (0 < β) := ⟨hβ⟩
  have ha' : Measurable fun p : Ω' × ℝ => (fun (ω : Ω') (_ : ℝ) => a ω) p.1 p.2 :=
    ha.comp measurable_fst
  have hset := measurableSet_isRelaxedTimeWrt (β := β) (Ω := Ω') W (fun ω _ => a ω) hW ha' hrc
  have hmk : Measurable fun ω : Ω' => (ω, t) := measurable_id.prodMk measurable_const
  exact hmk hset

/-- **Relaxed times are adapted** (structure of relaxed times; stopping times (d), first sentence). If `w` is a
right-continuous adapted lattice path and `α t` is `𝒢_t`-measurable, then
`{ω | t ∈ 𝒯(ω)}` is `𝒢_t`-measurable. -/
theorem measurableSet_stepRelaxed_adapted {β : ℝ} (hβ : 0 < β) (f : Filtration ℝ≥0 m)
    (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0)
    (hw : ∀ t, Measurable[f t] (w t)) (hrc : ∀ ω t, ∀ᶠ u in 𝓝[≥] t, w u ω = w t ω)
    (hα : ∀ t, Measurable[f t] (α t)) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | IsRelaxedTimeWrt β (stepExt fun s => w s ω) (α t ω) t} := by
  have hjoint := measurable_clip_joint f w hw hrc t
  have hsec := @measurableSet_relaxed_section d Ω (f t) β hβ
    (fun ω r => w (min r.toNNReal t) ω) (fun ω => ((α t ω : ℝ≥0) : ℝ)) (t : ℝ) hjoint
    (@Measurable.coe_nnreal_real _ (f t) _ (hα t))
    (fun ω s => by
      obtain ⟨ε, hε, h⟩ := clip_plateau (g := fun u => w u ω) (hrc ω) t s
      exact ⟨ε, hε, h⟩)
  have heq : {ω | IsRelaxedTimeWrt β (stepExt fun s => w s ω) (α t ω) t} =
      {ω | IsRelaxedTimeWrt β (fun r => w (min r.toNNReal t) ω) ((α t ω : ℝ≥0) : ℝ) (t : ℝ)} := by
    ext ω
    refine isRelaxedTimeWrt_congr_le hβ (fun s hs0 hst => ?_) (α t ω).2 t.2
    have h1 : min s.toNNReal t = s.toNNReal := min_eq_left (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hst)
    simp [stepExt, h1]
  rw [heq]
  exact hsec

end ElboimSly.Paper
