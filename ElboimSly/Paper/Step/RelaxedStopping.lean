/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.LocIco
public import ElboimSly.Paper.Base.Progressive
public import ElboimSly.Foundations.SRW.Stopping
public import Mathlib

/-!
# First entrance into a locally-`[l, r)` adapted set is a stopping time

Structure of relaxed times; stopping times (d), second sentence: for a stopping time `R` and `U`
adapted and locally of type `[l, r)`, `inf {t > R : t ∈ U}` is a stopping time.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

/-- A set locally of type `[l, r)` contains a right neighbourhood of each of its points. -/
theorem IsLocIco.exists_Ico {U : Set ℝ} (hU : IsLocIco U) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ∈ U) :
    ∃ ε > 0, Ico t (t + ε) ⊆ U := by
  obtain ⟨L, hL, hLe⟩ := hU (t + 1)
  have : t ∈ U ∩ Icc 0 (t + 1) := ⟨ht, ht0, by linarith⟩
  rw [hLe] at this
  obtain ⟨hmem, -⟩ := this
  simp only [mem_iUnion, exists_prop] at hmem
  obtain ⟨p, hp, hpt⟩ := hmem
  refine ⟨min (p.2 - t) 1, lt_min (by linarith [hpt.2]) one_pos, fun x hx => ?_⟩
  have hx' : x ∈ (⋃ p ∈ L, Ico p.1 p.2) ∩ Icc 0 (t + 1) :=
    ⟨mem_iUnion₂.2 ⟨p, hp, ⟨hpt.1.trans hx.1, by
      have := min_le_left (p.2 - t) 1; linarith [hx.2]⟩⟩, ht0.trans hx.1, by
      have := min_le_right (p.2 - t) 1; linarith [hx.2]⟩
  rw [← hLe] at hx'
  exact hx'.1

/-- A set locally of type `[l, r)` misses a right neighbourhood of each point it misses. -/
theorem IsLocIco.exists_Ico_compl {U : Set ℝ} (hU : IsLocIco U) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ∉ U) : ∃ ε > 0, ∀ x ∈ Ico t (t + ε), x ∉ U := by
  classical
  obtain ⟨L, hL, hLe⟩ := hU (t + 1)
  have key : ∀ L' : Finset (ℝ × ℝ), (∀ p ∈ L', p.1 < p.2) → (∀ p ∈ L', t ∉ Ico p.1 p.2) →
      ∃ ε > 0, ε ≤ 1 ∧ ∀ p ∈ L', ∀ x ∈ Ico t (t + ε), x ∉ Ico p.1 p.2 := by
    intro L'
    induction L' using Finset.induction_on with
    | empty => intro _ _; exact ⟨1, one_pos, le_rfl, by simp⟩
    | insert q L'' hq ih =>
      intro h1 h2
      obtain ⟨ε, hε, hε1, hall⟩ := ih (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
        (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
      have hq2 := h2 q (Finset.mem_insert_self _ _)
      by_cases hq1 : t < q.1
      · refine ⟨min ε (q.1 - t), lt_min hε (by linarith), (min_le_left _ _).trans hε1, ?_⟩
        intro p hp x hx
        rcases Finset.mem_insert.1 hp with rfl | hp
        · intro hxp
          have := min_le_right ε (p.1 - t)
          linarith [hx.2, hxp.1]
        · exact hall p hp x ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith [min_le_left ε (q.1 - t)])⟩
      · refine ⟨ε, hε, hε1, ?_⟩
        intro p hp x hx
        rcases Finset.mem_insert.1 hp with rfl | hp
        · intro hxp
          apply hq2
          have hqt : p.1 ≤ t := not_lt.1 hq1
          refine ⟨hqt, ?_⟩
          by_contra hh
          have hh' : p.2 ≤ t := not_lt.1 hh
          have := hxp.2
          have := hx.1
          linarith
        · exact hall p hp x hx
  have hnot : ∀ p ∈ L, t ∉ Ico p.1 p.2 := by
    intro p hp hpt
    apply ht
    have : t ∈ (⋃ p ∈ L, Ico p.1 p.2) ∩ Icc 0 (t + 1) :=
      ⟨mem_iUnion₂.2 ⟨p, hp, hpt⟩, ht0, by linarith⟩
    rw [← hLe] at this
    exact this.1
  obtain ⟨ε, hε, hε1, hall⟩ := key L hL hnot
  refine ⟨ε, hε, fun x hx hxU => ?_⟩
  have : x ∈ U ∩ Icc 0 (t + 1) := ⟨hxU, ht0.trans hx.1, by linarith [hx.2]⟩
  rw [hLe] at this
  obtain ⟨hmem, -⟩ := this
  simp only [mem_iUnion, exists_prop] at hmem
  obtain ⟨p, hp, hxp⟩ := hmem
  exact hall p hp x hx hxp

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `inf {t > R : t ∈ U}` (`:= ⊤` if there is none). -/
noncomputable def stepNextIn (U : Ω → Set ℝ) (R : Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (u : ℝ≥0) (_ : (u : ℝ) ∈ U ω ∧ R ω < u), (u : WithTop ℝ≥0)

theorem stepNextIn_le_iff {U : Set ℝ} (hU : IsLocIco U) (R : WithTop ℝ≥0) (t : ℝ≥0) :
    (⨅ (u : ℝ≥0) (_ : (u : ℝ) ∈ U ∧ R < u), (u : WithTop ℝ≥0)) ≤ t ↔
      ∃ u : ℝ≥0, (u : ℝ) ∈ U ∧ R ≤ u ∧ u ≤ t := by
  constructor
  · intro h
    by_cases hS : ∃ u : ℝ≥0, (u : ℝ) ∈ U ∧ R < u
    · obtain ⟨u₁, hu₁U, hRu₁⟩ := hS
      obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hRu₁)
      have hru₁ : (r : ℝ) < u₁ := by exact_mod_cast WithTop.coe_lt_coe.1 hRu₁
      obtain ⟨mm, hmU, hrm, hlow, -⟩ := hU.sInf_eq_min r.2 ⟨(u₁ : ℝ), hu₁U, hru₁⟩
      have hm0 : 0 ≤ mm := r.2.trans hrm
      refine ⟨mm.toNNReal, by rwa [Real.coe_toNNReal _ hm0], ?_, ?_⟩
      · exact WithTop.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hm0]; exact hrm)
      · have h1 : ((mm.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ⨅ (u : ℝ≥0) (_ : (u : ℝ) ∈ U ∧
            (r : WithTop ℝ≥0) < u), (u : WithTop ℝ≥0) := by
          refine le_iInf₂ fun u hu => ?_
          have hru : (r : ℝ) < u := by exact_mod_cast WithTop.coe_lt_coe.1 hu.2
          exact WithTop.coe_le_coe.2 (by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hm0]; exact hlow _ hu.1 hru.le)
        exact WithTop.coe_le_coe.1 (h1.trans h)
    · exfalso
      have : (⨅ (u : ℝ≥0) (_ : (u : ℝ) ∈ U ∧ R < u), (u : WithTop ℝ≥0)) = ⊤ := by
        simp only [iInf_eq_top]
        intro u hu
        exact absurd ⟨u, hu⟩ hS
      rw [this] at h
      exact absurd h (WithTop.not_top_le_coe _)
  · rintro ⟨u, hu, hRu, hut⟩
    refine le_trans ?_ (WithTop.coe_le_coe.2 hut)
    rcases hRu.lt_or_eq with hlt | heq
    · exact iInf₂_le_of_le u ⟨hu, hlt⟩ le_rfl
    · obtain ⟨ε, hε, hsub⟩ := hU.exists_Ico u.2 hu
      refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      cases a with
      | top => exact le_top
      | coe v =>
        have huv : u < v := WithTop.coe_lt_coe.1 ha
        have hεR : (0 : ℝ) < ε := hε
        have huvR : (u : ℝ) < v := by exact_mod_cast huv
        obtain ⟨δ, hδpos, hδ1, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε / 2 ∧ δ ≤ ((v : ℝ) - u) / 2 :=
          ⟨min (ε / 2) (((v : ℝ) - u) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
            min_le_right _ _⟩
        obtain ⟨e, heR⟩ : ∃ e : ℝ≥0, (e : ℝ) = δ := ⟨δ.toNNReal, Real.coe_toNNReal _ hδpos.le⟩
        have hepos : 0 < e := by
          rw [← NNReal.coe_pos, heR]; exact hδpos
        have hue : u + e < v := by
          rw [← NNReal.coe_lt_coe, NNReal.coe_add, heR]; linarith
        have hmem : ((u + e : ℝ≥0) : ℝ) ∈ U := by
          have h1 : (u : ℝ) ≤ (u : ℝ) + δ := by linarith
          have h2 : (u : ℝ) + δ < (u : ℝ) + ε := by linarith
          rw [NNReal.coe_add, heR]
          exact hsub ⟨h1, h2⟩
        have hlt : R < ((u + e : ℝ≥0) : WithTop ℝ≥0) := by
          rw [heq]; exact WithTop.coe_lt_coe.2 (lt_add_of_pos_right _ hepos)
        exact (iInf₂_le_of_le (u + e) ⟨hmem, hlt⟩ le_rfl).trans (WithTop.coe_le_coe.2 hue.le)

/-- The `ℕ`-valued indicator process of an adapted family. -/
noncomputable def stepIndProc (U : Ω → Set ℝ) (s : ℝ≥0) (ω : Ω) : ℕ := by
  classical exact if (s : ℝ) ∈ U ω then 1 else 0

variable (f : Filtration ℝ≥0 m)

theorem stepIndProc_adapted {U : Ω → Set ℝ}
    (hU : ∀ t : ℝ≥0, MeasurableSet[f t] {ω | (t : ℝ) ∈ U ω}) (t : ℝ≥0) :
    Measurable[f t] (stepIndProc U t) := by
  classical
  refine @measurable_to_countable' ℕ Ω _ _ (f t) _ fun n => ?_
  by_cases h1 : n = 1
  · subst h1
    convert hU t using 1
    ext ω; simp [stepIndProc]
  · by_cases h0 : n = 0
    · subst h0
      convert (hU t).compl using 1
      ext ω; simp [stepIndProc]
    · convert MeasurableSet.empty using 1
      ext ω; simp only [stepIndProc, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      split_ifs <;> omega


theorem stepIndProc_rc {U : Ω → Set ℝ} (hloc : ∀ ω, IsLocIco (U ω)) (ω : Ω) (t : ℝ≥0) :
    ∀ᶠ u in 𝓝[≥] t, stepIndProc U u ω = stepIndProc U t ω := by
  classical
  by_cases ht : (t : ℝ) ∈ U ω
  · obtain ⟨ε, hε, hsub⟩ := (hloc ω).exists_Ico t.2 ht
    refine mem_nhdsGE_iff_exists_Ico_subset.2 ⟨t + ⟨ε, hε.le⟩, ?_, fun u hu => ?_⟩
    · exact lt_add_of_pos_right _ (by exact_mod_cast hε)
    · have hu' : (u : ℝ) ∈ U ω := hsub ⟨by exact_mod_cast hu.1, by
        have h2 : (u : ℝ) < ((t + ⟨ε, hε.le⟩ : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 hu.2
        exact h2⟩
      simp [stepIndProc, hu', ht]
  · obtain ⟨ε, hε, hsub⟩ := (hloc ω).exists_Ico_compl t.2 ht
    refine mem_nhdsGE_iff_exists_Ico_subset.2 ⟨t + ⟨ε, hε.le⟩, ?_, fun u hu => ?_⟩
    · exact lt_add_of_pos_right _ (by exact_mod_cast hε)
    · have hu' : (u : ℝ) ∉ U ω := hsub _ ⟨by exact_mod_cast hu.1, by
        have h2 : (u : ℝ) < ((t + ⟨ε, hε.le⟩ : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 hu.2
        exact h2⟩
      simp [stepIndProc, hu', ht]

end ElboimSly.Paper
