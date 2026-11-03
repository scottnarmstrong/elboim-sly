/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.SrwLaw
public import Mathlib

/-!
# Countable reduction of path events

Countable reduction of path events (i)-(iv).

Rational times are `ratNN r = max r 0` for `r : ℚ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

/-- The nonnegative real attached to a rational. -/
noncomputable def ratNN (r : ℚ) : ℝ≥0 := Real.toNNReal r

theorem exists_ratNN_btwn {x y : ℝ≥0} (h : x < y) : ∃ r : ℚ, x < ratNN r ∧ ratNN r < y := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 h)
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg x).trans hq1.le
  refine ⟨q, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]; unfold ratNN; rw [Real.coe_toNNReal _ hq0]; exact hq1
  · rw [← NNReal.coe_lt_coe]; unfold ratNN; rw [Real.coe_toNNReal _ hq0]; exact hq2

variable {d : ℕ} {γ : PathSpace d}

/-- (i) of countable reduction of path events. -/
theorem IsRegularPath.exists_Icc_iff (hγ : IsRegularPath γ) (K : Set (Fin d → ℤ)) {a b : ℝ≥0}
    (hab : a ≤ b) :
    (∃ s, a ≤ s ∧ s ≤ b ∧ γ s ∈ K) ↔
      (γ b ∈ K ∨ ∃ r : ℚ, a ≤ ratNN r ∧ ratNN r < b ∧ γ (ratNN r) ∈ K) := by
  constructor
  · rintro ⟨s, hs1, hs2, hs⟩
    rcases hs2.eq_or_lt with rfl | hlt
    · exact Or.inl hs
    · right
      obtain ⟨δ, hδ, h⟩ := hγ s
      obtain ⟨r, hr1, hr2⟩ := exists_ratNN_btwn (lt_min hlt (lt_add_of_pos_right s hδ))
      refine ⟨r, hs1.trans hr1.le, hr2.trans_le (min_le_left _ _), ?_⟩
      rw [h _ hr1.le (hr2.trans_le (min_le_right _ _))]
      exact hs
  · rintro (h | ⟨r, h1, h2, h3⟩)
    · exact ⟨b, hab, le_rfl, h⟩
    · exact ⟨ratNN r, h1, h2.le, h3⟩

/-- (ii) of countable reduction of path events. -/
theorem IsRegularPath.exists_Ici_iff (hγ : IsRegularPath γ) (K : Set (Fin d → ℤ)) (a : ℝ≥0) :
    (∃ s, a ≤ s ∧ γ s ∈ K) ↔ ∃ r : ℚ, a ≤ ratNN r ∧ γ (ratNN r) ∈ K := by
  constructor
  · rintro ⟨s, hs1, hs⟩
    obtain ⟨δ, hδ, h⟩ := hγ s
    obtain ⟨r, hr1, hr2⟩ := exists_ratNN_btwn (lt_add_of_pos_right s hδ)
    refine ⟨r, hs1.trans hr1.le, ?_⟩
    rw [h _ hr1.le hr2]
    exact hs
  · rintro ⟨r, h1, h2⟩
    exact ⟨ratNN r, h1, h2⟩

/-- (iii) of countable reduction of path events. -/
theorem IsRegularPath.exists_pair_iff (hγ : IsRegularPath γ) (G : (Fin d → ℤ) → (Fin d → ℤ) → Prop)
    {a b h : ℝ≥0} (hab : a ≤ b) :
    (∃ s s', a ≤ s ∧ s ≤ s' ∧ s' ≤ b ∧ s' - s ≤ h ∧ G (γ s) (γ s')) ↔
      ∃ q q' : ℝ≥0, (q ∈ range ratNN ∨ q = b) ∧ (q' ∈ range ratNN ∨ q' = b) ∧
        a ≤ q ∧ q ≤ q' ∧ q' ≤ b ∧ q' - q ≤ h ∧ G (γ q) (γ q') := by
  constructor
  · rintro ⟨s, s', has, hss', hsb, hh, hG⟩
    obtain ⟨δ, hδ, hconst⟩ := hγ s
    obtain ⟨δ', hδ', hconst'⟩ := hγ s'
    rcases hss'.eq_or_lt with heq | hlt
    · -- `s = s'`
      subst heq
      rcases hsb.eq_or_lt with rfl | hlt2
      · exact ⟨s, s, Or.inr rfl, Or.inr rfl, has, le_rfl, le_rfl, by simp, hG⟩
      · obtain ⟨r, hr1, hr2⟩ := exists_ratNN_btwn (lt_min hlt2 (lt_add_of_pos_right s hδ))
        have hq : γ (ratNN r) = γ s := hconst _ hr1.le (hr2.trans_le (min_le_right _ _))
        exact ⟨ratNN r, ratNN r, Or.inl ⟨r, rfl⟩, Or.inl ⟨r, rfl⟩, has.trans hr1.le, le_rfl,
          (hr2.trans_le (min_le_left _ _)).le, by simp, by rw [hq]; exact hG⟩
    · -- `s < s'`
      rcases hsb.eq_or_lt with rfl | hlt2
      · -- `s' = b`
        obtain ⟨r, hr1, hr2⟩ := exists_ratNN_btwn
          (lt_min hlt (lt_add_of_pos_right s hδ))
        have hq : γ (ratNN r) = γ s := hconst _ hr1.le (hr2.trans_le (min_le_right _ _))
        refine ⟨ratNN r, s', Or.inl ⟨r, rfl⟩, Or.inr rfl, has.trans hr1.le,
          (hr2.trans_le (min_le_left _ _)).le, le_rfl, ?_, by rw [hq]; exact hG⟩
        calc s' - ratNN r ≤ s' - s := tsub_le_tsub_left hr1.le _
          _ ≤ h := hh
      · -- `s' < b`
        set ε : ℝ≥0 := min (min δ δ') (min (s' - s) (b - s')) with hε
        have hεpos : 0 < ε := lt_min (lt_min hδ hδ') (lt_min (tsub_pos_of_lt hlt)
          (tsub_pos_of_lt hlt2))
        obtain ⟨r', hr'1, hr'2⟩ := exists_ratNN_btwn (lt_add_of_pos_right s' hεpos)
        set η : ℝ≥0 := ratNN r' - s' with hη
        have hq'eq : ratNN r' = s' + η := by
          rw [hη, add_tsub_cancel_of_le hr'1.le]
        have hηε : η < ε := by
          have : s' + η < s' + ε := hq'eq ▸ hr'2
          exact lt_of_add_lt_add_left this
        have hηδ : η < δ := hηε.trans_le ((min_le_left _ _).trans (min_le_left _ _))
        have hηs : η < s' - s := hηε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        have hs_lt : s + η < s' := by
          have : s + η < s + (s' - s) := by gcongr
          rwa [add_tsub_cancel_of_le hlt.le] at this
        obtain ⟨r, hr1, hr2⟩ := exists_ratNN_btwn
          (lt_min hs_lt (show s + η < s + δ by gcongr))
        have hq : γ (ratNN r) = γ s :=
          hconst _ (le_trans (le_self_add) hr1.le) (hr2.trans_le (min_le_right _ _))
        have hq' : γ (ratNN r') = γ s' :=
          hconst' _ hr'1.le (hr'2.trans_le (by
            have : ε ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
            gcongr))
        have hqs' : ratNN r < s' := hr2.trans_le (min_le_left _ _)
        refine ⟨ratNN r, ratNN r', Or.inl ⟨r, rfl⟩, Or.inl ⟨r', rfl⟩,
          has.trans (le_trans (le_self_add) hr1.le), (hqs'.trans_le hr'1.le).le, ?_, ?_,
          by rw [hq, hq']; exact hG⟩
        · have : ε ≤ b - s' := (min_le_right _ _).trans (min_le_right _ _)
          have h5 : s' + ε ≤ b := by
            calc s' + ε ≤ s' + (b - s') := by gcongr
              _ = b := add_tsub_cancel_of_le hlt2.le
          exact (hr'2.trans_le h5).le
        · rw [tsub_le_iff_right]
          have h6 : s' ≤ h + s := tsub_le_iff_right.1 hh
          calc ratNN r' = s' + η := hq'eq
            _ ≤ (h + s) + η := by gcongr
            _ = h + (s + η) := by ring
            _ ≤ h + ratNN r := by gcongr
  · rintro ⟨q, q', -, -, h1, h2, h3, h4, h5⟩
    exact ⟨q, q', h1, h2, h3, h4, h5⟩

/-- (iv) of countable reduction of path events, for a family of predicates whose failure set is right-open. -/
theorem IsRegularPath.forall_Icc_iff (hγ : IsRegularPath γ) (Pc : ℝ≥0 → (Fin d → ℤ) → Prop)
    (hP : ∀ y s, ¬ Pc s y → ∃ ε > 0, ∀ s', s ≤ s' → s' < s + ε → ¬ Pc s' y) {a b : ℝ≥0}
    (hab : a ≤ b) :
    (∀ s, a ≤ s → s ≤ b → Pc s (γ s)) ↔
      (Pc b (γ b) ∧ ∀ r : ℚ, a ≤ ratNN r → ratNN r < b → Pc (ratNN r) (γ (ratNN r))) := by
  constructor
  · intro h
    exact ⟨h b hab le_rfl, fun r h1 h2 => h _ h1 h2.le⟩
  · rintro ⟨hb, hr⟩ s hs1 hs2
    by_contra hns
    rcases hs2.eq_or_lt with rfl | hlt
    · exact hns hb
    · obtain ⟨δ, hδ, hconst⟩ := hγ s
      obtain ⟨ε, hε, hfail⟩ := hP _ _ hns
      obtain ⟨r, hr1, hr2⟩ := exists_ratNN_btwn
        (lt_min hlt (lt_min (lt_add_of_pos_right s hδ) (lt_add_of_pos_right s hε)))
      have h3 : ratNN r < s + δ := hr2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have h4 : ratNN r < s + ε := hr2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have h5 : ratNN r < b := hr2.trans_le (min_le_left _ _)
      have := hr r (hs1.trans hr1.le) h5
      rw [hconst _ hr1.le h3] at this
      exact hfail _ hr1.le h4 this

variable {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → PathSpace d}

theorem measurableSet_exists_Icc (hZm : ∀ s, Measurable fun ω => Z ω s)
    (hreg : ∀ ω, IsRegularPath (Z ω)) (K : Set (Fin d → ℤ)) {a b : ℝ≥0} (hab : a ≤ b) :
    MeasurableSet {ω | ∃ s, a ≤ s ∧ s ≤ b ∧ Z ω s ∈ K} := by
  have : {ω | ∃ s, a ≤ s ∧ s ≤ b ∧ Z ω s ∈ K} = {ω | Z ω b ∈ K} ∪
      ⋃ r : ℚ, {ω | a ≤ ratNN r ∧ ratNN r < b ∧ Z ω (ratNN r) ∈ K} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    exact (hreg ω).exists_Icc_iff K hab
  rw [this]
  refine MeasurableSet.union ((hZm b) (MeasurableSet.of_discrete (s := K))) ?_
  refine MeasurableSet.iUnion fun r => ?_
  by_cases h : a ≤ ratNN r ∧ ratNN r < b
  · have : {ω | a ≤ ratNN r ∧ ratNN r < b ∧ Z ω (ratNN r) ∈ K} = {ω | Z ω (ratNN r) ∈ K} := by
      ext ω; simp [h.1, h.2]
    rw [this]; exact (hZm _) (MeasurableSet.of_discrete (s := K))
  · have : {ω | a ≤ ratNN r ∧ ratNN r < b ∧ Z ω (ratNN r) ∈ K} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨h'.1, h'.2.1⟩
    rw [this]; exact MeasurableSet.empty

end SRW
end ElboimSly
