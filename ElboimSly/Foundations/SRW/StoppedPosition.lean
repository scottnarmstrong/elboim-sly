/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Freeze
public import Mathlib

/-!
# The stopped position is `ℱ_T`-measurable

Hitting times and stopped positions (b).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω} {T : Ω → WithTop ℝ≥0}

theorem IsRegularPath.stop {γ : PathSpace d} (hγ : IsRegularPath γ) (c : ℝ≥0) :
    IsRegularPath fun s => γ (min s c) := by
  intro t
  rcases le_or_gt c t with hct | hct
  · refine ⟨1, one_pos, fun s hs _ => ?_⟩
    show γ (min s c) = γ (min t c)
    rw [min_eq_right (hct.trans hs), min_eq_right hct]
  · obtain ⟨δ, hδ, h⟩ := hγ t
    refine ⟨min δ (c - t), lt_min hδ (tsub_pos_of_lt hct), fun s hs hs2 => ?_⟩
    have h1 : s < c := by
      have h3 : t + min δ (c - t) ≤ t + (c - t) := by gcongr; exact min_le_right _ _
      have := lt_of_lt_of_le hs2 h3
      rwa [add_tsub_cancel_of_le hct.le] at this
    have h2 : t + min δ (c - t) ≤ t + δ := by gcongr; exact min_le_left _ _
    show γ (min s c) = γ (min t c)
    rw [min_eq_left h1.le, min_eq_left hct.le]
    exact h s hs (lt_of_lt_of_le hs2 h2)

/-- Hitting times and stopped positions (b): `Z(T) 1_{T < ∞}` is `ℱ_T`-measurable. -/
theorem IsAdmissible.measurable_stopped_position (hF : IsAdmissible P Z F)
    (hreg : ∀ ω, IsRegularPath (Z ω)) (hT : IsStoppingTime hF.filtration T) :
    Measurable[hT.measurableSpace] (fun ω => if T ω = ⊤ then (0 : Fin d → ℤ)
      else Z ω (stopReal T ω)) := by
  classical
  intro U _
  -- the preimage restricted to `{T ≤ i}` lies in `F i`
  have hi : ∀ i : ℝ≥0, MeasurableSet[F i]
      ({ω | (if T ω = ⊤ then (0 : Fin d → ℤ) else Z ω (stopReal T ω)) ∈ U} ∩
        {ω | T ω ≤ (i : WithTop ℝ≥0)}) := by
    intro i
    have hmeas : Measurable[F i] fun ω => Z ω (stopMin T i ω) := by
      have hcoord : ∀ s, Measurable[F i] fun ω => Z ω (min s i) := fun s =>
        hF.adapted (min s i) i (min_le_right _ _)
      have := @measurable_eval_regular d Ω (F i) (fun ω s => Z ω (min s i)) hcoord
        (fun ω => (hreg ω).stop i) (stopMin T i) (hT.measurable_stopMin i)
      have e : (fun ω => Z ω (min (stopMin T i ω) i)) = fun ω => Z ω (stopMin T i ω) := by
        funext ω
        simp [stopMin]
      simpa only [e] using this
    have hset : MeasurableSet[F i] ({ω | Z ω (stopMin T i ω) ∈ U} ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)}) :=
      (hmeas (MeasurableSet.of_discrete (s := U))).inter (hT i)
    convert hset using 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hne : T ω ≠ ⊤ := fun h => by rw [h] at h2; exact WithTop.coe_ne_top (top_le_iff.1 h2)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
      rw [ite_eq_right hne] at h1
      have hri : r ≤ i := by rw [← hr] at h2; exact WithTop.coe_le_coe.1 h2
      have : stopMin T i ω = stopReal T ω := by
        unfold stopMin stopReal; rw [← hr]; exact min_eq_left hri
      rwa [this]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hne : T ω ≠ ⊤ := fun h => by rw [h] at h2; exact WithTop.coe_ne_top (top_le_iff.1 h2)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
      rw [ite_eq_right hne]
      have hri : r ≤ i := by rw [← hr] at h2; exact WithTop.coe_le_coe.1 h2
      have : stopMin T i ω = stopReal T ω := by
        unfold stopMin stopReal; rw [← hr]; exact min_eq_left hri
      rwa [this] at h1
  -- assemble the `ℱ_T`-measurability
  have hmT : MeasurableSet {ω | T ω = ⊤} := hT.measurableSet_top

  have hdecomp : {ω | (if T ω = ⊤ then (0 : Fin d → ℤ) else Z ω (stopReal T ω)) ∈ U} =
      (⋃ n : ℕ, {ω | (if T ω = ⊤ then (0 : Fin d → ℤ) else Z ω (stopReal T ω)) ∈ U} ∩
        {ω | T ω ≤ (n : ℝ≥0)}) ∪
      ({ω | T ω = ⊤} ∩ {_ω | (0 : Fin d → ℤ) ∈ U}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff]
    by_cases h : T ω = ⊤
    · simp [h]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h
      obtain ⟨n, hn⟩ := exists_nat_ge r
      constructor
      · intro h1; left; exact ⟨n, h1, by rw [← hr]; exact WithTop.coe_le_coe.2 hn⟩
      · rintro (⟨n, h1, _⟩ | ⟨h2, _⟩)
        · exact h1
        · exact absurd h2 h
  have hfirst : @MeasurableSet Ω (⨆ t, F t)
      {ω | (if T ω = ⊤ then (0 : Fin d → ℤ) else Z ω (stopReal T ω)) ∈ U} := by
    let : MeasurableSpace Ω := ⨆ t, F t
    have hle : ∀ (n : ℕ) (S : Set Ω), MeasurableSet[F n] S → MeasurableSet S :=
      fun n S h => le_iSup F (n : ℝ≥0) S h
    rw [hdecomp]
    refine MeasurableSet.union (MeasurableSet.iUnion fun n : ℕ => hle n _ (hi n)) ?_
    by_cases h0 : (0 : Fin d → ℤ) ∈ U
    · have e1 : {ω | T ω = ⊤} ∩ {_ω | (0 : Fin d → ℤ) ∈ U} = {ω | T ω = ⊤} := by
        ext ω; simp [h0]
      rw [e1]
      have e2 : {ω | T ω = ⊤} = (⋃ n : ℕ, {ω | T ω ≤ (n : ℝ≥0)})ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists]
        constructor
        · intro h n hn; rw [h] at hn; exact WithTop.coe_ne_top (top_le_iff.1 hn)
        · intro h
          by_contra hne
          obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
          obtain ⟨n, hn⟩ := exists_nat_ge a
          exact h n (by rw [← ha]; exact WithTop.coe_le_coe.2 hn)
      rw [e2]
      exact (MeasurableSet.iUnion fun n : ℕ => hle n _ (hT n)).compl
    · have e1 : {ω | T ω = ⊤} ∩ {_ω | (0 : Fin d → ℤ) ∈ U} = ∅ := by
        ext ω; simp [h0]
      rw [e1]; exact MeasurableSet.empty
  exact ⟨hfirst, fun i => hi i⟩

end SRW
end ElboimSly
