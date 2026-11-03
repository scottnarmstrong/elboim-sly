/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Stopping
public import Mathlib

/-!
# Dyadic slicing of an event along a stopping time

Strong Markov property (proof by dyadic approximation of the stopping time).

For `A ∈ ℱ_T`, the sets `gset A T m k = A ∩ {t_{k-1} < T ≤ t_k}` with `t_k = k / 2^m` are pairwise
disjoint, `gset A T m k ∈ ℱ_{t_k}`, and their union over `k` is `A ∩ {T < ∞}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The dyadic time `k / 2^m`. -/
noncomputable def dt (m k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ m

theorem dt_mono (m : ℕ) : Monotone (dt m) := fun a b h => by
  unfold dt; gcongr

theorem dt_succ (m k : ℕ) : dt m (k + 1) = dt m k + 1 / 2 ^ m := by
  unfold dt; push_cast; rw [add_div]

/-- `A ∩ {t_{k-1} < T ≤ t_k}`. -/
def gset (A : Set Ω) (T : Ω → WithTop ℝ≥0) (m k : ℕ) : Set Ω :=
  A ∩ {ω | T ω ≤ (dt m k : WithTop ℝ≥0)} ∩
    ⋂ j ∈ Finset.range k, {ω | T ω ≤ (dt m j : WithTop ℝ≥0)}ᶜ

omit mΩ in
theorem mem_gset {A : Set Ω} {T : Ω → WithTop ℝ≥0} {m k : ℕ} {ω : Ω} :
    ω ∈ gset A T m k ↔ ω ∈ A ∧ T ω ≤ (dt m k : WithTop ℝ≥0) ∧
      ∀ j < k, ¬ T ω ≤ (dt m j : WithTop ℝ≥0) := by
  simp [gset, and_assoc]

theorem measurableSet_gset {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime f T) {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) (m k : ℕ) :
    MeasurableSet[f (dt m k)] (gset A T m k) := by
  have h1 : MeasurableSet[f (dt m k)] (A ∩ {ω | T ω ≤ (dt m k : WithTop ℝ≥0)}) := (hA.2 _)
  have h2 : MeasurableSet[f (dt m k)]
      (⋂ j ∈ Finset.range k, {ω | T ω ≤ (dt m j : WithTop ℝ≥0)}ᶜ) := by
    refine Finset.measurableSet_biInter _ fun j hj => ?_
    have hjk : dt m j ≤ dt m k := dt_mono m (Finset.mem_range.1 hj).le
    exact (f.mono hjk _ (hT _)).compl
  exact h1.inter h2

omit mΩ in
theorem pairwise_disjoint_gset (A : Set Ω) (T : Ω → WithTop ℝ≥0) (m : ℕ) :
    Pairwise (Function.onFun Disjoint (gset A T m)) := by
  intro a b hab
  wlog h : a < b generalizing a b
  · exact (this hab.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)).symm
  refine Set.disjoint_left.2 fun ω ha hb => ?_
  rw [mem_gset] at ha hb
  exact hb.2.2 a h ha.2.1

omit mΩ in
theorem iUnion_gset (A : Set Ω) (T : Ω → WithTop ℝ≥0) (m : ℕ) :
    ⋃ k, gset A T m k = A ∩ {ω | T ω < ⊤} := by
  ext ω
  simp only [mem_iUnion, mem_gset, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hA, hk, -⟩
    exact ⟨hA, lt_of_le_of_lt hk (WithTop.coe_lt_top _)⟩
  · rintro ⟨hA, hlt⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hlt.ne
    have hex : ∃ k : ℕ, r ≤ dt m k := by
      obtain ⟨k, hk⟩ := exists_nat_ge (r * 2 ^ m)
      refine ⟨k, ?_⟩
      unfold dt
      rw [le_div_iff₀ (by positivity)]
      exact hk
    classical
    refine ⟨Nat.find hex, hA, ?_, fun j hj => ?_⟩
    · rw [← hr]; exact WithTop.coe_le_coe.2 (Nat.find_spec hex)
    · rw [← hr]
      intro h
      exact Nat.find_min hex hj (WithTop.coe_le_coe.1 h)

omit mΩ in
theorem gset_bounds {A : Set Ω} {T : Ω → WithTop ℝ≥0} {m k : ℕ} {ω : Ω}
    (h : ω ∈ gset A T m k) :
    ω ∈ A ∧ T ω ≠ ⊤ ∧ stopReal T ω ≤ dt m k ∧ dt m k ≤ stopReal T ω + 1 / 2 ^ m := by
  rw [mem_gset] at h
  obtain ⟨hA, hk, hmin⟩ := h
  have hne : T ω ≠ ⊤ := fun h => by
    rw [h] at hk; exact WithTop.coe_ne_top (top_le_iff.1 hk)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
  have hsr : stopReal T ω = r := by unfold stopReal; rw [← hr]; rfl
  rw [hsr]
  refine ⟨hA, hne, by rw [← hr] at hk; exact WithTop.coe_le_coe.1 hk, ?_⟩
  rcases k with _ | k
  · simp [dt]
  · have := hmin k (Nat.lt_succ_self k)
    rw [← hr] at this
    have h2 : dt m k < r := lt_of_not_ge fun h => this (WithTop.coe_le_coe.2 h)
    rw [dt_succ]
    gcongr

end SRW
end ElboimSly
