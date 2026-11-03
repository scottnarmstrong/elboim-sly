/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.OccTimes
public import ElboimSly.Foundations.Brownian.FarHit
import Mathlib

/-!
# Return times of a Brownian path at integer times

ES22 Lemma 9.3: occupation of a cube at integer times, Step 2. The return times `κ_k` of the visits
`{i : B(i) ∈ D}` are integer-valued stopping times for the Brownian filtration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- The visit predicate of the path `ω`: `i` is a visit iff `B(i) ∈ D`. -/
def visits (B : ℝ≥0 → Ω → (Fin d → ℝ)) (D : Set (Fin d → ℝ)) (ω : Ω) : ℕ → Prop :=
  fun i => B (i : ℝ≥0) ω ∈ D

open Classical in
/-- The `k`-th return time as an extended nonnegative real. -/
noncomputable def occTau (B : ℝ≥0 → Ω → (Fin d → ℝ)) (D : Set (Fin d → ℝ)) (T₀ k : ℕ) (ω : Ω) :
    ℝ≥0∞ :=
  if occTimes T₀ (visits B D ω) k = ⊤ then ⊤ else (((occTimes T₀ (visits B D ω) k).toNat : ℕ) : ℝ≥0∞)

omit mΩ in
lemma occTau_eq_natCast {D : Set (Fin d → ℝ)} {T₀ k : ℕ} {ω : Ω} {j : ℕ} :
    occTau B D T₀ k ω = ((j : ℝ≥0) : ℝ≥0∞) ↔ occTimes T₀ (visits B D ω) k = (j : ℕ∞) := by
  classical
  unfold occTau
  split_ifs with h
  · simp [h]
  · constructor
    · intro h1
      have h2 : (((occTimes T₀ (visits B D ω) k).toNat : ℕ) : ℝ≥0∞) = (j : ℝ≥0∞) := by
        simpa using h1
      have h3 : (occTimes T₀ (visits B D ω) k).toNat = j := by exact_mod_cast h2
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
      rw [← hn] at h3 ⊢
      rw [ENat.toNat_natCast] at h3
      rw [h3]
    · intro h1
      rw [h1]; simp

omit mΩ in
lemma occTau_lt_top_iff {D : Set (Fin d → ℝ)} {T₀ k : ℕ} {ω : Ω} :
    occTau B D T₀ k ω < ⊤ ↔ occTimes T₀ (visits B D ω) k ≠ ⊤ := by
  classical
  unfold occTau
  split_ifs with h
  · simp [h]
  · simp [h]

omit mΩ in
lemma occTau_toNNReal {D : Set (Fin d → ℝ)} {T₀ k : ℕ} {ω : Ω} {n : ℕ}
    (h : occTimes T₀ (visits B D ω) k = (n : ℕ∞)) : (occTau B D T₀ k ω).toNNReal = (n : ℝ≥0) := by
  have := occTau_eq_natCast.2 h
  rw [this]; simp

lemma measurableSet_visit (_hB : ∀ t, Measurable (B t)) {D : Set (Fin d → ℝ)} (hD : MeasurableSet D)
    {i j : ℕ} (hij : i ≤ j) :
    MeasurableSet[bmFiltration B (j : ℝ≥0)] {ω | visits B D ω i} :=
  measurable_bmFiltration (B := B) (s := (i : ℝ≥0)) (a := (j : ℝ≥0)) (by exact_mod_cast hij) hD

lemma measurableSet_nxt (hB : ∀ t, Measurable (B t)) {D : Set (Fin d → ℝ)} (hD : MeasurableSet D)
    (a j : ℕ) :
    MeasurableSet[bmFiltration B (j : ℝ≥0)] {ω | nxt (visits B D ω) a = (j : ℕ∞)} := by
  have e : {ω | nxt (visits B D ω) a = (j : ℕ∞)} =
      {ω | a ≤ j} ∩ ({ω | visits B D ω j} ∩
        ⋂ i : ℕ, ⋂ (_ : a ≤ i ∧ i < j), {ω | ¬ visits B D ω i}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, nxt_eq_iff, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun i hi => h3 i hi.1 hi.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun i h4 h5 => h3 i ⟨h4, h5⟩⟩
  rw [e]
  by_cases haj : a ≤ j
  · have : {ω : Ω | a ≤ j} = Set.univ := by ext; simp [haj]
    rw [this, Set.univ_inter]
    exact @MeasurableSet.inter Ω (bmFiltration B (j : ℝ≥0)) _ _ (measurableSet_visit hB hD le_rfl)
      (@MeasurableSet.iInter Ω ℕ (bmFiltration B (j : ℝ≥0)) _ _ fun i =>
        @MeasurableSet.iInter Ω _ (bmFiltration B (j : ℝ≥0)) _ _ fun hi =>
          (measurableSet_visit hB hD hi.2.le).compl)
  · have : {ω : Ω | a ≤ j} = ∅ := by ext; simp [haj]
    rw [this, Set.empty_inter]
    exact @MeasurableSet.empty Ω (bmFiltration B (j : ℝ≥0))

lemma measurableSet_occTimes (hB : ∀ t, Measurable (B t)) {D : Set (Fin d → ℝ)}
    (hD : MeasurableSet D) (T₀ k j : ℕ) :
    MeasurableSet[bmFiltration B (j : ℝ≥0)] {ω | occTimes T₀ (visits B D ω) k = (j : ℕ∞)} := by
  induction k generalizing j with
  | zero => exact measurableSet_nxt hB hD 0 j
  | succ k ih =>
    have e : {ω | occTimes T₀ (visits B D ω) (k + 1) = (j : ℕ∞)} =
        ⋃ n : ℕ, ⋃ (_ : n ≤ j), ({ω | occTimes T₀ (visits B D ω) k = (n : ℕ∞)} ∩
          {ω | nxt (visits B D ω) (n + T₀) = (j : ℕ∞)}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h
        have hk : occTimes T₀ (visits B D ω) k ≠ ⊤ := fun htop => by
          rw [occTimes_succ_of_top htop] at h; exact absurd h (by simp)
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hk
        rw [occTimes_succ_of_eq hn.symm] at h
        have := ((nxt_eq_iff _ _ _).1 h).1
        exact ⟨n, by omega, hn.symm, h⟩
      · rintro ⟨n, -, hn, h⟩
        rw [occTimes_succ_of_eq hn]; exact h
    rw [e]
    refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hn => ?_
    refine MeasurableSet.inter ?_ (measurableSet_nxt hB hD _ j)
    exact bmFiltration_mono B (by exact_mod_cast hn) _ (ih n)

end ElboimSly.Brownian
