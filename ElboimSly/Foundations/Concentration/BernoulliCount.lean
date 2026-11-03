/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.BinomialTail

/-!
# Counting successes of adapted trials

Auxiliary material for domination by Bernoulli trials: the event `Γ_j = ⋂_{i<j} G_i` that the
first `j` trials are active, the number `S_j = ∑_{i<j} 1_{A_i}` of successes, their measurability,
and the formula for the integral of a function of `S_j`.
-/

public section

namespace ElboimSly

open MeasureTheory Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The event `Γ_j = ⋂_{i<j} G_i` that the first `j` trials are active. -/
@[expose] def concGamma (G : ℕ → Set Ω) (j : ℕ) : Set Ω := {ω | ∀ i < j, ω ∈ G i}

/-- The number of successes `S_j = ∑_{i<j} 1_{A_i}` among the first `j` trials. -/
@[expose] noncomputable def concCount (A : ℕ → Set Ω) (j : ℕ) (ω : Ω) : ℕ :=
  ∑ i ∈ range j, (A i).indicator (fun _ => (1 : ℕ)) ω

lemma concGamma_zero (G : ℕ → Set Ω) : concGamma G 0 = Set.univ := by
  ext ω; simp [concGamma]

lemma concGamma_succ (G : ℕ → Set Ω) (j : ℕ) : concGamma G (j + 1) = concGamma G j ∩ G j := by
  ext ω
  simp only [concGamma, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact h1 i h
    · subst h; exact h2

lemma concCount_zero (A : ℕ → Set Ω) (ω : Ω) : concCount A 0 ω = 0 := by
  simp [concCount]

lemma concCount_succ (A : ℕ → Set Ω) (j : ℕ) (ω : Ω) :
    concCount A (j + 1) ω = concCount A j ω + (A j).indicator (fun _ => (1 : ℕ)) ω := by
  simp [concCount, Finset.sum_range_succ]

lemma concCount_le (A : ℕ → Set Ω) (j : ℕ) (ω : Ω) : concCount A j ω ≤ j := by
  induction j with
  | zero => simp [concCount_zero]
  | succ j ih =>
    rw [concCount_succ]
    have : (A j).indicator (fun _ => (1 : ℕ)) ω ≤ 1 := by
      by_cases h : ω ∈ A j <;> simp [h]
    omega

lemma measurableSet_concGamma {m : MeasurableSpace Ω} {G : ℕ → Set Ω} {j : ℕ}
    (h : ∀ i < j, MeasurableSet[m] (G i)) : MeasurableSet[m] (concGamma G j) := by
  induction j with
  | zero => rw [concGamma_zero]; exact MeasurableSet.univ
  | succ j ih =>
    rw [concGamma_succ]
    exact (ih fun i hi => h i (by omega)).inter (h j (by omega))

lemma measurable_concCount {m : MeasurableSpace Ω} {A : ℕ → Set Ω} {j : ℕ}
    (h : ∀ i < j, MeasurableSet[m] (A i)) : Measurable[m] (concCount A j) := by
  induction j with
  | zero =>
    have : concCount A 0 = fun _ => 0 := by funext ω; simp [concCount_zero]
    rw [this]; exact measurable_const
  | succ j ih =>
    have : concCount A (j + 1) =
        fun ω => concCount A j ω + (A j).indicator (fun _ => (1 : ℕ)) ω := by
      funext ω; exact concCount_succ A j ω
    rw [this]
    exact (ih fun i hi => h i (by omega)).add (measurable_const.indicator (h j (by omega)))

/-- Integral of a function of a bounded `ℕ`-valued random variable, on an event. -/
lemma integral_indicator_comp_nat {E : Set Ω} (hE : MeasurableSet E) {S : Ω → ℕ}
    (hS : Measurable S) {N : ℕ} (hSN : ∀ ω, S ω ≤ N) (g : ℕ → ℝ) [IsFiniteMeasure μ] :
    Integrable (E.indicator (fun ω => g (S ω))) μ ∧
      ∫ ω, E.indicator (fun ω => g (S ω)) ω ∂μ =
        ∑ s ∈ range (N + 1), g s * μ.real (E ∩ {ω | S ω = s}) := by
  have hmeas : ∀ s, MeasurableSet (E ∩ {ω | S ω = s}) := fun s =>
    hE.inter (hS (measurableSet_singleton s))
  have hdecomp : E.indicator (fun ω => g (S ω)) =
      ∑ s ∈ range (N + 1), (E ∩ {ω | S ω = s}).indicator (fun _ => g s) := by
    funext ω
    rw [Finset.sum_apply]
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω, Finset.sum_eq_single (S ω)]
      · rw [Set.indicator_of_mem (show ω ∈ E ∩ {ω' | S ω' = S ω} from ⟨hω, rfl⟩)]
      · intro s _ hs
        rw [Set.indicator_of_notMem]
        rintro ⟨_, h⟩
        exact hs h.symm
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (hSN ω))) h
    · rw [Set.indicator_of_notMem hω]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [Set.indicator_of_notMem]
      exact fun h => hω h.1
  rw [hdecomp]
  constructor
  · rw [show (∑ s ∈ range (N + 1), (E ∩ {ω | S ω = s}).indicator (fun _ => g s)) =
        fun ω => ∑ s ∈ range (N + 1), (E ∩ {ω | S ω = s}).indicator (fun _ => g s) ω from by
      funext ω; rw [Finset.sum_apply]]
    exact integrable_finsetSum _ fun s _ => (integrable_const (g s)).indicator (hmeas s)
  · rw [show (∑ s ∈ range (N + 1), (E ∩ {ω | S ω = s}).indicator (fun _ => g s)) =
        fun ω => ∑ s ∈ range (N + 1), (E ∩ {ω | S ω = s}).indicator (fun _ => g s) ω from by
      funext ω; rw [Finset.sum_apply]]
    rw [integral_finsetSum _ fun s _ => (integrable_const (g s)).indicator (hmeas s)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_indicator_const _ (hmeas s)]
    simp [mul_comm]

end ElboimSly
