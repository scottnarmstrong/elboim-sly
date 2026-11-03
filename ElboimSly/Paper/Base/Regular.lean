/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.StepAux
public import Mathlib

/-!
# Regular functionals of pairs of paths: definitions and measurability

Regular functionals of pairs of paths (supplement), part (a).

`Π_T = ((ℤ^d)^k)^{[0,T]}` is `PathsOn d k T` with the cylinder `σ`-algebra.  Since only the
values on `[0, T]` matter, a path `γ ∈ Π_T` is read through its extension `extT T γ i` to
`[0, ∞)`, constant after `T`.  `γ` is *regular* if each `γ_i` is right-continuous with finitely
many discontinuities, i.e. if each `extT T γ i` is a step path.

For `i, j < k`, `L ∈ [0, T]` and `ρ ≥ 0`: `V(γ) = {γ_i(q) : q ∈ 𝕼_L}` (`vset`),
`f^γ(s) = 1{d(γ_j(s), V(γ)) ≤ ρ}` (`fval`) and
`Φ(γ) = limsup_m T 2^{-m} ∑_{l < 2^m} f^γ(l T 2^{-m})` (`Phi`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Paper.Base

variable {d k : ℕ}

/-- `Π_T = ((ℤ^d)^k)^{[0,T]}` with the cylinder `σ`-algebra. -/
abbrev PathsOn (d k : ℕ) (T : ℝ≥0) : Type := Set.Icc (0 : ℝ≥0) T → Fin k → Fin d → ℤ

/-- The `i`-th coordinate path of `γ ∈ Π_T`, extended to `[0, ∞)` by constancy after `T`. -/
def extT (T : ℝ≥0) (γ : PathsOn d k T) (i : Fin k) (u : ℝ≥0) : Fin d → ℤ :=
  γ ⟨min u T, bot_le, min_le_right _ _⟩ i

/-- `γ ∈ Π_T` is regular: each `γ_i` is right-continuous with finitely many discontinuities. -/
def IsRegularPaths (T : ℝ≥0) (γ : PathsOn d k T) : Prop := ∀ i, IsStepPath (extT T γ i)

/-- The set `𝕼_L = (ℚ ∩ [0, L)) ∪ {L}`. -/
def qSetL (L : ℝ≥0) : Set ℝ≥0 := {q | q < L ∧ ∃ r : ℚ, 0 ≤ r ∧ Real.toNNReal (r : ℝ) = q} ∪ {L}

/-- `V(γ) = {γ_i(q) : q ∈ 𝕼_L}`. -/
def vset (T L : ℝ≥0) (i : Fin k) (γ : PathsOn d k T) : Set (Fin d → ℤ) :=
  extT T γ i '' qSetL L

/-- `f^γ(s) = 1{d(γ_j(s), V(γ)) ≤ ρ}`. -/
noncomputable def fval (T L : ℝ≥0) (ρ : ℝ) (i j : Fin k) (γ : PathsOn d k T) (s : ℝ≥0) : ℝ :=
  open Classical in
  if Metric.infDist (extT T γ j s) (vset T L i γ) ≤ ρ then 1 else 0

/-- `Φ(γ) = limsup_m T 2^{-m} ∑_{l < 2^m} f^γ(l T 2^{-m})`. -/
noncomputable def Phi (T L : ℝ≥0) (ρ : ℝ) (i j : Fin k) (γ : PathsOn d k T) : ℝ :=
  Filter.limsup (fun m : ℕ => (T : ℝ) / 2 ^ m *
    ∑ l ∈ Finset.range (2 ^ m), fval T L ρ i j γ ((l : ℝ≥0) * T / 2 ^ m)) Filter.atTop

theorem measurable_extT (T : ℝ≥0) (i : Fin k) (u : ℝ≥0) :
    Measurable fun γ : PathsOn d k T => extT T γ i u :=
  (measurable_pi_apply i).comp (measurable_pi_apply _)

theorem qSetL_countable (L : ℝ≥0) : (qSetL L).Countable := by
  refine Countable.union ?_ (countable_singleton L)
  refine (countable_range (fun r : ℚ => Real.toNNReal (r : ℝ))).mono ?_
  rintro q ⟨_, r, _, hr⟩
  exact ⟨r, hr⟩

theorem qSet_nonempty (L : ℝ≥0) : (qSetL L).Nonempty := ⟨L, Or.inr rfl⟩

theorem measurable_fval (T L : ℝ≥0) (ρ : ℝ) (i j : Fin k) (s : ℝ≥0) :
    Measurable (fun γ : PathsOn d k T => fval T L ρ i j γ s) := by
  classical
  have hne : ∀ γ : PathsOn d k T, (vset T L i γ).Nonempty := fun γ =>
    (qSet_nonempty L).image _
  have hset : MeasurableSet {γ : PathsOn d k T |
      Metric.infDist (extT T γ j s) (vset T L i γ) ≤ ρ} := by
    have : {γ : PathsOn d k T | Metric.infDist (extT T γ j s) (vset T L i γ) ≤ ρ} =
        ⋂ p : ℕ, ⋃ q ∈ qSetL L, {γ | ‖extT T γ j s - extT T γ i q‖ < ρ + 1 / (p + 1)} := by
      ext γ
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
      constructor
      · intro h p
        have hp : Metric.infDist (extT T γ j s) (vset T L i γ) < ρ + 1 / (p + 1) :=
          lt_of_le_of_lt h (by have : (0 : ℝ) < 1 / (p + 1) := by positivity
                               linarith)
        obtain ⟨y, ⟨q, hq, rfl⟩, hy⟩ := (Metric.infDist_lt_iff (hne γ)).1 hp
        exact ⟨q, hq, by rwa [dist_eq_norm] at hy⟩
      · intro h
        refine le_of_forall_pos_lt_add fun ε hε => ?_
        obtain ⟨p, hp⟩ := exists_nat_one_div_lt hε
        obtain ⟨q, hq, hlt⟩ := h p
        calc Metric.infDist (extT T γ j s) (vset T L i γ)
            ≤ dist (extT T γ j s) (extT T γ i q) :=
              Metric.infDist_le_dist_of_mem ⟨q, hq, rfl⟩
          _ < ρ + 1 / (p + 1) := by rwa [dist_eq_norm]
          _ < ρ + ε := by linarith
    rw [this]
    refine MeasurableSet.iInter fun p => ?_
    refine MeasurableSet.biUnion (qSetL_countable L) fun q _ => ?_
    exact measurableSet_lt (((measurable_extT T j s).sub (measurable_extT T i q)).norm)
      measurable_const
  exact Measurable.ite hset measurable_const measurable_const

/-- Regular functionals of pairs of paths (a): `Φ` is measurable on `Π_T`. -/
theorem measurable_Phi (T L : ℝ≥0) (ρ : ℝ) (i j : Fin k) :
    Measurable (Phi (d := d) T L ρ i j) := by
  refine Measurable.limsup fun m => ?_
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_fun_sum _ fun l _ => measurable_fval T L ρ i j _

end ElboimSly.Paper
