/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Roots.RegenCopies
public import ElboimSly.Paper.Roots.RootR2OfR1
public import ElboimSly.Frozen.Defs.IndHyp
import Mathlib

/-!
# R1 from the induction (conditional helper)

R1: the origin is rarely in a finite cycle (proof).

`IndMainStmt` restates the proposition of `ind_main` verbatim, so that this file does not import the
statement file. `root_R1_of_indMain` is the implication Theorem 3.2 ⇒ R1. It uses the constructions of the regenerated walk
(i) only through the marginal statement `isPoissonPointProcess_copyEnv`, which is proved, so it has
no cyclic hypothesis.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Roots

/-- The proposition of the frozen `ind_main`, for all `d ≥ 5`. -/
def IndMainStmt : Prop :=
  ∀ (d : ℕ), 5 ≤ d →
    ∃ β₀ : ℝ, ∃ n₀ : ℕ, 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        IndHyp d β n t₀

/-! ### The numerical bound -/

theorem term_le {d : ℕ} (hd : 5 ≤ d) {β : ℝ} (hβ : 1 ≤ β) (i : ℕ) :
    (((i : ℝ) + 1) * β) ^ (-(d : ℝ) / 2 + 1 / 10) ≤ 1 / ((i : ℝ) + 1) ^ 2 * (1 / β) := by
  have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hi0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by linarith
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  rw [Real.mul_rpow hi0 hβ0]
  have h1 : ((i : ℝ) + 1) ^ (-(d : ℝ) / 2 + 1 / 10) ≤ ((i : ℝ) + 1) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hi (by linarith)
  have h2 : β ^ (-(d : ℝ) / 2 + 1 / 10) ≤ β ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hβ (by linarith)
  have e1 : ((i : ℝ) + 1) ^ (-2 : ℝ) = 1 / ((i : ℝ) + 1) ^ 2 := by
    rw [Real.rpow_neg hi0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have e2 : β ^ (-1 : ℝ) = 1 / β := by rw [Real.rpow_neg_one, one_div]
  rw [e1] at h1
  rw [e2] at h2
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hβ0 _) (by positivity)

theorem tsum_term_lt {d : ℕ} (hd : 5 ≤ d) {β : ℝ} (hβ : 1 ≤ β) :
    ∑' i : ℕ, ENNReal.ofReal ((((i : ℝ) + 1) * β) ^ (-(d : ℝ) / 2 + 1 / 10)) <
      ENNReal.ofReal (2 / β) := by
  have hβ0 : 0 < β := by linarith
  have hz : HasSum (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := hasSum_zeta_two
    have h := (hasSum_nat_add_iff' 1).mpr this
    simpa using h
  have hz' : HasSum (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2 * (1 / β)) (Real.pi ^ 2 / 6 * (1 / β)) :=
    hz.mul_right _
  calc ∑' i : ℕ, ENNReal.ofReal ((((i : ℝ) + 1) * β) ^ (-(d : ℝ) / 2 + 1 / 10))
      ≤ ∑' i : ℕ, ENNReal.ofReal (1 / ((i : ℝ) + 1) ^ 2 * (1 / β)) :=
        ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (term_le hd hβ i)
    _ = ENNReal.ofReal (Real.pi ^ 2 / 6 * (1 / β)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hz'.summable, hz'.tsum_eq]
    _ < ENNReal.ofReal (2 / β) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        have := Real.pi_lt_d2
        have hp := Real.pi_pos
        have : Real.pi ^ 2 / 6 < 2 := by nlinarith
        calc Real.pi ^ 2 / 6 * (1 / β) < 2 * (1 / β) := by
              exact mul_lt_mul_of_pos_right this (by positivity)
          _ = 2 / β := by ring

/-- (H2) for the environment record, at every real time `t ≥ 1`, from `ind_main`'s hypotheses. -/
theorem indH2_of_indHyp {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ : ℕ}
    (hind : ∀ n : ℕ, n₀ ≤ n → IndHyp d β n 4)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {t : ℝ} (ht : 1 ≤ t) (u : Fin d → ℤ) :
    P {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} ≤
      ENNReal.ofReal (t ^ (-(d : ℝ) / 2 + 1 / 10)) := by
  have hn : n₀ ≤ n₀ + ⌈t⌉₊ := Nat.le_add_right _ _
  have h2 := ((hind _ hn).1 Ω P N hN).2.1
  refine h2 t ⟨ht, ?_⟩ u
  unfold indScale
  have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have h3 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ ((n₀ + ⌈t⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left _ _
  have h4 : ((n₀ + ⌈t⌉₊ : ℕ) : ℝ) < (4 : ℝ) ^ (n₀ + ⌈t⌉₊) := by
    exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 4)
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) (n₀ + ⌈t⌉₊)]

universe u

/-- Conditional helper. R1: the origin is rarely in a finite cycle (proof): `ind_main` implies R1. The law-transfer
step uses measurability, uniqueness in law and the marginal part of the constructions of the regenerated walk (i)
(`isPoissonPointProcess_copyEnv`); no cyclic statement is assumed. -/
theorem root_R1_of_indMain : IndMainStmt → RootR1Stmt.{u} := by
  intro hI d hd
  obtain ⟨β₀, n₀, hn₀, hind⟩ := hI d hd
  refine ⟨max β₀ 1, lt_max_of_lt_right one_pos, fun β hβ _ Ω _ P N hN => ?_⟩
  have hβ1 : 1 ≤ β := le_trans (le_max_right _ _) hβ
  have hβ₀ : β₀ ≤ β := le_trans (le_max_left _ _) hβ
  have hFin : MeasurableSet (finZeroEvent d β) := measurableSet_finZeroEvent
  obtain ⟨Ω', _, P', N', hP', hN', -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  have h0 := isPoissonPointProcess_copyEnv hN' 0
  have h1 := isPoissonPointProcess_copyEnv hN' 1
  -- law transfer
  have hlaw : P {ω | N ω ∈ finZeroEvent d β} = P' {ω | copyEnv (N' ω) 0 ∈ finZeroEvent d β} := by
    have e1 := Measure.map_apply (μ := P) hN.measurable hFin
    have e2 := Measure.map_apply (μ := P') h0.measurable hFin
    rw [map_eq_ringLaw hN] at e1
    rw [map_eq_ringLaw h0] at e2
    exact e1.symm.trans e2
  rw [hlaw]
  have hsub : {ω | copyEnv (N' ω) 0 ∈ finZeroEvent d β} ⊆
      (⋃ i : ℕ, {ω | regenWalk (fun k => copyEnv (N' ω) k) (((i : ℝ) + 1) * β) = 0}) ∪
        {ω | ¬ Good (copyEnv (N' ω) 1)} := by
    intro ω hω
    by_cases hg : Good (copyEnv (N' ω) 1)
    · left
      have hg0 : Good (copyEnv (N' ω) 0) := hω.1
      have hlt : cycTreg (copyEnv (N' ω) 0) < ⊤ :=
        (Cyclic.cycTreg_lt_top_iff_mem_finZeroEvent hg0).2 hω
      obtain ⟨m, hm, -, htr⟩ := Cyclic.exists_cycTreg_eq hlt
      refine Set.mem_iUnion.2 ⟨m - 1, ?_⟩
      have hcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
        rw [Nat.cast_sub hm]; push_cast; ring
      simp only [Set.mem_ofPred_eq]
      rw [hcast]
      refine regenWalk_eq_zero_of_treg _ hg (by positivity) htr
    · exact Or.inr hg
  have hnull : P' {ω | ¬ Good (copyEnv (N' ω) 1)} = 0 := ae_iff.1 (Interchange.ae_good h1)
  have hind' : ∀ n : ℕ, n₀ ≤ n → IndHyp d β n 4 := fun n hn =>
    hind β hβ₀ n hn 4 (by norm_num) le_rfl
  calc P' {ω | copyEnv (N' ω) 0 ∈ finZeroEvent d β}
      ≤ P' ((⋃ i : ℕ, {ω | regenWalk (fun k => copyEnv (N' ω) k) (((i : ℝ) + 1) * β) = 0}) ∪
        {ω | ¬ Good (copyEnv (N' ω) 1)}) := measure_mono hsub
    _ ≤ P' (⋃ i : ℕ, {ω | regenWalk (fun k => copyEnv (N' ω) k) (((i : ℝ) + 1) * β) = 0}) +
        P' {ω | ¬ Good (copyEnv (N' ω) 1)} := measure_union_le _ _
    _ = P' (⋃ i : ℕ, {ω | regenWalk (fun k => copyEnv (N' ω) k) (((i : ℝ) + 1) * β) = 0}) := by
        rw [hnull, add_zero]
    _ ≤ ∑' i : ℕ, P' {ω | regenWalk (fun k => copyEnv (N' ω) k) (((i : ℝ) + 1) * β) = 0} :=
        measure_iUnion_le _
    _ ≤ ∑' i : ℕ, ENNReal.ofReal ((((i : ℝ) + 1) * β) ^ (-(d : ℝ) / 2 + 1 / 10)) :=
        ENNReal.tsum_le_tsum fun i => indH2_of_indHyp hind' hN'
          (by nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) 0
    _ < ENNReal.ofReal (2 / β) := tsum_term_lt hd hβ1

end ElboimSly.Roots

end
