/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Stopping times and their dyadic approximations

Stopping times and their dyadic approximations (Part II).

Given a family `F : ℝ≥0 → MeasurableSpace Ω` of `σ`-algebras, a *stopping time* is
`τ : Ω → ℝ≥0∞` with `{τ ≤ t} ∈ F t` for all `t`. We define the stopped `σ`-algebra
`stoppedSigma`, the dyadic approximations `dyadic n τ`, and prove
`τ < dyadic n τ ≤ τ + 2⁻ⁿ` on `{τ < ∞}` and `A ∩ {dyadic n τ = a} ∈ F a` for `A` in the stopped
`σ`-algebra.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory

namespace ElboimSly.StrongApprox

section Sigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Stopping times and their dyadic approximations (a). The `σ`-algebra `ℱ_τ` of events `A` with
`A ∩ {τ ≤ t} ∈ ℱ_t` for all `t`. -/
@[instance_reducible] def stoppedSigma (F : ℝ≥0 → MeasurableSpace Ω) (τ : Ω → ℝ≥0∞)
    (hτ : ∀ t : ℝ≥0, MeasurableSet[F t] {ω | τ ω ≤ t}) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ ∀ t : ℝ≥0, MeasurableSet[F t] (A ∩ {ω | τ ω ≤ t})
  measurableSet_empty := ⟨MeasurableSet.empty, fun t => by simp⟩
  measurableSet_compl := by
    rintro A ⟨hA, hA'⟩
    refine ⟨hA.compl, fun t => ?_⟩
    have : Aᶜ ∩ {ω | τ ω ≤ t} = {ω | τ ω ≤ t} \ (A ∩ {ω | τ ω ≤ t}) := by
      ext ω; simp [and_comm]
    rw [this]
    exact (hτ t).diff (hA' t)
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion fun i => (hf i).1, fun t => ?_⟩
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion fun i => (hf i).2 t

lemma measurableSet_stoppedSigma {F : ℝ≥0 → MeasurableSpace Ω} {τ : Ω → ℝ≥0∞}
    {hτ : ∀ t : ℝ≥0, MeasurableSet[F t] {ω | τ ω ≤ t}} {A : Set Ω} :
    MeasurableSet[stoppedSigma F τ hτ] A ↔
      MeasurableSet A ∧ ∀ t : ℝ≥0, MeasurableSet[F t] (A ∩ {ω | τ ω ≤ t}) := Iff.rfl

lemma stoppedSigma_le {F : ℝ≥0 → MeasurableSpace Ω} {τ : Ω → ℝ≥0∞}
    {hτ : ∀ t : ℝ≥0, MeasurableSet[F t] {ω | τ ω ≤ t}} : stoppedSigma F τ hτ ≤ mΩ :=
  fun _ hA => hA.1

omit mΩ in
/-- Stopping times and their dyadic approximations (a): `{τ < b} ∩ A ∈ ℱ_b`. -/
lemma measurableSet_inter_lt {F : ℝ≥0 → MeasurableSpace Ω} (hF : Monotone F) {τ : Ω → ℝ≥0∞}
    {A : Set Ω} (hA : ∀ t : ℝ≥0, MeasurableSet[F t] (A ∩ {ω | τ ω ≤ t})) (b : ℝ≥0) :
    MeasurableSet[F b] (A ∩ {ω | τ ω < b}) := by
  rcases eq_or_ne b 0 with rfl | hb
  · have : A ∩ {ω | τ ω < ((0 : ℝ≥0) : ℝ≥0∞)} = ∅ := by
      ext ω; simp
    rw [this]; exact @MeasurableSet.empty _ (F 0)
  · have hbpos : 0 < b := pos_iff_ne_zero.2 hb
    have : A ∩ {ω | τ ω < b} =
        ⋃ m : ℕ, A ∩ {ω | τ ω ≤ ((b - ((m : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hAω, hlt⟩
        have hne : τ ω ≠ ⊤ := ne_top_of_lt hlt
        set t' := (τ ω).toNNReal with ht'
        have ht'b : t' < b := by
          rw [← ENNReal.coe_lt_coe, ht', ENNReal.coe_toNNReal hne]; exact hlt
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (tsub_pos_of_lt ht'b)
        refine ⟨m, hAω, ?_⟩
        have : t' ≤ b - ((m : ℝ≥0) + 1)⁻¹ := by
          refine le_tsub_of_add_le_right ?_
          have h2 : ((m : ℝ≥0) + 1)⁻¹ ≤ b - t' := by
            have := hm.le
            simpa [one_div] using this
          calc t' + ((m : ℝ≥0) + 1)⁻¹ ≤ t' + (b - t') := by gcongr
            _ = b := add_tsub_cancel_of_le ht'b.le
        calc τ ω = t' := (ENNReal.coe_toNNReal hne).symm
          _ ≤ _ := by exact_mod_cast this
      · rintro ⟨m, hAω, hle⟩
        refine ⟨hAω, lt_of_le_of_lt hle ?_⟩
        exact_mod_cast tsub_lt_self hbpos (by positivity)
    rw [this]
    refine MeasurableSet.iUnion fun m => ?_
    have h1 := hA (b - ((m : ℝ≥0) + 1)⁻¹)
    exact hF tsub_le_self _ h1

end Sigma

/-! ### Dyadic approximations -/

/-- Stopping times and their dyadic approximations (b). `τ_n = 2⁻ⁿ(⌊2ⁿτ⌋ + 1)` on `{τ < ∞}`, `∞` otherwise. -/
noncomputable def dyadic (n : ℕ) (τ : ℝ≥0∞) : ℝ≥0∞ :=
  if τ = ⊤ then ⊤ else (((⌊(2 : ℝ≥0) ^ n * τ.toNNReal⌋₊ + 1 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0)

lemma dyadic_top (n : ℕ) : dyadic n ⊤ = ⊤ := by simp [dyadic]

lemma dyadic_coe (n : ℕ) (t : ℝ≥0) :
    dyadic n (t : ℝ≥0∞) = (((⌊(2 : ℝ≥0) ^ n * t⌋₊ + 1 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0) := by
  simp [dyadic]

lemma dyadic_lt_top_iff (n : ℕ) (τ : ℝ≥0∞) : dyadic n τ < ⊤ ↔ τ < ⊤ := by
  by_cases h : τ = ⊤
  · simp [h, dyadic_top]
  · rw [dyadic, ite_eq_right h]
    exact iff_of_true ENNReal.coe_lt_top (lt_top_iff_ne_top.2 h)

/-- Stopping times and their dyadic approximations (b): `τ < τ_n`. -/
lemma lt_dyadic {n : ℕ} {τ : ℝ≥0∞} (h : τ < ⊤) : τ < dyadic n τ := by
  have hne := h.ne
  lift τ to ℝ≥0 using hne with t
  rw [dyadic_coe]
  rw [ENNReal.coe_lt_coe]
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  rw [lt_div_iff₀ h2, mul_comm]
  have := Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * t)
  push_cast
  exact this

/-- Stopping times and their dyadic approximations (b): `τ_n ≤ τ + 2⁻ⁿ`. -/
lemma dyadic_le_add {n : ℕ} {τ : ℝ≥0∞} (h : τ < ⊤) : dyadic n τ ≤ τ + ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  have hne := h.ne
  lift τ to ℝ≥0 using hne with t
  rw [dyadic_coe]
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  have : ((t : ℝ≥0∞) + ((2 : ℝ≥0∞) ^ n)⁻¹) = ((t + (2 ^ n)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    push_cast
    rfl
  rw [this, ENNReal.coe_le_coe, div_le_iff₀ h2]
  have h3 : (⌊(2 : ℝ≥0) ^ n * t⌋₊ : ℝ≥0) ≤ 2 ^ n * t := Nat.floor_le (by positivity)
  calc (((⌊(2 : ℝ≥0) ^ n * t⌋₊ + 1 : ℕ)) : ℝ≥0) = (⌊(2 : ℝ≥0) ^ n * t⌋₊ : ℝ≥0) + 1 := by push_cast; rfl
    _ ≤ 2 ^ n * t + 1 := by gcongr
    _ = (t + (2 ^ n)⁻¹) * 2 ^ n := by
      field_simp

lemma monotone_dyadic (n : ℕ) : Monotone (dyadic n) := by
  intro a b hab
  by_cases hb : b = ⊤
  · rw [hb, dyadic_top]; exact le_top
  · have ha : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
    lift a to ℝ≥0 using ha with x
    lift b to ℝ≥0 using hb with y
    rw [dyadic_coe, dyadic_coe, ENNReal.coe_le_coe]
    have hxy : x ≤ y := ENNReal.coe_le_coe.1 hab
    gcongr

lemma measurable_dyadic (n : ℕ) : Measurable (dyadic n) := (monotone_dyadic n).measurable

lemma dyadic_tendsto {τ : ℝ≥0∞} (h : τ < ⊤) :
    Filter.Tendsto (fun n => (dyadic n τ).toNNReal) Filter.atTop (nhds τ.toNNReal) := by
  have hl : ∀ n, τ.toNNReal ≤ (dyadic n τ).toNNReal := fun n => by
    have := (lt_dyadic (n := n) h).le
    exact ENNReal.toNNReal_mono ((dyadic_lt_top_iff n τ).2 h).ne this
  have hu : ∀ n, (dyadic n τ).toNNReal ≤ τ.toNNReal + (2 ^ n)⁻¹ := fun n => by
    have h1 := dyadic_le_add (n := n) h
    have h2 : (dyadic n τ).toNNReal ≤ (τ + ((2 : ℝ≥0∞) ^ n)⁻¹).toNNReal :=
      ENNReal.toNNReal_mono (ENNReal.add_ne_top.2 ⟨h.ne, by simp⟩) h1
    rw [ENNReal.toNNReal_add h.ne (by simp)] at h2
    simpa [ENNReal.toNNReal_ofNat] using h2
  have hlim : Filter.Tendsto (fun n : ℕ => τ.toNNReal + ((2 : ℝ≥0) ^ n)⁻¹) Filter.atTop
      (nhds (τ.toNNReal + 0)) := by
    refine tendsto_const_nhds.add ?_
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0)⁻¹) (zero_le) (by
      rw [← NNReal.coe_lt_coe]; norm_num)
    simpa [inv_pow] using this
  rw [add_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hl hu

lemma dyadic_eq_iff (n m : ℕ) (τ : ℝ≥0∞) :
    dyadic n τ = (((m + 1 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0) ↔
      ((((m : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ≥0∞) ≤ τ ∧
        τ < ((((m + 1 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  by_cases hτ : τ = ⊤
  · subst hτ
    rw [dyadic_top]
    constructor
    · intro h; exact absurd h.symm ENNReal.coe_ne_top
    · rintro ⟨_, h⟩; exact absurd h (not_lt.2 le_top)
  · lift τ to ℝ≥0 using hτ with t
    rw [dyadic_coe, ENNReal.coe_inj, ENNReal.coe_le_coe, ENNReal.coe_lt_coe,
      div_le_iff₀ h2, lt_div_iff₀ h2, div_left_inj' h2.ne', mul_comm t]
    have key := Nat.floor_eq_iff (a := (2 : ℝ≥0) ^ n * t) (n := m) zero_le
    push_cast
    constructor
    · intro h
      have : ⌊(2 : ℝ≥0) ^ n * t⌋₊ + 1 = m + 1 := by exact_mod_cast h
      exact key.1 (by omega)
    · intro h
      have := key.2 h
      rw [this]

open MeasureTheory in
/-- Stopping times and their dyadic approximations (c). -/
lemma measurableSet_inter_dyadic_eq {Ω : Type*} [MeasurableSpace Ω]
    {F : ℝ≥0 → MeasurableSpace Ω} (hF : Monotone F) {τ : Ω → ℝ≥0∞}
    (hτ : ∀ t : ℝ≥0, MeasurableSet[F t] {ω | τ ω ≤ t}) {A : Set Ω}
    (hA : ∀ t : ℝ≥0, MeasurableSet[F t] (A ∩ {ω | τ ω ≤ t})) (n m : ℕ) :
    MeasurableSet[F (((m + 1 : ℕ) : ℝ≥0) / 2 ^ n)]
      (A ∩ {ω | dyadic n (τ ω) = (((m + 1 : ℕ) : ℝ≥0) / 2 ^ n : ℝ≥0)}) := by
  set a : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) / 2 ^ n with ha
  set a' : ℝ≥0 := ((m : ℕ) : ℝ≥0) / 2 ^ n with ha'
  have haa : a' ≤ a := by
    rw [ha, ha']; gcongr; exact_mod_cast Nat.le_succ m
  have e : A ∩ {ω | dyadic n (τ ω) = (a : ℝ≥0∞)} =
      (A ∩ {ω | τ ω < a}) \ ({ω | τ ω < a'}) := by
    have hd : ∀ ω, dyadic n (τ ω) = (a : ℝ≥0∞) ↔ (a' : ℝ≥0∞) ≤ τ ω ∧ τ ω < a :=
      fun ω => dyadic_eq_iff n m (τ ω)
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff, hd, not_lt]
    tauto
  rw [e]
  refine MeasurableSet.diff (measurableSet_inter_lt hF hA a) ?_
  have h1 := measurableSet_inter_lt hF (A := Set.univ) (τ := τ)
    (fun t => by simpa using hτ t) a'
  simp only [Set.univ_inter] at h1
  exact hF haa _ h1

end ElboimSly.StrongApprox
