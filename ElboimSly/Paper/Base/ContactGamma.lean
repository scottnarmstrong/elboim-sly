/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactTimes
public import ElboimSly.Paper.Base.ContactScenario
public import ElboimSly.Foundations.SRW.CountableReduction
public import ElboimSly.Foundations.SRW.ShiftWalk
public import ElboimSly.Foundations.SRW.HitThm
public import Mathlib

/-!
# The escape scenario `Γ_{y₀}`

Contacts are few (ii), "The escape scenario".

For `y₀ ∈ ℤ^d` with `0 < ‖y₀‖ ≤ 1`, `escDir y₀` is a unit vector `±e_i` with `(y₀)_i = ±1`, and
`v₀ = (escDir y₀).vec`.  `contactGamma y₀` is the set of paths `x̄ = (x₁, x₂)` in `ℤ^{d+d}` such that
`x̄(1) = (0, v₀)`, `x̄(q) ∈ {(0,0),(0,v₀)}` at rational `q ∈ [0, 1]`, and
`‖y₀ + v₀ + (x₂ - x₁)(1 + q) - (x₂ - x₁)(1)‖ ≥ 2` at rational `q ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ}

section Dir

variable [NeZero d]

/-- A unit vector `±e_i` with `|(y₀)_i| = 1` and the same sign. -/
noncomputable def escDir (y₀ : Fin d → ℤ) : Dir d :=
  open Classical in
  if h : ∃ i, |y₀ i| = 1 then (Classical.choose h, decide (0 < y₀ (Classical.choose h)))
  else (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)

theorem exists_abs_eq_one {y₀ : Fin d → ℤ} (h0 : y₀ ≠ 0) (h1 : ‖y₀‖ ≤ 1) : ∃ i, |y₀ i| = 1 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d)) (fun j => ‖y₀ j‖)
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, Finset.mem_univ _⟩
  have hxi : ‖y₀‖ = ‖y₀ i‖ := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ _)
    · exact norm_le_pi_norm y₀ i
  have hne : y₀ i ≠ 0 := by
    intro h
    apply h0
    have : ‖y₀‖ = 0 := by rw [hxi, h]; simp
    exact norm_eq_zero.1 this
  refine ⟨i, ?_⟩
  have h2 : ‖y₀ i‖ ≤ 1 := hxi ▸ h1
  rw [Int.norm_eq_abs] at h2
  have h3 : |y₀ i| ≤ 1 := by exact_mod_cast h2
  have h4 : 0 < |y₀ i| := abs_pos.2 hne
  omega

/-- `‖y₀ + v₀‖ ≥ 2` for the escape direction `v₀ = (escDir y₀).vec`. -/
theorem two_le_norm_add_escDir {y₀ : Fin d → ℤ} (h0 : y₀ ≠ 0) (h1 : ‖y₀‖ ≤ 1) :
    2 ≤ ‖y₀ + (escDir y₀).vec‖ := by
  classical
  have hex := exists_abs_eq_one h0 h1
  have hdir : escDir y₀ = (Classical.choose hex, decide (0 < y₀ (Classical.choose hex))) := by
    unfold escDir; rw [dite_eq_left hex]
  set i := Classical.choose hex with hi
  have hi1 : |y₀ i| = 1 := Classical.choose_spec hex
  have key : (2 : ℝ) ≤ ‖(y₀ + (escDir y₀).vec) i‖ := by
    rw [hdir]
    simp only [Dir.vec, Pi.add_apply, Pi.single_eq_same, Int.norm_eq_abs]
    rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 hi1 with e | e
    · rw [e]; simp
    · rw [e]; simp
  exact key.trans (norm_le_pi_norm _ i)

end Dir

/-- The first block of a path in `ℤ^{d+d}`. -/
def fstP (γ : PathSpace (d + d)) : PathSpace d := fun s i => γ s (Fin.castAdd d i)

/-- The second block of a path in `ℤ^{d+d}`. -/
def sndP (γ : PathSpace (d + d)) : PathSpace d := fun s i => γ s (Fin.natAdd d i)

/-- Contacts are few (ii): the escape scenario `Γ_{y₀}`. -/
def contactGamma [NeZero d] (y₀ : Fin d → ℤ) : Set (PathSpace (d + d)) :=
  {γ | fstP γ 1 = 0 ∧ sndP γ 1 = (escDir y₀).vec ∧
    (∀ q : ℚ, 0 ≤ q → q ≤ 1 → fstP γ (ratNN q) = 0 ∧
      (sndP γ (ratNN q) = 0 ∨ sndP γ (ratNN q) = (escDir y₀).vec)) ∧
    ∀ q : ℚ, 0 ≤ q → 2 ≤ ‖(y₀ + (escDir y₀).vec) +
      ((sndP γ (1 + ratNN q) - fstP γ (1 + ratNN q)) - (sndP γ 1 - fstP γ 1))‖}

theorem measurableSet_pair_preimage (s t : ℝ≥0) (S : Set ((Fin (d + d) → ℤ) × (Fin (d + d) → ℤ))) :
    MeasurableSet {γ : PathSpace (d + d) | (γ s, γ t) ∈ S} :=
  ((measurable_pi_apply s).prodMk (measurable_pi_apply t)) (MeasurableSet.of_discrete (s := S))

theorem measurableSet_escGamma [NeZero d] (y₀ : Fin d → ℤ) : MeasurableSet (contactGamma y₀) := by
  have h1 : MeasurableSet {γ : PathSpace (d + d) | fstP γ 1 = 0} := by
    have := measurableSet_pair_preimage (d := d) 1 1 {p | (fun i : Fin d => p.1 (Fin.castAdd d i)) = 0}
    exact this
  have h2 : MeasurableSet {γ : PathSpace (d + d) | sndP γ 1 = (escDir y₀).vec} := by
    have := measurableSet_pair_preimage (d := d) 1 1
      {p | (fun i : Fin d => p.1 (Fin.natAdd d i)) = (escDir y₀).vec}
    exact this
  have h3 : MeasurableSet {γ : PathSpace (d + d) | ∀ q : ℚ, 0 ≤ q → q ≤ 1 →
      fstP γ (ratNN q) = 0 ∧ (sndP γ (ratNN q) = 0 ∨ sndP γ (ratNN q) = (escDir y₀).vec)} := by
    have : {γ : PathSpace (d + d) | ∀ q : ℚ, 0 ≤ q → q ≤ 1 →
        fstP γ (ratNN q) = 0 ∧ (sndP γ (ratNN q) = 0 ∨ sndP γ (ratNN q) = (escDir y₀).vec)} =
        ⋂ q : ℚ, {γ | (γ (ratNN q), γ (ratNN q)) ∈ {p : (Fin (d + d) → ℤ) × (Fin (d + d) → ℤ) |
          0 ≤ q → q ≤ 1 → (fun i : Fin d => p.1 (Fin.castAdd d i)) = 0 ∧
            ((fun i : Fin d => p.1 (Fin.natAdd d i)) = 0 ∨
              (fun i : Fin d => p.1 (Fin.natAdd d i)) = (escDir y₀).vec)}} := by
      ext γ; simp only [mem_iInter, mem_ofPred_eq]; exact Iff.rfl
    rw [this]
    exact MeasurableSet.iInter fun q => measurableSet_pair_preimage _ _ _
  have h4 : MeasurableSet {γ : PathSpace (d + d) | ∀ q : ℚ, 0 ≤ q → 2 ≤ ‖(y₀ + (escDir y₀).vec) +
      ((sndP γ (1 + ratNN q) - fstP γ (1 + ratNN q)) - (sndP γ 1 - fstP γ 1))‖} := by
    have : {γ : PathSpace (d + d) | ∀ q : ℚ, 0 ≤ q → 2 ≤ ‖(y₀ + (escDir y₀).vec) +
        ((sndP γ (1 + ratNN q) - fstP γ (1 + ratNN q)) - (sndP γ 1 - fstP γ 1))‖} =
        ⋂ q : ℚ, {γ | (γ (1 + ratNN q), γ 1) ∈ {p : (Fin (d + d) → ℤ) × (Fin (d + d) → ℤ) |
          0 ≤ q → 2 ≤ ‖(y₀ + (escDir y₀).vec) +
            (((fun i : Fin d => p.1 (Fin.natAdd d i)) - (fun i : Fin d => p.1 (Fin.castAdd d i))) -
              ((fun i : Fin d => p.2 (Fin.natAdd d i)) - (fun i : Fin d => p.2 (Fin.castAdd d i))))‖}} := by
      ext γ; simp only [mem_iInter, mem_ofPred_eq]; exact Iff.rfl
    rw [this]
    exact MeasurableSet.iInter fun q => measurableSet_pair_preimage _ _ _
  exact h1.inter (h2.inter (h3.inter h4))

end ElboimSly.Paper
