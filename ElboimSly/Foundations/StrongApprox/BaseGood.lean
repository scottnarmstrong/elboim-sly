/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseWalkId
public import ElboimSly.Foundations.StrongApprox.UnitWindows
public import Mathlib

/-!
# The good event of the base coupling

ES22 (8.3): base coupling with precision n^10 ("Good event"): outside the bad events `𝒜₁, 𝒜₂, 𝒜₃`, the
distance `‖X̃(t) - √2 B(t)‖` is `< 4 a_n` for every `t ∈ [0, T]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

/-- The walk as a real vector. -/
noncomputable def Xr (d : ℕ) (ν : Measure (Dir d × ℝ)) (t : ℝ) : Fin d → ℝ :=
  fun i => ((walk d ν t i : ℤ) : ℝ)

/-- The partial sums of the coupling coordinate pair, in the form of A1. -/
noncomputable def Sdef {N : ℕ} (p : (Fin N → ℝ) × (Fin N → ℝ)) (J : Fin N) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· ≤ J), (p.1 i - 1 - p.2 i)

theorem Sfun_eq_Sdef {d N : ℕ} (a : SA d N) (v : Dir d) (J : Fin N) :
    Sfun a v ((J : ℕ) + 1) = Sdef (a v) J := by
  unfold Sfun Sdef
  refine Finset.sum_bij (fun m hm => (⟨m, by
      have := Finset.mem_range.1 hm; have := J.2; omega⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    have := Finset.mem_range.1 hm; omega
  · intro m _ m' _ h
    simpa using h
  · intro p hp
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hp
    exact Finset.mem_range.2 (by omega)
  · intro m hm
    have : (m : ℕ) < N := by have := Finset.mem_range.1 hm; have := J.2; omega
    simp [this]

theorem Sfun_eq_Sdef' {d N : ℕ} (a : SA d N) (v : Dir d) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ N) :
    Sfun a v j = Sdef (a v) ⟨j - 1, by omega⟩ := by
  have := Sfun_eq_Sdef a v ⟨j - 1, by omega⟩
  simp only at this
  rwa [Nat.sub_add_cancel h1] at this

variable {d N : ℕ}

theorem norm_le_sum_abs (x : Fin d → ℝ) : ‖x‖ ≤ ∑ i, |x i| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |x i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)

/-- The deterministic good-event estimate. -/
theorem good_bound (ν : Measure (Dir d × ℝ)) (Xs : ℕ → Fin d → ℝ) (Bf : ℝ≥0 → Fin d → ℝ)
    (S : Dir d → ℕ → ℝ) (a : ℝ) (ha : 0 < a) (hN : 1 ≤ N)
    (hid : ∀ j : ℕ, j ≤ N → ∀ i : Fin d,
      ((walk d ν j i : ℤ) : ℝ) - √2 * ∑ m ∈ Finset.range j, Xs m i =
        S (i, true) j - S (i, false) j)
    (hBj : ∀ j : ℕ, Bf (j : ℝ≥0) = fun i => ∑ m ∈ Finset.range j, Xs m i)
    (hS : ∀ v : Dir d, ∀ j : ℕ, 1 ≤ j → j ≤ N → |S v j| < a)
    (hA2 : ∀ s s' : ℝ, 0 ≤ s → s ≤ s' → s' ≤ N → s' - s ≤ 1 → incrL1 d ν s s' < a)
    (hA3 : ∀ s s' : ℝ≥0, (s : ℝ) ≤ N → (s' : ℝ) ≤ N → dist s s' ≤ 1 →
      ‖√2 • Bf s - √2 • Bf s'‖ < a)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ N) :
    ‖Xr d ν t - √2 • Bf t‖ < 4 * a := by
  set j : ℕ := max 1 ⌈(t : ℝ)⌉₊ with hj
  have hj1 : 1 ≤ j := le_max_left _ _
  have hjN : j ≤ N := max_le hN (Nat.ceil_le.2 ht)
  have htj : (t : ℝ) ≤ j := le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
  have hjt : (j : ℝ) - t ≤ 1 := by
    have h1 : (⌈(t : ℝ)⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one t.2
    have h2 : (j : ℝ) = max 1 (⌈(t : ℝ)⌉₊ : ℝ) := by rw [hj]; push_cast; rfl
    rw [h2]
    have : (0 : ℝ) ≤ t := t.2
    rcases max_cases (1 : ℝ) (⌈(t : ℝ)⌉₊ : ℝ) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> linarith
  have hsplit : Xr d ν t - √2 • Bf t = (Xr d ν t - Xr d ν j) +
      ((Xr d ν j - √2 • Bf (j : ℝ≥0)) + (√2 • Bf (j : ℝ≥0) - √2 • Bf t)) := by abel
  -- the three terms
  have h1 : ‖Xr d ν t - Xr d ν j‖ < a := by
    rw [norm_sub_rev]
    refine lt_of_le_of_lt (norm_le_sum_abs _) ?_
    have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
    exact hA2 t j t.2 htj hjN' hjt
  have h2 : ‖Xr d ν j - √2 • Bf (j : ℝ≥0)‖ < 2 * a := by
    refine (pi_norm_lt_iff (by linarith)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have := hid j hjN i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Xr, hBj j]
    rw [this]
    calc |S (i, true) j - S (i, false) j| ≤ |S (i, true) j| + |S (i, false) j| := abs_sub _ _
      _ < a + a := add_lt_add (hS _ j hj1 hjN) (hS _ j hj1 hjN)
      _ = 2 * a := by ring
  have h3 : ‖√2 • Bf (j : ℝ≥0) - √2 • Bf t‖ < a := by
    refine hA3 _ _ (by simpa using (Nat.cast_le.2 hjN : (j : ℝ) ≤ N)) ht ?_
    rw [NNReal.dist_eq]
    simp only [NNReal.coe_natCast]
    rw [abs_le]; constructor <;> linarith
  rw [hsplit]
  calc _ ≤ ‖Xr d ν t - Xr d ν j‖ + ‖(Xr d ν j - √2 • Bf (j : ℝ≥0)) +
        (√2 • Bf (j : ℝ≥0) - √2 • Bf t)‖ := norm_add_le _ _
    _ ≤ ‖Xr d ν t - Xr d ν j‖ + (‖Xr d ν j - √2 • Bf (j : ℝ≥0)‖ +
        ‖√2 • Bf (j : ℝ≥0) - √2 • Bf t‖) := by gcongr; exact norm_add_le _ _
    _ < 4 * a := by linarith

end StrongApprox
end ElboimSly
