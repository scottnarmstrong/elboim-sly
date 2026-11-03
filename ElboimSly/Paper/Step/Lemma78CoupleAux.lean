/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleRegion
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import ElboimSly.Foundations.Cyclic.CycEnvLocality
public import ElboimSly.Foundations.Interchange.GoodAsCount
public import Mathlib

/-!
# Auxiliary facts for w_2 after zeta_i, given ℱ^+_zeta_i

Two points of one edge are at distance at most `1`; restart of the cyclic walk
(restriction, restart, periodicity (b)); equality in the circle `ℝ / βℤ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem norm_le_one_of_latticeAdj {a b : Fin d → ℤ} (h : LatticeAdj d a b) : ‖a - b‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have h1 : |a i - b i| ≤ ∑ j, |a j - b j| :=
    Finset.single_le_sum (f := fun j => |a j - b j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : (∑ j, |a j - b j|) = 1 := h
  rw [h2] at h1
  simpa [Int.norm_eq_abs] using (by exact_mod_cast h1 : ((|a i - b i| : ℤ) : ℝ) ≤ 1)

theorem norm_le_one_of_edge_mem {e : Edge d} {z z' : Fin d → ℤ} (hz : Edge.Mem z e)
    (hz' : Edge.Mem z' e) : ‖z - z'‖ ≤ 1 := by
  obtain ⟨a, b, hab, hadj⟩ := e.2
  unfold Edge.Mem at hz hz'
  rw [hab] at hz hz'
  have hba : LatticeAdj d b a := by
    unfold LatticeAdj at hadj ⊢
    rw [← hadj]; exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  rcases Sym2.mem_iff.1 hz with rfl | rfl <;> rcases Sym2.mem_iff.1 hz' with rfl | rfl
  · simp
  · exact norm_le_one_of_latticeAdj hadj
  · exact norm_le_one_of_latticeAdj hba
  · simp

/-- Restart of the cyclic walk. Restriction, restart, periodicity (b). -/
theorem cycWalk_restart {μ : Measure (RingSpace d β)} (hμ : Good μ) (u : Fin d → ℤ) (q : ℝ)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : 0 ≤ s) :
    cycWalk μ (cycWalk μ u q ζ) (q + ζ) s = cycWalk μ u q (ζ + s) := by
  rw [cycWalk_of_nonneg hμ _ _ hs, cycWalk_of_nonneg hμ _ _ hζ,
    cycWalk_of_nonneg hμ _ _ (by linarith)]
  have := fwdTraj_restart hμ u (a := q) (c := q + ζ) (by linarith) (t := q + ζ + s)
    (by linarith)
  rw [show q + (ζ + s) = q + ζ + s by ring]
  exact this.symm

theorem exists_int_of_coe_eq {a b : ℝ} (h : (a : AddCircle β) = (b : AddCircle β)) :
    ∃ k : ℤ, b = a + k * β := by
  have h1 : -a + b ∈ AddSubgroup.zmultiples β := QuotientAddGroup.eq.1 h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
  refine ⟨k, ?_⟩
  rw [zsmul_eq_mul] at hk
  linarith

/-- Backward uniqueness: if the walk returns to the same position `k` periods later, it was
`kβ`-periodic before. W_2 after zeta_i, given ℱ^+_zeta_i, "No closing before `b`". -/
theorem cycWalk_periodic_before {μ : Measure (RingSpace d β)} (hμ : Good μ) (u : Fin d → ℤ)
    (q : ℝ) {ζ : ℝ} (hζ : 0 ≤ ζ) {k : ℕ}
    (h : cycWalk μ u q (ζ + k * β) = cycWalk μ u q ζ) :
    ∀ t : ℝ, 0 ≤ t → t ≤ ζ → cycWalk μ u q (t + k * β) = cycWalk μ u q t := by
  have hβ : 0 < β := Fact.out
  have hkβ : (0 : ℝ) ≤ k * β := by positivity
  set f := fwdTraj hμ u q with hf
  have hpath := fwdTraj_isPathOn hμ u q (q + ζ + k * β)
  have hF : IsPathOn μ q (q + ζ) f := hpath.mono le_rfl (by linarith)
  have hG0 : IsPathOn μ (q + k * β) (q + ζ + k * β) f := hpath.mono (by linarith) le_rfl
  have hG := hG0.shift (-(k : ℤ))
  have hG' : IsPathOn μ q (q + ζ) (fun t => f (t + k * β)) := by
    convert hG using 1
    · push_cast; ring
    · push_cast; ring
    · funext t; push_cast; ring_nf
  have h0 : f (q + ζ) = (fun t => f (t + k * β)) (q + ζ) := by
    have := h
    rw [cycWalk_of_nonneg hμ _ _ (by linarith), cycWalk_of_nonneg hμ _ _ hζ] at this
    simp only
    rw [show q + ζ + k * β = q + (ζ + k * β) by ring]
    exact this.symm
  intro t ht0 htζ
  have := hF.eq_of_right hμ (by linarith) hG' h0 (q + t) ⟨by linarith, by linarith⟩
  rw [cycWalk_of_nonneg hμ _ _ (by linarith), cycWalk_of_nonneg hμ _ _ ht0]
  rw [show q + (t + k * β) = q + t + k * β by ring]
  exact this.symm


end ElboimSly.Paper.Step

end
