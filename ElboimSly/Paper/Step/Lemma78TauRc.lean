/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.ProcessLaw
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegenLaw
public import ElboimSly.Foundations.Cyclic.CycFarRc
public import ElboimSly.Foundations.Cyclic.CycMergeMeas
public import Mathlib

/-!
# Right-continuity of the glued continuation `W'`

One excursion succeeds with probability at least frac12 (the surrogate for `W'_i`). `contGlue β p q` is right-continuous
whenever the pieces `p`, `q k` are (`isRCPath_contGlue`); `walkMap ν` and `envWalk ν δ` are
right-continuous for every `ν` (`isRCPath_walkMap`, `isRCPath_envWalk`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- A real-time right-continuity statement gives right-continuity on `ℝ≥0`. -/
theorem isRCPath_of_real {x : ℝ≥0 → Fin d → ℤ} {y : ℝ → Fin d → ℤ}
    (hxy : ∀ s : ℝ≥0, x s = y s) (hy : ∀ s : ℝ≥0, ∀ᶠ u in 𝓝[≥] (s : ℝ), y u = y s) :
    IsRCPath x := by
  intro s
  have ht : Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[≥] s) (𝓝[≥] (s : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (NNReal.continuous_coe.tendsto s).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact mem_Ici.2 (by exact_mod_cast mem_Ici.1 hu)
  filter_upwards [ht.eventually (hy s)] with u hu
  rw [hxy u, hxy s]; exact hu

theorem isRCPath_walkMap (ν : Measure (RingSpace d β)) : IsRCPath (walkMap ν) := by
  classical
  have hg : Good (if Good ν then ν else 0) := by split_ifs with h; exacts [h, good_zero]
  exact isRCPath_of_real (y := fun r => cycWalk (if Good ν then ν else 0) 0 0 r)
    (fun s => rfl) (fun s => cycWalk_rightCont hg 0 0 (NNReal.coe_nonneg s))

theorem isRCPath_envWalk {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] (ν : Measure (CycS I d β))
    (δ : CycData I d) : IsRCPath (envWalk ν δ) := by
  classical
  unfold envWalk
  by_cases h : CycGood ν
  · rw [ite_eq_left h]
    have hlen := envPath_len (δ := δ) (ν := ν) (h δ.copy)
    rw [← hlen.2]
    exact (envPath ν δ).1.rc
  · rw [ite_eq_right h]
    intro t
    exact Filter.Eventually.of_forall fun s => rfl

theorem isRCPath_sub_const {x : ℝ≥0 → Fin d → ℤ} (hx : IsRCPath x) (c : Fin d → ℤ) :
    IsRCPath (fun s => x s - c) := fun t => by
  filter_upwards [hx t] with s hs
  rw [hs]

theorem isRCPath_contGlue {b : ℝ≥0} (hb : 0 < b) {p : ℝ≥0 → Fin d → ℤ}
    {q : ℕ → ℝ≥0 → Fin d → ℤ} (hp : IsRCPath p) (hq : ∀ k, IsRCPath (q k)) :
    IsRCPath (contGlue b p q) := by
  have hpieces : ∀ k, IsRCPath (contPieces p q k) := by
    intro k; cases k with
    | zero => exact hp
    | succ k => exact hq k
  set σ := partialSums fun k => pathTreg b (contPieces p q k) with hσ
  have hm : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ, partialSums_succ]; exact le_self_add
  have h0 : σ 0 = 0 := by simp [hσ, partialSums]
  have hbdd := bdd_partialSums hb (τ := fun k => pathTreg b (contPieces p q k))
    (fun k => le_pathTreg b _)
  intro s
  exact gluedWalk_rc hm h0 hbdd (w := contPieces p q) (fun k s => hpieces k s) s

end ElboimSly.Paper.Step

end
