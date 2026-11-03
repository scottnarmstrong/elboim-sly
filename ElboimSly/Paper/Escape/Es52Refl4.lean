/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Refl3
public import ElboimSly.Paper.Escape.Es52Aux
public import ElboimSly.Paper.Escape.Es52Meas2
public import ElboimSly.Paper.Step.RegenMeas
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: equivariance of the regenerated walk, `ξ_B`, `Y_B`

ES22 Proposition 5.2 Step 2: "the regenerated walk and the records of `h_*N` are the images
under `h` of those of `N`.  As `h` preserves `‖·‖`, `ξ_{B̃}(h_*N) = ξ_B(N)`, `ℰ` is preserved".
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace (k + 2) β)}

theorem norm_reflAut (x : Fin (k + 2) → ℤ) : ‖(reflAut k).toEquiv x‖ = ‖x‖ := by
  have h : ∀ y : Fin (k + 2) → ℤ, ‖(reflAut k).toEquiv y‖ ≤ ‖y‖ := by
    intro y
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
    by_cases hc : c = 0
    · subst hc; simp only [reflAut_apply, ite_true, norm_neg]; exact norm_le_pi_norm y 0
    · simp only [reflAut_apply, hc, ite_false]; exact norm_le_pi_norm y c
  exact le_antisymm (h x) (by simpa [reflAut_invol] using h ((reflAut k).toEquiv x))

theorem reflAut_sub (a b : Fin (k + 2) → ℤ) :
    (reflAut k).toEquiv a - (reflAut k).toEquiv b = (reflAut k).toEquiv (a - b) := by
  funext c; by_cases hc : c = 0 <;> simp [reflAut_apply, hc]; ring

theorem norm_reflAut_sub (a b : Fin (k + 2) → ℤ) :
    ‖(reflAut k).toEquiv a - (reflAut k).toEquiv b‖ = ‖a - b‖ := by
  rw [reflAut_sub, norm_reflAut]

/-- The regenerated walk of `h_*ν` is `h ∘ W`. -/
theorem escWalk_envMap (hν : CycGood ν) {x : ℝ} (hx : 0 ≤ x) :
    escWalk (envMap (reflAut k) ν) x = (reflAut k).toEquiv (escWalk ν x) := by
  have h := regenWalk_latticeMeasure (ν := fun i => copyEnv ν i)
    (fun i => by rw [copyEnv_eq_cycSlice]; exact hν i) (reflAut k) reflAut_zero x.toNNReal
  rw [Real.coe_toNNReal x hx] at h
  unfold escWalk
  have e : (fun i => copyEnv (envMap (reflAut k) ν) i) =
      fun i => latticeMeasure (reflAut k) (copyEnv ν i) := by
    funext i
    rw [copyEnv_eq_cycSlice, copyEnv_eq_cycSlice, cycSlice_envMap_refl]
  rw [e]
  exact h

theorem escXi_envMap {j : ℕ} {u : Fin (k + 2) → ℤ} (hν : CycGood ν) :
    escXi (escWalk (envMap (reflAut k) ν)) (escBlock j (reflU j u)) =
      escXi (escWalk ν) (escBlock j u) := by
  unfold escXi
  refine iInf_congr fun t => iInf_congr_Prop ?_ fun _ => rfl
  rw [escWalk_envMap hν (NNReal.coe_nonneg t), reflAut_mem_block]

theorem cycTreg_copyEnv_envMap (hν : CycGood ν) :
    cycTreg (copyEnv (envMap (reflAut k) ν) 0) = cycTreg (copyEnv ν 0) := by
  rw [copyEnv_eq_cycSlice, copyEnv_eq_cycSlice]
  exact treg_envMap hν 0

theorem escEvent_envMap {n j : ℕ} (hν : CycGood ν) {T : ℝ} (hT : 0 ≤ T) :
    EscEvent n j (escWalk (envMap (reflAut k) ν)) T ↔ EscEvent n j (escWalk ν) T := by
  unfold EscEvent
  refine forall_congr' fun s => ?_
  refine imp_congr_right fun hs1 => imp_congr_right fun hs2 => ?_
  have hs0 : 0 ≤ s := le_trans (by positivity) hs1
  rw [escWalk_envMap hν (by linarith), escWalk_envMap hν hT, norm_reflAut_sub]

theorem escYg_envMap {n : ℕ} {tn : ℝ} {u : Fin (k + 2) → ℤ} (μ : Measure (ℕ × RingSpace (k + 2) β)) :
    escYg n tn (reflU (escJ n) u) (envMap (reflAut k) μ) = escYg n tn u μ := by
  classical
  unfold escYg
  by_cases hμ : CycGood μ
  · rw [ite_eq_left (cycGood_envMap_of hμ), ite_eq_left hμ]
    unfold escY
    rw [escXi_envMap hμ]
    by_cases hc : escXi (escWalk μ) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn
    · by_cases he : EscEvent n (escJ n) (escWalk μ) (escXi (escWalk μ) (escBlock (escJ n) u)).toReal
      · rw [ite_eq_left ⟨hc, (escEvent_envMap hμ ENNReal.toReal_nonneg).2 he⟩, ite_eq_left ⟨hc, he⟩]
      · rw [ite_eq_right (fun h => he ((escEvent_envMap hμ ENNReal.toReal_nonneg).1 h.2)),
          ite_eq_right (fun h => he h.2)]
    · rw [ite_eq_right (fun h => hc h.1), ite_eq_right (fun h => hc h.1)]
  · rw [ite_eq_right (fun h => hμ (cycGood_envMap_iff.1 h)), ite_eq_right hμ]

end ElboimSly.Paper.Escape
