/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Refl7
public import ElboimSly.Paper.Escape.Es52Step1Sum
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: the half `W(ξ_B) ∈ B⁺`, by reflection

ES22 Proposition 5.2 proof, Step 2.  The `B⁺`-half for `N` is contained (up to a null set) in the
`B̃⁻`-half for `h_*N`, where `(Pr, h_*N, h_*N')` is again a setting (`es4Setting_envRefl`) and
`π_{B̃}(h_*N) ≤ π_B(N)` (`escPiG_envRefl_le`); Step 1 applies to `B̃` (admissible, whatever its
corner).  The hypotheses `H55`, `h54` are those of Step 1, for the reflected setting.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem one_le_escJ {n : ℕ} (hn : 2000 ≤ n) : 1 ≤ escJ n := by
  by_contra h
  have h0 : escJ n = 0 := by omega
  have := le_two_pow_escJ n
  rw [h0] at this
  have h2 : 1 < n ^ 20 := Nat.one_lt_pow (by norm_num) (by omega)
  simp at this
  omega

/-- **Step 2 of ES22 Proposition 5.2** (conditional on the Step 1 inputs for the reflected setting). -/
theorem es52_step2 (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (hn : 2000 ≤ n)
    (hlb : Real.log β ≤ (n : ℝ) ^ 40) (u : Fin (k + 2) → ℤ) (hu : u ≠ 0)
    (hadm : EscAdmissible (escJ n) u)
    (H55 : ∀ β' i, 1 ≤ i → i ≤ escIstar n (escJ n) →
      ∀ᵐ ω ∂Pr, envRefl N ω ∈ escKSet β (indScale t₀ n) n β' (reflU (escJ n) u) ∩
          escASet n (reflU (escJ n) u) β' (hlog_of_params hS.params) i →
        2 * ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2))) ≤
          resPhi (plan5 n β (indScale t₀ n) (reflU (escJ n) u) β' i (hlog_of_params hS.params)) Pr
            (envRefl N)
            (lamT (plan5 n β (indScale t₀ n) (reflU (escJ n) u) β' i
              (hlog_of_params hS.params)) (envRefl N) (escIstar n (escJ n) + 1))
            (escConSet β n (reflU (escJ n) u) i) ω)
    (h54 : ∀ β', 1 - (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n) ≤
          Pr {ω | ∃ ℓ, ℓ < escIstar n (escJ n) ∧
            (escEntry n (reflU (escJ n) u) β' (hlog_of_params hS.params)
              (cycNgood (envRefl N) ω) ℓ).len = (4 : ℝ≥0∞) ^ n}) :
    Pr {ω | CycGood (N ω) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal (indScale t₀ n) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escWalk (N ω) (escXi (escWalk (N ω)) (escBlock (escJ n) u)).toReal ∈
          escBlockPlus (escJ n) u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} ≤
      ⌈β⌉₊ * (2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n)) := by
  have hS' := es4Setting_envRefl hS
  have hadm' : EscAdmissible (escJ n) (reflU (escJ n) u) := reflAut_admissible hadm hu
  have hj := one_le_escJ hn
  refine le_trans (measure_mono_ae ?_) (es52_step1_sum hS' hn hlb _ hadm' H55 h54)
  filter_upwards [escPiG_envRefl_le hS (indScale t₀ n) u] with ω hπ hω
  obtain ⟨hg, h1, h2, h3, h4⟩ := hω
  have hg' : CycGood (envMap (reflAut k) (N ω)) := cycGood_envMap_of hg
  show CycGood (envMap (reflAut k) (N ω)) ∧ _
  refine ⟨hg', ?_, ?_, ?_, ?_⟩
  · simp only [envRefl]; rw [escXi_envMap hg]; exact h1
  · simp only [envRefl]; rw [escXi_envMap hg, cycTreg_copyEnv_envMap hg]; exact h2
  · simp only [envRefl]; rw [escXi_envMap hg, escWalk_envMap hg ENNReal.toReal_nonneg]
    exact (reflAut_mem_blockMinus hj).2 h3
  · exact (hπ hg).trans h4

end ElboimSly.Paper.Escape
