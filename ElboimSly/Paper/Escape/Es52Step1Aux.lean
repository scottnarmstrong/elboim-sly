/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Step1Loc
public import ElboimSly.Paper.Escape.Es52Incl
public import ElboimSly.Paper.Escape.Es52Meas2
public import ElboimSly.Paper.Escape.Es52Meas3
public import ElboimSly.Paper.Escape.Es55Stmt
public import Mathlib

/-!
# ES22 Proposition 5.2 Step 1: the tower step and the disjointness of the `Con_i`

For a fixed `i`: a.s., `2 n^{-γ} Φ_{𝒦∩𝒜_i}(ρ^{𝒫₅}_{S₁}) ≤ Φ_{𝒦∩𝒜_i∩Con_i}(ρ^{𝒫₅}_{S₁})`, from
the tower property, `Es55Concl` and `resPhi_le_inter`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem indScale_pos' (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') : 0 < indScale t₀ n :=
  lt_trans (Fact.out : 0 < β) hS.params.beta_lt

/-- The events `Con_i` are pairwise disjoint (the point `p_i` determines `i`). -/
theorem escConSet_disjoint {n : ℕ} (hn : 2000 ≤ n) (u : Fin (k + 2) → ℤ) {i i' : ℕ}
    (h : i ≠ i') : Disjoint (escConSet β n u i) (escConSet β n u i') := by
  rw [Set.disjoint_left]
  intro ν h1 h2
  have e := h1.2.2.2.symm.trans h2.2.2.2
  exact h (escPoint_injective (escLambda_pos hn) e)

theorem plan5_K_pos (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β) :
    0 < (plan5 n β tn u β' i hlog).K := by
  rw [plan5_K]; exact_mod_cast Nat.succ_pos _

theorem lamT_le_lamTI (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β) :
    lamT (plan5 n β tn u β' i hlog) N 1 ≤ lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 1) := by
  intro ω
  unfold lamT
  exact lam_mono (by omega)

section generic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}

theorem resampleProb_mono (Λ : Measure (Measure (CycS I d β))) (M : Measure (CycS I d β))
    (R : Set (CycS I d β)) {X Y : Set (Measure (CycS I d β))} (h : X ⊆ Y) :
    resampleProb Λ M R X ≤ resampleProb Λ M R Y :=
  measure_mono fun _ hν => h hν

theorem resampleProb_union_le (Λ : Measure (Measure (CycS I d β))) (M : Measure (CycS I d β))
    (R : Set (CycS I d β)) (X Y : Set (Measure (CycS I d β))) :
    resampleProb Λ M R (X ∪ Y) ≤ resampleProb Λ M R X + resampleProb Λ M R Y :=
  measure_union_le _ _

end generic

/-- **The tower step of Step 1.**  For `1 ≤ i ≤ I`, given the conclusion of ES22 Lemma 5.5 for `i`:
a.s., `2 n^{-γ} Φ_{𝒦∩𝒜_i}(ρ_{S₁}) ≤ Φ_{𝒦∩𝒜_i∩Con_i}(ρ_{S₁})`, for the plan `𝒫₅(B, β', i)`. -/
theorem step1_tower (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (u : EscV k)
    (hadm : EscAdmissible (escJ n) u) (β' i : ℕ) (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n))
    (b : ℝ≥0∞)
    (H55 : ∀ᵐ ω ∂Pr, N ω ∈ escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i →
        b ≤ resPhi (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) Pr N
            (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
              (escIstar n (escJ n) + 1))
            (escConSet β n u i) ω) :
    ∀ᵐ ω ∂Pr, b * resPhi (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) Pr N
        (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N 1)
        (escKSet β (indScale t₀ n) n β' u ∩ escASet n u β' (hlog_of_params hS.params) i) ω ≤
      resPhi (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) Pr N
        (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N 1)
        (escKSet β (indScale t₀ n) n β' u ∩ escASet n u β' (hlog_of_params hS.params) i ∩
          escConSet β n u i) ω := by
  have hN := hS.space.ppp
  have hN' := hS.space.ppp'
  have h𝒢 := hS.space.le
  have hI1 := hS.space.indep
  have hI2 := hS.space.indep'
  have htn := indScale_pos' hS
  set hlog := hlog_of_params hS.params with hhlog
  set P := plan5 n β (indScale t₀ n) u β' i hlog with hP
  set Kset := escKSet β (indScale t₀ n) n β' u with hKset
  set Aset := escASet n u β' hlog i with hAset
  have hKm : MeasurableSet Kset := measurableSet_escKSet n _ u β' hlog hadm htn
  have hAm : MeasurableSet Aset := measurableSet_escASet n u β' hlog hi1 hiI
  have hCm : MeasurableSet (escConSet β n u i) := measurableSet_escConSet n u i
  have hT1 := isStoppingTime_lamT1 hS n u β' i hlog
  have hT2 := isStoppingTime_lamTI1 hS n u β' i hlog
  have hf1 := ae_lamT1_ne_top hS n u β' i hlog
  have hf2 := ae_lamTI1_ne_top hS n u β' i hlog
  have hH := measurableSet_KA_S2 hS u hadm htn β' i hlog hi1 hiI hT2
  have hle := resPhi_le_inter P 𝒢₀ hN hN' hI1 hI2 (plan5_K_pos n _ u β' i hlog) h𝒢 hT2 hf2
    (hKm.inter hAm) hCm hH
  have ha : ∀ᵐ ω ∂Pr, N ω ∈ Kset ∩ Aset → b ≤ resPhi P Pr N
      (lamT P N (escIstar n (escJ n) + 1)) (Kset ∩ Aset ∩ escConSet β n u i) ω := by
    filter_upwards [H55, hle] with ω h1 h2 hm
    exact (h1 hm).trans (h2 hm)
  exact resample_tower_lower P 𝒢₀ hN hN' hI1 hI2 (plan5_K_pos n _ u β' i hlog) h𝒢 hT1 hT2
    (lamT_le_lamTI n _ u β' i hlog) hf1 hf2 (hKm.inter hAm) ((hKm.inter hAm).inter hCm) hH ha

end ElboimSly.Paper.Escape
