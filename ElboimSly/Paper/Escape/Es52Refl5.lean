/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Refl4
public import ElboimSly.Paper.Avoid.Setting
public import ElboimSly.Paper.Escape.Es52Meas3
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: `h_*N` is again an `Es4Setting`

ES22 Proposition 5.2 Step 2: "`h_*N \overset d = N`" -- here as the stronger structural statement
that `(Pr, h_*N, h_*N')` satisfies (S1)-(S2) with the same `𝒢₀`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}

/-- `ω ↦ h_*(N ω)`. -/
noncomputable def envRefl (N : Ω → Measure (CycS ℕ (k + 2) β)) : Ω → Measure (CycS ℕ (k + 2) β) :=
  fun ω => envMap (reflAut k) (N ω)

omit [Fact (0 < β)] in
theorem measurable_envMap_refl :
    Measurable (envMap (reflAut k) : Measure (ℕ × RingSpace (k + 2) β) → _) :=
  Measure.measurable_map _ (measurable_envMapFn _)

omit mΩ in
omit [Fact (0 < β)] in
theorem comap_envRefl_le (N : Ω → Measure (CycS ℕ (k + 2) β)) :
    MeasurableSpace.comap (envRefl N) inferInstance ≤ MeasurableSpace.comap N inferInstance := by
  have : envRefl N = envMap (reflAut k) ∘ N := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_envMap_refl.comap_le

theorem es4Setting_envRefl {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
    (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') :
    Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr (envRefl N) (envRefl N') where
  params := hS.params
  space :=
    { ppp := isPoissonPointProcess_envMap hS.space.ppp (reflAut k)
      ppp' := isPoissonPointProcess_envMap hS.space.ppp' (reflAut k)
      le := hS.space.le
      indep := indep_of_indep_of_le_right hS.space.indep (comap_envRefl_le N)
      indep' := indep_of_indep_of_le_right
        (indep_of_indep_of_le_left hS.space.indep'
          (comap_envRefl_le N')) (sup_le_sup_left (comap_envRefl_le N) _) }

theorem cycNgood_envRefl {N : Ω → Measure (CycS ℕ (k + 2) β)} {ω : Ω} (hω : CycGood (N ω)) :
    cycNgood (envRefl N) ω = envMap (reflAut k) (N ω) := by
  have : CycGood (envRefl N ω) := cycGood_envMap_of hω
  rw [cycNgood_of_good this]; rfl

end ElboimSly.Paper.Escape
