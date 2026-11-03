/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Refl6
public import ElboimSly.Paper.Escape.Es52Aux
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: `π_{B̃}(h_*N) ≤ π_B(N)` almost surely

ES22 Proposition 5.2 Step 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem escTg_envRefl {tn : ℝ} {u : Fin (k + 2) → ℤ} {ω : Ω} (hω : CycGood (N ω)) :
    escTg (envRefl N) tn n (reflU (escJ n) u) ω = escTg N tn n u ω := by
  unfold escTg escT0
  rw [cycNgood_envRefl hω, cycNgood_of_good hω, escXi_envMap hω]

theorem escPiG_eq_Tg {tn : ℝ} {u : Fin (k + 2) → ℤ} {ω : Ω} (hω : CycGood (N ω)) :
    escPiG Pr N n tn u ω =
      resampleInt (regPlan (k + 2) β) Pr N (escTg N tn n u) (fun p => escYg n tn u p.2) ω := by
  have hTeq : escT N tn (escBlock (escJ n) u) ω = escTg N tn n u ω := by
    show _ = ((escT0 β tn n u (cycNgood N ω) : ℝ≥0) : WithTop ℝ≥0)
    rw [cycNgood_of_good hω]; rfl
  simp only [escPiG, resampleInt, cycRecStop, cycRegionStop, SRW.stopReal, hTeq]

omit [Fact (0 < β)] mΩ in
theorem cycRegionStop_congr {P : CycPlan ℕ (k + 2) β} {M : Ω → Measure (CycS ℕ (k + 2) β)}
    {T T' : Ω → WithTop ℝ≥0} {ω : Ω} (h : T ω = T' ω) :
    cycRegionStop P M T ω = cycRegionStop P M T' ω := by
  unfold cycRegionStop; rw [h]

omit [Fact (0 < β)] mΩ in
theorem cycRecStop_congr {P : CycPlan ℕ (k + 2) β} {M : Ω → Measure (CycS ℕ (k + 2) β)}
    {T T' : Ω → WithTop ℝ≥0} {ω : Ω} (h : T ω = T' ω) :
    cycRecStop P M T ω = cycRecStop P M T' ω := by
  unfold cycRecStop SRW.stopReal; rw [h]

theorem cycRegionStop_envRefl {T : Ω → WithTop ℝ≥0} {ω : Ω} (hω : CycGood (N ω)) :
    cycRegionStop (regPlan (k + 2) β) (cycNgood (envRefl N)) T ω =
      psiE k β ⁻¹' cycRegionStop (regPlan (k + 2) β) (cycNgood N) T ω := by
  ext x
  rw [mem_preimage, mem_cycRegionStop_iff, mem_cycRegionStop_iff]
  refine and_congr_right fun _ => ?_
  unfold cycRecStop
  rw [cycNgood_envRefl hω, cycNgood_of_good hω]
  exact region_trunc_envMap hω _ x

/-- **`π_{B̃}(h_*N) ≤ π_B(N)`** almost surely on the good environments. -/
theorem escPiG_envRefl_le (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (tn : ℝ)
    (u : Fin (k + 2) → ℤ) :
    ∀ᵐ ω ∂Pr, CycGood (N ω) →
      escPiG Pr (envRefl N) n tn (reflU (escJ n) u) ω ≤ escPiG Pr N n tn u ω := by
  have hS' := es4Setting_envRefl hS
  have hK : 0 < (regPlan (k + 2) β).K := by simp [regPlan, closingPlan]
  have rm1 := (cyc_multi_exploration_a (regPlan (k + 2) β) 𝒢₀ hS.space.ppp hS.space.ppp'
    hS.space.indep hS.space.indep' hK hS.space.le (isStoppingTime_escTg hS tn u)).2.2.2.1
  have rm2 := (cyc_multi_exploration_a (regPlan (k + 2) β) 𝒢₀ hS'.space.ppp hS'.space.ppp'
    hS'.space.indep hS'.space.indep' hK hS'.space.le
    (isStoppingTime_escTg hS' tn (reflU (escJ n) u))).2.2.2.1
  filter_upwards [rm1, rm2] with ω h1 h2 hω
  have hTT := escTg_envRefl (N := N) (n := n) (tn := tn) (u := u) hω
  have hω' : CycGood (envRefl N ω) := cycGood_envMap_of hω
  set T := escTg N tn n u with hT
  rw [escPiG_eq_Tg hω, escPiG_eq_Tg hω']
  have h1' := h1 (escTg_ne_top N tn n u ω)
  have h2' := h2 (escTg_ne_top (envRefl N) tn n _ ω)
  rw [cycRegionStop_congr hTT, cycRecStop_congr hTT] at h2'
  unfold resampleInt
  rw [cycRegionStop_congr hTT, cycRecStop_congr hTT, ← h2', cycRegionStop_envRefl hω]
  rw [← h1']
  have hmap : (Pr.map (envRefl N)) = (Pr.map N).map (envMap (reflAut k)) := by
    rw [Measure.map_map measurable_envMap_refl hS.space.ppp.measurable]
    rfl
  rw [hmap]
  exact key_integral n tn u (N ω) _ _

end ElboimSly.Paper.Escape
