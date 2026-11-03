/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvZ
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncTrunc
public import ElboimSly.Foundations.Cyclic.CycTruncMeas
public import Mathlib

/-!
# The environment scheme (c): `cycRec(s')` is `𝒢_κ`-measurable

The environment scheme (c), last sentence. For a run of `cycScheme P s_∘ U` (`K ≥ 1`) and
`s' ≤ s_∘`, the truncation `cycRec^𝒫(s') = Trunc_{s'}(ρ^𝒫(N))` coincides almost surely with the
`𝒢_κ`-measurable random element `Trunc_{s'}(ρ_κ)` (`recKappa`):

* `inGkappa_trunc_recKappa`: `Trunc_{s'}(recKappa)` is `𝒢_κ`-measurable (`ExplRun.InGkappa`);
* `ae_trunc_recKappa_eq`: it equals `Trunc_{s'}(ρ^𝒫(N))` almost surely (uses `CycRec.trunc_trunc`);
* `exists_gKappa_measurable_cycRec`: the packaged statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {sc : ℝ≥0∞}
variable {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
variable (run : ExplRun (cycScheme P sc U) Pr)

/-- `Trunc_{s'}(ρ_κ)` is `𝒢_κ`-measurable. -/
theorem inGkappa_trunc_recKappa (junk : CycEntry I d) (s' : ℝ≥0) {B : Set (CycRec I d)}
    (hB : MeasurableSet B) :
    run.InGkappa (kappa run) {ω | CycRec.trunc s' (recKappa run junk ω) ∈ B} := by
  have : Nonempty (CycEntry I d) := ⟨junk⟩
  have hmt : Measurable fun ρ : CycRec I d => CycRec.trunc s' ρ :=
    measurable_trunc.comp (measurable_id.prodMk measurable_const)
  obtain ⟨Ainf, hAinf, hAeq⟩ := (isStopping_kappa run).top
  choose Ak hAk hAkeq using isStopping_kappa run
  refine ⟨fun k => ⟨Ak k ∩ {η | CycRec.trunc s' (CycScheme.stateAt P sc k η).1 ∈ B},
      (hAk k).inter ((hmt.comp (CycScheme.measurable_stateAt P sc k).fst) hB), ?_⟩,
    Ainf ∩ {y | CycRec.trunc s' (recPhi P sc U junk y) ∈ B},
      hAinf.inter ((hmt.comp (measurable_recPhi junk)) hB), ?_⟩
  · ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    have h1 := Set.ext_iff.1 (hAkeq k) ω
    simp only [mem_ofPred_eq, mem_preimage] at h1
    rw [← h1]
    constructor
    · rintro ⟨hG, hκ⟩
      refine ⟨hκ, ?_⟩
      unfold recKappa at hG
      rw [hκ] at hG
      simpa using hG
    · rintro ⟨hκ, hG⟩
      refine ⟨?_, hκ⟩
      unfold recKappa
      rw [hκ]
      simpa using hG
  · ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    have h1 := Set.ext_iff.1 hAeq ω
    simp only [mem_ofPred_eq, mem_preimage] at h1
    rw [← h1]
    constructor
    · rintro ⟨hG, hκ⟩
      refine ⟨hκ, ?_⟩
      unfold recKappa at hG
      rw [hκ] at hG
      simpa using hG
    · rintro ⟨hκ, hG⟩
      refine ⟨?_, hκ⟩
      unfold recKappa
      rw [hκ]
      simpa using hG

/-- Almost surely `Trunc_{s'}(ρ_κ) = Trunc_{s'}(ρ^𝒫(N)) = cycRec^𝒫(s')` for `s' ≤ s_∘`. -/
theorem ae_trunc_recKappa_eq (junk : CycEntry I d) (hK : 0 < P.K) {s' : ℝ≥0}
    (hs : (s' : ℝ≥0∞) ≤ sc) :
    ∀ᵐ ω ∂Pr, CycRec.trunc s' (recKappa run junk ω) =
      CycRec.trunc s' (P.envFinal (run.N ω)) := by
  filter_upwards [ae_recKappa_eq run junk hK] with ω h
  rw [h]
  unfold cycRecAt
  by_cases hsc : sc = ⊤
  · rw [ite_eq_left hsc]
  · rw [ite_eq_right hsc]
    have : s' ≤ sc.toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hsc]; exact hs
    exact CycRec.trunc_trunc junk this _

/-- The environment scheme (c), last sentence: for `s' ≤ s_∘`, `cycRec^𝒫(s')` coincides
almost surely with a `𝒢_κ`-measurable random element. -/
theorem exists_gKappa_measurable_cycRec (hK : 0 < P.K) {s' : ℝ≥0} (hs : (s' : ℝ≥0∞) ≤ sc) :
    ∃ Y : Ω → CycRec I d, (∀ B : Set (CycRec I d), MeasurableSet B →
        run.InGkappa (kappa run) (Y ⁻¹' B)) ∧
      ∀ᵐ ω ∂Pr, Y ω = CycRec.trunc s' (P.envFinal (run.N ω)) :=
  ⟨fun ω => CycRec.trunc s' (recKappa run P.junk ω),
    fun _ hB => inGkappa_trunc_recKappa run P.junk s' hB, ae_trunc_recKappa_eq run P.junk hK hs⟩

end CycSchemeEnv
end ElboimSly.Cyclic

end
