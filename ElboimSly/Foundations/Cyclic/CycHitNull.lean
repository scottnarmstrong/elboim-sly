/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMarkovFilt
public import Mathlib

/-!
# ES22 Lemma 2.1, Step 1: `{T = ∞}` is independent of `N'`

ES22 Lemma 2.1, Step 1 ("`N'` is independent of `{T = ∞} ∈ σ(𝒢₀, N) ∨ 𝒩`").

* `aeSigma Pr m`: the σ-algebra of the sets that are almost surely equal to an `m`-set;
* `cycMarkovFilt_le_aeSigma`: `ℱ_t ≤ aeSigma Pr (𝒢₀ ⊔ σ(N))`;
* `measurableSet_top_aeSigma`: `{T = ∞}` is a.s. equal to a set of `𝒢₀ ⊔ σ(N)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

/-- The σ-algebra of the sets almost surely equal to a set of `m`. -/
@[instance_reducible] def aeSigma {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) (m : MeasurableSpace Ω) :
    MeasurableSpace Ω where
  MeasurableSet' s := ∃ t, MeasurableSet[m] t ∧ s =ᵐ[Pr] t
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m, Filter.EventuallyEq.rfl⟩
  measurableSet_compl := fun s ⟨t, ht, hst⟩ => ⟨tᶜ, @MeasurableSet.compl _ _ m ht, hst.compl⟩
  measurableSet_iUnion := fun s hs => by
    choose t ht hst using hs
    exact ⟨⋃ n, t n, @MeasurableSet.iUnion _ _ m _ _ ht, Filter.EventuallyEqSet.countable_iUnion hst⟩

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} (𝒢₀ : MeasurableSpace Ω)
  [mΩ : MeasurableSpace Ω]

theorem cycMarkovFilt_le_aeSigma (h𝒢 : 𝒢₀ ≤ mΩ) {N : Ω → Measure (RingSpace d β)}
    (hN : Measurable N) (Pr : Measure Ω) (t : ℝ≥0) :
    cycMarkovFilt 𝒢₀ h𝒢 hN Pr t ≤ aeSigma Pr (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) := by
  classical
  show 𝒢₀ ⊔ cycWalkFiltration Pr (markovNgood N) t ≤ _
  refine sup_le ?_ (sup_le ?_ ?_)
  · intro s hs
    exact ⟨s, (le_sup_left : 𝒢₀ ≤ 𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) s hs, Filter.EventuallyEq.rfl⟩
  · refine iSup₂_le fun r hr => ?_
    -- `W(r)` is a measurable function of `N`
    have hW : Measurable fun ν : Measure (RingSpace d β) =>
        ElboimSly.cycWalk (if Good ν then ν else 0) 0 0 (r : ℝ) := by
      have h1 : Measurable fun ν : Measure (RingSpace d β) =>
          (⟨if Good ν then ν else 0, by split_ifs with h; exacts [h, good_zero]⟩ : GoodSet d β) :=
        Measurable.subtype_mk (Measurable.ite measurableSet_good measurable_id measurable_const)
      exact (measurable_cycWalk 0 0 (NNReal.coe_nonneg r)).comp h1
    intro s hs
    obtain ⟨B, hB, rfl⟩ := hs
    refine ⟨(fun ω => ElboimSly.cycWalk (markovNgood N ω) 0 0 (r : ℝ)) ⁻¹' B, ?_,
      Filter.EventuallyEq.rfl⟩
    have : (fun ω => ElboimSly.cycWalk (markovNgood N ω) 0 0 (r : ℝ)) =
        (fun ν : Measure (RingSpace d β) =>
          ElboimSly.cycWalk (if Good ν then ν else 0) 0 0 (r : ℝ)) ∘ N := rfl
    rw [this, preimage_comp]
    exact (le_sup_right : MeasurableSpace.comap N inferInstance ≤ 𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) _ ⟨_, hW hB, rfl⟩
  · refine MeasurableSpace.generateFrom_le fun s hs => ?_
    refine ⟨∅, @MeasurableSet.empty _ (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance), ?_⟩
    exact (ae_eq_empty.2 hs.2)

end ElboimSly.Cyclic

end
