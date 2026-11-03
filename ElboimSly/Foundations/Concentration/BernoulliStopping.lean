/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.BernoulliDomination

/-!
# Bernoulli domination at stopping times

Domination by Bernoulli trials (c). For stopping times `s_0 ≤ s_1 ≤ … ≤ s_K` of a
filtration indexed by `ι`, the σ-algebras `𝒢_i = ℱ_{s_i}` increase, so (a) and (b) apply. We
prove the admissibility facts listed in the written proof:
`H ∩ {s_i < T}`, `H ∩ {s_i ≤ T}` lie in `ℱ_{s_i}`, and for `ι = ℝ≥0`,
`{s_i + L ≤ r_i} ∈ ℱ_{s_{i+1}}` when `s_i ≤ r_i ≤ s_{i+1}`.
-/

public section

namespace ElboimSly

open MeasureTheory NNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

section General

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] {ℱ : Filtration ι m0}

/-- Domination by Bernoulli trials (c): the event `H ∩ {s < T}` is `ℱ_s`-measurable
for stopping times `s_0 ≤ s` and `T`, and `H ∈ ℱ_{s_0}`. -/
theorem measurableSet_inter_lt_stopping {s₀ s T : Ω → WithTop ι} (h₀ : IsStoppingTime ℱ s₀)
    (hs : IsStoppingTime ℱ s) (hT : IsStoppingTime ℱ T) (h₀s : ∀ ω, s₀ ω ≤ s ω) {H : Set Ω}
    (hH : MeasurableSet[h₀.measurableSpace] H) :
    MeasurableSet[hs.measurableSpace] (H ∩ {ω | s ω < T ω}) := by
  refine (h₀.measurableSpace_mono hs h₀s H hH).inter ?_
  have := (hT.measurableSet_stopping_time_le hs).compl
  convert this using 1
  ext ω
  simp

end General

section Domination

variable {ι : Type*} [LinearOrder ι] {ℱ : Filtration ι m0}

/-- Lower-tail domination for stopping times. Domination by Bernoulli trials (c)
with (a). -/
theorem concBernoulli_lower_stopping [IsProbabilityMeasure μ] {K : ℕ} {s : ℕ → Ω → WithTop ι}
    (hs : ∀ i, IsStoppingTime ℱ (s i)) (hmono : ∀ i < K, ∀ ω, s i ω ≤ s (i + 1) ω)
    {G A : ℕ → Set Ω}
    (hG : ∀ i < K, MeasurableSet[(hs i).measurableSpace] (G i))
    (hA : ∀ i < K, MeasurableSet[(hs (i + 1)).measurableSpace] (A i))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hB : ∀ i < K, ∀ F, MeasurableSet[(hs i).measurableSpace] F →
      p * μ.real (G i ∩ F) ≤ μ.real (A i ∩ G i ∩ F)) (m : ℤ) :
    μ.real (concGamma G K ∩ {ω | (concCount A K ω : ℤ) ≤ m}) ≤ concBinomLE K p m :=
  concBernoulli_lower (𝒢 := fun i => (hs i).measurableSpace) (fun i _ => (hs i).measurableSpace_le)
    (fun i hi => (hs i).measurableSpace_mono (hs (i + 1)) (hmono i hi)) hG hA hp0 hp1 hB m

end Domination

section NNReal

variable {ℱ : Filtration ℝ≥0 m0}

/-- Domination by Bernoulli trials (c): for stopping times `s ≤ r ≤ s'` and a constant
`L ≥ 0`, the event `{s + L ≤ r}` lies in `ℱ_{s'}`. -/
theorem measurableSet_add_const_le_stopping {s r s' : Ω → WithTop ℝ≥0}
    (hs : IsStoppingTime ℱ s) (hr : IsStoppingTime ℱ r) (hs' : IsStoppingTime ℱ s')
    (hsr : ∀ ω, s ω ≤ r ω) (hrs' : ∀ ω, r ω ≤ s' ω) (L : ℝ≥0) :
    MeasurableSet[hs'.measurableSpace] {ω | s ω + (L : WithTop ℝ≥0) ≤ r ω} := by
  refine hr.measurableSpace_mono hs' hrs' _ ?_
  let _ : MeasurableSpace Ω := hr.measurableSpace
  have h1 : Measurable s := hs.measurable.mono (hs.measurableSpace_mono hr hsr) le_rfl
  have h2 : Measurable fun x : WithTop ℝ≥0 => x + (L : WithTop ℝ≥0) :=
    Monotone.measurable (fun a b h => by simpa using add_le_add_left h (L : WithTop ℝ≥0))
  exact measurableSet_le (h2.comp h1) hr.measurable

end NNReal

end ElboimSly
