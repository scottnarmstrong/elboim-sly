/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauHat
public import ElboimSly.Paper.Heavy.PiecesRegen
public import ElboimSly.Paper.Heavy.ThrFinite
public import ElboimSly.Foundations.Concentration.GeometricMain

/-!
# The good event `𝒢` and Lemma 6.12

The events 𝒢(i) and 𝒢; ES22 Lemma 6.12 (§6; deviation F52).

In construction (i), with environments `ν k = cycSlice k (N ω)`, the `k`-th piece (ES22's piece
`k + 1`) is `fun s => cycWalk (ν k) 0 0 s`.

* `heavyGamma`: the set `Γ_n` of cyclic paths with `τ_fast ∧ τ_jump ∧ τ' ∧ τ_bad > T(w) ∧ t_n`.
* `heavyGoodPiece`, `heavyGood`: `𝒢(i)` and `𝒢 = {𝔑_{t_n} ≤ n³} ∩ ⋂_{i ≤ 𝔑_{t_n}} 𝒢(i)`.
* `es6_twelve_of_tauhat`: `P(𝒢^c) ≤ e^{-c_6 n³}`, given the geometric premise `P_{4^n}` (the
  premise of geometric domination of regenerations) and the per-piece bound of mathbbP(𝒢(i))ge1-e^-cn^3 as the distinctly
  named hypothesis `hGi`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The events 𝒢(i) and 𝒢. The set `Γ_n`. -/
def heavyGamma (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) : Prop :=
  IsCyclicPath w ∧
    min (cycClosingTime β w) (ENNReal.ofReal (indScale t₀ n)) <
      min (pathTfastCube w n) (min (pathTjumpCube w n)
        (min (heavyTauPrime d t₀ n w) (heavyTauBad d β t₀ n w)))

/-- The `k`-th piece of the regenerated walk in construction (i). -/
noncomputable def heavyPiece (ν : ℕ → Measure (RingSpace d β)) (k : ℕ) : ℝ → Fin d → ℤ :=
  fun s => cycWalk (ν k) 0 0 s

/-- The events 𝒢(i) and 𝒢. The event `𝒢`. -/
def heavyGood (d : ℕ) (β t₀ : ℝ) (n : ℕ) (ν : ℕ → Measure (RingSpace d β)) : Prop :=
  regenCount ν (indScale t₀ n) ≤ n ^ 3 ∧
    ∀ k ≤ regenCount ν (indScale t₀ n), heavyGamma d β t₀ n (heavyPiece ν k)

variable {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}

/-- ES22 Lemma 6.12, conditional on the per-piece bound `hGi` of mathbbP(𝒢(i))ge1-e^-cn^3. -/
theorem es6_twelve_of_tauhat {E : HeavyEscConsts} {n : ℕ} {t₀ : ℝ}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hd : 5 ≤ d) (hβ : 15 ≤ β) (hn : 4 ≤ n) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hP : GeoPremise Pe N ((4 : ℝ) ^ n))
    (hGi : ∀ k : ℕ, Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3))))
    (hT11 : Real.exp (-(n : ℝ) ^ 3) + ((n : ℝ) ^ 3 + 1) * heavyA d n *
      Real.exp (-(heavyc d E * n ^ 3)) ≤ Real.exp (-(heavyC6 d E * n ^ 3))) :
    Pe {ω | ¬ heavyGood d β t₀ n (geoSlices N ω)} ≤
      ENNReal.ofReal (Real.exp (-(heavyC6 d E * (n : ℝ) ^ 3))) := by
  have := hN.isProbabilityMeasure
  have htn0 : 0 ≤ indScale t₀ n := by
    unfold indScale; have : 0 ≤ t₀ := by linarith
    positivity
  have htn4 : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1) := indScale_le_four_pow ht4 n
  have hgeo := geo_count_ge_cube hN hd hβ hn hP htn0 htn4
  set A : ℝ := heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3)) with hA
  have hA0' : 0 ≤ heavyA d n := by
    unfold heavyA
    have := heavyCJ_pos (d := d)
    positivity
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hsum : ∑ _k ∈ Finset.range (n ^ 3 + 1), ENNReal.ofReal A =
      ENNReal.ofReal (((n : ℝ) ^ 3 + 1) * A) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.ofReal_mul (p := (n : ℝ) ^ 3 + 1) (by positivity)]
    congr 1
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  have hsub : {ω | ¬ heavyGood d β t₀ n (geoSlices N ω)} ⊆
      {ω | n ^ 3 ≤ regenCount (geoSlices N ω) (indScale t₀ n)} ∪
        ⋃ k ∈ Finset.range (n ^ 3 + 1),
          {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} := by
    intro ω hω
    simp only [heavyGood, not_and, not_forall, mem_union, mem_ofPred_eq, mem_iUnion,
      Finset.mem_range, exists_prop] at hω ⊢
    by_cases hR : regenCount (geoSlices N ω) (indScale t₀ n) ≤ n ^ 3
    · obtain ⟨k, hk, hkg⟩ := hω hR
      exact Or.inr ⟨k, by omega, hkg⟩
    · exact Or.inl (by omega)
  calc Pe {ω | ¬ heavyGood d β t₀ n (geoSlices N ω)}
      ≤ Pe ({ω | n ^ 3 ≤ regenCount (geoSlices N ω) (indScale t₀ n)} ∪
        ⋃ k ∈ Finset.range (n ^ 3 + 1),
          {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)}) := measure_mono hsub
    _ ≤ Pe {ω | n ^ 3 ≤ regenCount (geoSlices N ω) (indScale t₀ n)} +
        Pe (⋃ k ∈ Finset.range (n ^ 3 + 1),
          {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)}) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3))) +
        ∑ k ∈ Finset.range (n ^ 3 + 1),
          Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} :=
        add_le_add hgeo (measure_biUnion_finset_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3))) +
        ∑ _k ∈ Finset.range (n ^ 3 + 1), ENNReal.ofReal A :=
        add_le_add le_rfl (Finset.sum_le_sum fun k _ => hGi k)
    _ = ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3)) + ((n : ℝ) ^ 3 + 1) * A) := by
        rw [hsum, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        calc _ = Real.exp (-(n : ℝ) ^ 3) + ((n : ℝ) ^ 3 + 1) * heavyA d n *
              Real.exp (-(heavyc d E * n ^ 3)) := by rw [hA]; ring
          _ ≤ _ := hT11

end ElboimSly.Paper.Heavy
