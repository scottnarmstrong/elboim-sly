/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Sets
public import ElboimSly.Paper.Avoid.Claim2Final
public import ElboimSly.Paper.Avoid.CoupleAux
public import Mathlib

/-!
# Hitting `N(V, 1)`

One excursion succeeds with probability at least frac12, "Hitting `N(V,1)`": ES22 Claim 4.2 applied to the regenerated
walk and the deterministic set `A = N(V,1) - x ⊆ {‖y‖ ≥ L}` with `L = ρ_k - 1` and
`|A ∩ [-r, r]^d| ≤ r^{8/3}` for `r ≥ L`: `P(∃ s ≤ 4ⁿ, x + W(s) ∈ N(V,1)) ≤ C_{42} L^{-1/30}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Cyclic

theorem measure_le_of_disjoint_large {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S E : Set Ω} (hS : MeasurableSet S) (hSE : Disjoint S E) {c : ℝ}
    (hc : 0 ≤ c) (h : ENNReal.ofReal (1 - c) ≤ μ E) : μ S ≤ ENNReal.ofReal c := by
  rcases le_or_gt 1 c with h1 | h1
  · exact (prob_le_one).trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1)
  · have hE : μ E ≤ μ Sᶜ := measure_mono hSE.symm.subset_compl_right
    rw [prob_compl_eq_one_sub hS] at hE
    have h2 : μ S + ENNReal.ofReal (1 - c) ≤ ENNReal.ofReal c + ENNReal.ofReal (1 - c) := by
      calc μ S + ENNReal.ofReal (1 - c) ≤ μ S + μ E := by gcongr
        _ ≤ μ S + (1 - μ S) := by gcongr
        _ = 1 := add_tsub_cancel_of_le prob_le_one
        _ = ENNReal.ofReal c + ENNReal.ofReal (1 - c) := by
            rw [← ENNReal.ofReal_add hc (by linarith)]; simp
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h2

variable {d : ℕ}

/-- **Hitting `N(V,1)`**. -/
theorem step78_law_Sv (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ), Es4Params d β n₀ n t₀ →
      ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {Pr₀ : Measure Ω₀} {N₀ : Ω₀ → Measure (CycS ℕ d β)},
        IsPoissonPointProcess N₀ (cycIntensity ℕ d β) Pr₀ →
      ∀ {L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ L → L ≤ (4 : ℝ) ^ n →
      ∀ (x : Fin d → ℤ) (V : Set (Fin d → ℤ)),
        (∀ u : Fin d → ℤ, (∃ v ∈ V, ‖x + u - v‖ ≤ 1) → L ≤ ‖u‖) →
        (∀ r : ℝ, L ≤ r → (({u : Fin d → ℤ | ∃ v ∈ V, ‖x + u - v‖ ≤ 1} ∩ {u | ‖u‖ ≤ r}).ncard : ℝ)
          ≤ r ^ (8 / 3 : ℝ)) →
        (Pr₀.map (avoidPath N₀)) (step78Sv n x V) ≤ ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 30)) := by
  obtain ⟨C, hC, H⟩ := es4_claim2 hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω₀ _ Pr₀ N₀ hN₀ L hL1 hL2 x V hA hcnt
  have := hN₀.isProbabilityMeasure
  set A : Set (Fin d → ℤ) := {u | ∃ v ∈ V, ‖x + u - v‖ ≤ 1} with hAdef
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL1
  have hc : 0 ≤ C * L ^ (-(1 : ℝ) / 30) := by positivity
  set X : Ω₀ → ℝ≥0 → Fin d → ℤ := avoidPath (cycNgood N₀) with hXdef
  have hXm : Measurable X := measurable_avoidPath_cycNgood hN₀.measurable
  have hXrc : ∀ ω, IsRCPath (X ω) := fun ω => isRCPath_avoidPath (cycGood_cycNgood N₀ ω)
  have hae : X =ᵐ[Pr₀] avoidPath N₀ := by
    filter_upwards [ae_avoidPath_cycNgood hN₀] with ω h
    exact h.1.trans h.2.symm
  have hlaw : Pr₀.map X = Pr₀.map (avoidPath N₀) := Measure.map_congr hae
  have h2 := (H β n₀ n t₀ hp Pr₀ N₀ hN₀ hL1 hL2 (A := A) hA hcnt).2 Pr₀ X hXm.aemeasurable hXrc hlaw
  rw [← hlaw, Measure.map_apply hXm (measurableSet_step78Sv n x V)]
  refine measure_le_of_disjoint_large (hXm (measurableSet_step78Sv n x V)) ?_ hc h2
  refine Set.disjoint_left.2 fun ω h1 h3 => ?_
  obtain ⟨s, -, hs4, v, hv, hvn⟩ := h1
  exact h3 s (by exact_mod_cast hs4.le) (⟨v, hv, hvn⟩ : X ω s ∈ A)

end ElboimSly.Paper.Step

end
