/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Times

/-!
# Pointwise attainment for the times of Lemma 7.8

Measurability, last sentence: if `ζ_i < t'_n` then `ζ_i ∈ 𝒯₂`,
`d(W₂(ζ_i), V) ≥ ρ_k` and `ζ_i < treg^{(2)}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- The infimum `inf {r ≥ R : r ∈ U}` of a set locally of type `[l, r)` is attained when finite. -/
theorem step78FirstGe_attained {U : Ω → Set ℝ} {R : Ω → WithTop ℝ≥0} {ω : Ω}
    (hloc : IsLocIco (U ω)) (h : step78FirstGe U R ω < ⊤) :
    ∃ r : ℝ≥0, (r : ℝ) ∈ U ω ∧ R ω ≤ r ∧ step78FirstGe U R ω = r := by
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 h.ne
  have h1 : step78FirstGe U R ω ≤ x := hx.symm ▸ le_rfl
  have h2 : (⨅ (u : ℝ≥0) (_ : (u : ℝ) ∈ U ω ∧ R ω < u), (u : WithTop ℝ≥0)) ≤ x := by
    have := step78FirstGe_eq_stepNextIn (U := fun _ : Unit => U ω) (R := fun _ => R ω)
      (fun _ => hloc)
    have e := congrFun this ()
    simp only [step78FirstGe, stepNextIn] at e h1
    rw [← e]; exact h1
  obtain ⟨u, hu, hRu, hux⟩ := (stepNextIn_le_iff hloc (R ω) x).1 h2
  refine ⟨u, hu, hRu, le_antisymm ?_ ?_⟩
  · exact iInf₂_le u ⟨hu, hRu⟩
  · rw [← hx]; exact WithTop.coe_le_coe.2 hux

/-- Closing of `w₂ = W₂ - u` (closing (b)): if `W₂(mβ) = u` for some `m ≥ 1` then
`W₂(r + mβ) = W₂(r)` for all `r ≥ 0`. -/
def Step78Closing (D : Step78Data d Ω) : Prop :=
  ∀ ω (k : ℕ), 1 ≤ k → D.w ((k : ℝ) * D.β).toNNReal ω = D.u →
    ∀ r : ℝ, 0 ≤ r → D.path ω (r + k * D.β) = D.path ω r

namespace Step78Data

variable {D : Step78Data d Ω} {f : Filtration ℝ≥0 m}

/-- A relaxed time is strictly below `treg^{(2)}`. -/
theorem lt_treg_of_relaxed (hF : Step78Frame D f) (hC : Step78Closing D) (ω : Ω) {r : ℝ≥0}
    (hr : (r : ℝ) ∈ D.relaxed ω) : (r : WithTop ℝ≥0) < D.treg ω := by
  by_contra hge
  rw [not_lt] at hge
  obtain ⟨k, hk1, hkt, hkw⟩ := (D.treg_le_iff hF ω r).1 hge
  have hkt' : (k : ℝ) * D.β ≤ r := by
    have h0 : 0 ≤ (k : ℝ) * D.β := by have := hF.hβ; positivity
    have := (Real.toNNReal_le_iff_le_coe).1 hkt
    exact this
  exact not_relaxed_of_periodic hF.hd hF.hβ hk1 hkt' (hC ω k hk1 hkw) hr.2

/-- **measurability, attainment** for `ζ_{i+1}`: if `ζ_{i+1} < t'_n` then `ζ_{i+1} = r` with
`r ∈ 𝒯₂`, `d(W₂(r), V) ≥ ρ`, `r < treg^{(2)}` and `ζ'_i ≤ r`. -/
theorem zeta_succ_attained (hF : Step78Frame D f) (hC : Step78Closing D) (ω : Ω) (i : ℕ)
    (h : D.zeta (i + 1) ω < (D.T : WithTop ℝ≥0)) :
    ∃ r : ℝ≥0, D.zeta (i + 1) ω = r ∧ (r : ℝ) ∈ D.relaxed ω ∧
      (∀ v ∈ D.V ω, D.ρ ≤ ‖D.w r ω - v‖) ∧ (r : WithTop ℝ≥0) < D.treg ω ∧
      D.zp i ω ≤ r := by
  have hz : D.zeta (i + 1) ω = min (D.T : WithTop ℝ≥0) (step78FirstGe D.farSet (D.zp i) ω) := rfl
  have hFT : step78FirstGe D.farSet (D.zp i) ω < (D.T : WithTop ℝ≥0) := by
    by_contra hh
    rw [not_lt] at hh
    rw [hz, min_eq_left hh] at h
    exact lt_irrefl _ h
  obtain ⟨r, hrU, hRr, hre⟩ := step78FirstGe_attained (locIco_far hF ω)
    (hFT.trans (WithTop.coe_lt_top _))
  refine ⟨r, ?_, hrU.1, ?_, lt_treg_of_relaxed hF hC ω hrU.1, hRr⟩
  · rw [hz, min_eq_right hFT.le, hre]
  · intro v hv
    have := hrU.2 v hv
    rwa [path_coe] at this

end Step78Data

end ElboimSly.Paper.Step

end
