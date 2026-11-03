/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Paper.Step.WalkPathAux
public import ElboimSly.Foundations.Brownian.Sup
public import Mathlib

/-!
# Exit probability of a walk with a Brownian coupling

Probability that a block is bad, condition (GB2), via (H4) and Gaussian maximal bound.

If the law of a random lattice path `F` on `[0, T]` admits a `(σ, ε)`-coupling with failure
probability `η` (`AdmitsBMCoupling`), then the probability that `F` leaves the ball of radius `R`
is at most `η + 4d exp(-(l/σ)²/(2T))` whenever `l + ε ≤ R`.  The event is reduced to rational
times (right-local constancy), the coupling's second coordinate is replaced by a standard Brownian
motion (`Bridge.exists_standardBrownianMotion_of_admitsBMCoupling`), and Gaussian maximal bound is applied to
`σ B`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

/-- A right-locally constant function on `[0, T]` that satisfies a property somewhere satisfies it
at a rational time or at `T`. -/
theorem exists_mem_walkCount_of_rlc {T : ℝ≥0} {α : Type*} {f : Set.Icc (0 : ℝ≥0) T → α}
    {p : α → Prop}
    (hrlc : ∀ q : Set.Icc (0 : ℝ≥0) T, ∃ ε > 0, ∀ q' : Set.Icc (0 : ℝ≥0) T, (q : ℝ≥0) ≤ q' →
      (q' : ℝ≥0) < q + ε → f q' = f q)
    (h : ∃ q, p (f q)) : ∃ q ∈ walkCount T, p (f q) := by
  obtain ⟨q, hq⟩ := h
  by_cases hqT : (q : ℝ≥0) = T
  · exact ⟨q, Or.inl hqT, hq⟩
  have hqlt : (q : ℝ≥0) < T := lt_of_le_of_ne q.2.2 hqT
  obtain ⟨ε, hε, hconst⟩ := hrlc q
  have hlt : ((q : ℝ≥0) : ℝ) < min ((q : ℝ≥0) + ε : ℝ≥0) T := by
    refine lt_min ?_ ?_
    · have : (q : ℝ≥0) < (q : ℝ≥0) + ε := lt_add_of_pos_right _ hε
      exact_mod_cast this
    · exact_mod_cast hqlt
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (NNReal.coe_nonneg _) hr1
  have hrT : (r : ℝ) ≤ T := (hr2.trans_le (min_le_right _ _)).le
  have hrq : (r : ℝ) < ((q : ℝ≥0) + ε : ℝ≥0) := hr2.trans_le (min_le_left _ _)
  set x : Set.Icc (0 : ℝ≥0) T := ⟨Real.toNNReal r, zero_le, by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0.le]; exact hrT⟩ with hx
  have hxr : ((x : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0.le
  refine ⟨x, Or.inr ⟨r, hxr⟩, ?_⟩
  have h1 : (q : ℝ≥0) ≤ x := by
    rw [← NNReal.coe_le_coe, hxr]; exact hr1.le
  have h2 : (x : ℝ≥0) < (q : ℝ≥0) + ε := by
    rw [← NNReal.coe_lt_coe, hxr]; exact hrq
  rw [hconst x h1 h2]; exact hq

/-- Exit probability from a coupling. -/
theorem exit_prob_of_coupling {T : ℝ≥0} (hT : T ≠ 0) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Ω → Set.Icc (0 : ℝ≥0) T → Fin d → ℤ} (hF : AEMeasurable F P)
    (hrlc : ∀ᵐ ω ∂P, ∀ q : Set.Icc (0 : ℝ≥0) T, ∃ ε > 0, ∀ q' : Set.Icc (0 : ℝ≥0) T,
      (q : ℝ≥0) ≤ q' → (q' : ℝ≥0) < q + ε → F ω q' = F ω q)
    {σ ε η R l : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hl : 0 < l) (hlR : l + ε ≤ R)
    (hc : AdmitsBMCoupling d T (P.map F) σ ε η) :
    P {ω | ∃ t, R < ‖F ω t‖} ≤ ENNReal.ofReal η +
      (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(l / σ) ^ 2 / (2 * T))) := by
  obtain ⟨Q, hQp, hQmap, hB, -, hfail⟩ := Bridge.exists_standardBrownianMotion_of_admitsBMCoupling hc
  set Bm := Bridge.zeroMod (Prod.snd : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → _) with hBm
  let M : Set (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) := {f | ∃ q ∈ walkCount T, R < ‖f q‖}
  have hM : MeasurableSet M := by
    have : M = ⋃ q ∈ walkCount T, {f | R < ‖f q‖} := by
      ext f; simp [M]
    rw [this]
    refine MeasurableSet.biUnion (walkCount_countable T) fun q _ => ?_
    exact measurableSet_lt measurable_const
      ((measurable_of_countable (fun v : Fin d → ℤ => ‖v‖)).comp (measurable_pi_apply q))
  have hmeasfst : Measurable (fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  -- Step 1: reduce to rational times
  have hsub : {ω | ∃ t, R < ‖F ω t‖} ≤ᵐ[P] F ⁻¹' M := by
    filter_upwards [hrlc] with ω hω hmem
    obtain ⟨t, ht⟩ := hmem
    exact exists_mem_walkCount_of_rlc (f := F ω) (p := fun v => R < ‖v‖) hω ⟨t, ht⟩
  -- Step 2: transfer to the coupling
  have hstep2 : P (F ⁻¹' M) = Q ((fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' M) := by
    rw [← Measure.map_apply_of_aemeasurable hF hM, ← hQmap, Measure.map_apply hmeasfst hM]
  -- Step 3: split off the failure event
  let Fl : Set (WalkPath d T × C(ℝ≥0, Fin d → ℝ)) := {p | ENNReal.ofReal ε ≤
    ⨆ t : Set.Icc (0 : ℝ≥0) T,
      ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bm (t : ℝ≥0) p‖}
  let Sb : Set (WalkPath d T × C(ℝ≥0, Fin d → ℝ)) := {p | ∃ u ≤ T, l ≤ ‖σ • Bm u p‖}
  have hcover : (fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' M ⊆ Fl ∪ Sb := by
    intro p hp
    by_cases hpF : p ∈ Fl
    · exact Or.inl hpF
    · refine Or.inr ?_
      obtain ⟨q, -, hq⟩ := hp
      have hlt : ¬ ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) T,
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bm (t : ℝ≥0) p‖ := hpF
      rw [not_le] at hlt
      have h3 := (le_iSup (fun t : Set.Icc (0 : ℝ≥0) T =>
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bm (t : ℝ≥0) p‖) q).trans_lt hlt
      have h4 : ‖(fun i => ((p.1.1 q i : ℤ) : ℝ)) - σ • Bm (q : ℝ≥0) p‖ < ε :=
        (ENNReal.ofReal_lt_ofReal_iff hε).1 h3
      refine ⟨q, q.2.2, ?_⟩
      have h5 : ‖p.1.1 q‖ ≤ ‖σ • Bm (q : ℝ≥0) p‖ + ε := by
        rw [← norm_intCast_pi]
        have := norm_le_norm_add_norm_sub' (fun i => ((p.1.1 q i : ℤ) : ℝ)) (σ • Bm (q : ℝ≥0) p)
        linarith
      linarith
  -- Step 4: bound the two events
  have hQp' : IsProbabilityMeasure Q := hQp
  have hFl : Q Fl ≤ ENNReal.ofReal η := hfail
  have hSb : Q Sb ≤ (4 * d : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(l / σ) ^ 2 / (2 * T))) :=
    hB.sup_norm_smul_le hT hl hσ
  calc P {ω | ∃ t, R < ‖F ω t‖} ≤ P (F ⁻¹' M) := measure_mono_ae hsub
    _ = Q ((fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' M) := hstep2
    _ ≤ Q (Fl ∪ Sb) := measure_mono hcover
    _ ≤ Q Fl + Q Sb := measure_union_le _ _
    _ ≤ _ := add_le_add hFl hSb

end ElboimSly.Paper.Heavy
