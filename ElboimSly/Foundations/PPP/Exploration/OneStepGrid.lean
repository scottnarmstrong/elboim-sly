/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.OneStepDisc
import Mathlib

/-!
# One step: discrete stopping on a grid

The unexplored part after one step, Step 1.

`gridCeil h L r` is the smallest grid point `i h / L ≥ r`. With `t(ν) = gridCeil h L (ρ ν)` we prove
`E[g(St ν) 1_F(ν|_{D(t)ᶜ} + ν''|_{D(t)})] = E[g(St ν)] W(F)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

/-- The smallest grid point `i h / L` that is `≥ r`. -/
noncomputable def gridCeil (h : ℝ≥0) (L : ℕ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ i : Fin (L + 1), ⨅ (_ : r ≤ (gridTime h L i : ℝ≥0∞)), (gridTime h L i : ℝ≥0∞)

theorem le_gridCeil {h : ℝ≥0} {L : ℕ} {r : ℝ≥0∞} : r ≤ gridCeil h L r :=
  le_iInf fun _ => le_iInf fun hi => hi

theorem gridCeil_eq {h : ℝ≥0} {L : ℕ} (_hL : 0 < L) {r : ℝ≥0∞} {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ L)
    (hlt : (gridTime h L (i - 1) : ℝ≥0∞) < r) (hle : r ≤ gridTime h L i) :
    gridCeil h L r = gridTime h L i := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨i, by omega⟩ (iInf_le_of_le hle le_rfl)
  · refine le_iInf fun j => le_iInf fun hj => ?_
    have : i ≤ (j : ℕ) := by
      by_contra hcon
      have hjle : (gridTime h L j : ℝ≥0∞) ≤ gridTime h L (i - 1) := by
        exact_mod_cast gridTime_mono (show (j : ℕ) ≤ i - 1 by omega)
      exact absurd (lt_of_lt_of_le hlt (hj.trans hjle)) (lt_irrefl _)
    exact_mod_cast gridTime_mono this

section Step1

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

/-- `ψ_i(κ) = g(St^{≤ s_i}(κ)) 1{κ(D s_{i-1}) < 1, i = L ∨ κ(D s_i) ≥ 1}`. -/
noncomputable def gridPsi (μ : Measure S) [SigmaFinite μ] (R : S → ℝ≥0∞) (h : ℝ≥0) (L i : ℕ)
    (g : Outcome S → ℝ≥0∞) (κ : Measure S) : ℝ≥0∞ :=
  g (probeStep μ R (gridTime h L i) κ) *
    {κ : Measure S | κ (probeRegion R (gridTime h L (i - 1))) < 1 ∧
      (i = L ∨ 1 ≤ κ (probeRegion R (gridTime h L i)))}.indicator 1 κ

theorem measurable_gridPsi (hR : Measurable R) (L i : ℕ) {g : Outcome S → ℝ≥0∞}
    (hg : Measurable g) : Measurable (gridPsi μ R h L i g) := by
  unfold gridPsi
  refine (hg.comp (measurable_probeStep μ hR)).mul (measurable_one.indicator ?_)
  have hm : ∀ b, Measurable fun κ : Measure S => κ (probeRegion R b) := fun b =>
    Measure.measurable_coe (measurableSet_probeRegion hR b)
  exact (measurableSet_lt (hm _) measurable_const).inter
    ((MeasurableSet.const _).union (measurableSet_le measurable_const (hm _)))

theorem indicator_cellIndex_eq_gridPsi (hR : Measurable R) (hh : 0 < h) {L i : ℕ} (hi1 : 1 ≤ i)
    (hiL : i ≤ L) (g : Outcome S → ℝ≥0∞) {ν : Measure S} (hν : ν ∈ lfSet μ)
    (hreg : Reg R h Set.univ ν) :
    (cellIndex μ R h L i).indicator (fun ν => g (probeStep μ R h ν)) ν =
      gridPsi μ R h L i g (ν.restrict (probeRegion R (gridTime h L i))) := by
  have hL : 0 < L := by omega
  have hsi : (gridTime h L i : ℝ≥0) ≤ h := gridTime_le hL hiL
  have hab : (gridTime h L (i - 1) : ℝ≥0∞) ≤ gridTime h L i := by
    exact_mod_cast gridTime_mono (Nat.sub_le i 1)
  have hrest : ∀ a : ℝ≥0∞, a ≤ gridTime h L i →
      (ν.restrict (probeRegion R (gridTime h L i))) (probeRegion R a) = ν (probeRegion R a) := by
    intro a ha
    rw [Measure.restrict_apply (measurableSet_probeRegion hR _),
      Set.inter_eq_left.2 (probeRegion_mono ha)]
  have hprev : (gridTime h L (i - 1) : ℝ≥0∞) < h := by
    exact_mod_cast gridTime_lt hh (show i - 1 < L by omega)
  have hiff1 : probeRho μ R h ν ≤ gridTime h L (i - 1) ↔
      1 ≤ ν (probeRegion R (gridTime h L (i - 1))) := probeRho_le_iff hR hν hreg hprev
  have key : ν ∈ cellIndex μ R h L i ↔
      (ν (probeRegion R (gridTime h L (i - 1))) < 1 ∧
        (i = L ∨ 1 ≤ ν (probeRegion R (gridTime h L i)))) := by
    constructor
    · rintro ⟨hlt, hle⟩
      refine ⟨not_le.1 (fun hc => absurd (hiff1.2 hc) (not_le.2 hlt)), ?_⟩
      by_cases hiL' : i = L
      · exact Or.inl hiL'
      · right
        have hlt' : i < L := lt_of_le_of_ne hiL hiL'
        have : (gridTime h L i : ℝ≥0∞) < h := by exact_mod_cast gridTime_lt hh hlt'
        exact (probeRho_le_iff hR hν hreg this).1 hle
    · rintro ⟨h1, h2⟩
      refine ⟨not_le.1 (fun hc => absurd (hiff1.1 hc) (not_le.2 h1)), ?_⟩
      rcases h2 with rfl | h2
      · rw [gridTime_self h hL]; exact probeRho_le_h
      · by_cases hiL' : i = L
        · subst hiL'; rw [gridTime_self h hL]; exact probeRho_le_h
        · have hlt' : i < L := lt_of_le_of_ne hiL hiL'
          have : (gridTime h L i : ℝ≥0∞) < h := by exact_mod_cast gridTime_lt hh hlt'
          exact (probeRho_le_iff hR hν hreg this).2 h2
  unfold gridPsi
  by_cases hmem : ν ∈ cellIndex μ R h L i
  · rw [Set.indicator_of_mem hmem]
    have hc := key.1 hmem
    rw [Set.indicator_of_mem (show ν.restrict (probeRegion R (gridTime h L i)) ∈
      {κ : Measure S | κ (probeRegion R (gridTime h L (i - 1))) < 1 ∧
        (i = L ∨ 1 ≤ κ (probeRegion R (gridTime h L i)))} by
      show (ν.restrict _) _ < 1 ∧ (i = L ∨ 1 ≤ (ν.restrict _) _)
      rw [hrest _ hab, hrest _ le_rfl]; exact hc)]
    rw [Pi.one_apply, mul_one]
    exact congrArg g (probeStep_restrict hR hsi hν hmem.2).symm
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem, mul_zero]
    intro hcon
    apply hmem
    rw [key]
    have : (ν.restrict (probeRegion R (gridTime h L i))) (probeRegion R (gridTime h L (i - 1))) < 1 ∧
        (i = L ∨ 1 ≤ (ν.restrict (probeRegion R (gridTime h L i))) (probeRegion R (gridTime h L i))) :=
      hcon
    rw [hrest _ hab, hrest _ le_rfl] at this
    exact this

theorem sum_indicator_cellIndex (_hR : Measurable R) (_hh : 0 < h) {L : ℕ} (hL : 0 < L)
    (g : Outcome S → ℝ≥0∞) {ν : Measure S} (hne : probeRho μ R h ν ≠ 0) :
    ∑ i ∈ Finset.Icc 1 L, (cellIndex μ R h L i).indicator (fun ν => g (probeStep μ R h ν)) ν =
      g (probeStep μ R h ν) := by
  rcases exists_grid_index hL (r := probeRho μ R h ν) probeRho_le_h with h0 | ⟨i, hi1, hiL, hlt, hle⟩
  · exact absurd (le_antisymm h0 bot_le) hne
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_Icc.2 ⟨hi1, hiL⟩)]
    · rw [Set.indicator_of_mem (show ν ∈ cellIndex μ R h L i from ⟨hlt, hle⟩)]
    · intro j _ hji
      refine Set.indicator_of_notMem (fun hj => ?_) _
      exact Set.disjoint_left.1 (pairwiseDisjoint_cellIndex (μ := μ) (R := R) (h := h) L hji) hj
        (show ν ∈ cellIndex μ R h L i from ⟨hlt, hle⟩)

theorem aemeasurable_integrand (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) {L : ℕ}
    (hL : 0 < L) {g : Outcome S → ℝ≥0∞} (hg : Measurable g) {F : Set (Measure S)}
    (hF : MeasurableSet F) :
    AEMeasurable (fun p : Measure S × Measure S => g (probeStep μ R h p.1) *
        F.indicator 1 (renewAt (probeRegion R (gridCeil h L (probeRho μ R h p.1))) p))
        (W.prod W) := by
  have := hW.isProbabilityMeasure
  have hR := hP.measurable
  have hD : ∀ i, MeasurableSet (probeRegion R (gridTime h L i)) := fun i =>
    measurableSet_probeRegion hR _
  have hgs : Measurable fun ν : Measure S => g (probeStep μ R h ν) :=
    hg.comp (measurable_probeStep μ hR)
  have hgood : ∀ᵐ ν ∂W, ν ∈ lfSet μ ∧ Reg R h Set.univ ν ∧ probeRho μ R h ν ≠ 0 := by
    filter_upwards [ae_goodSet hW hP MeasurableSet.univ, ae_rho_ne_zero hW hP hh] with ν hν hne
    exact ⟨hν.1, hν.2.1, hne⟩
  have hgoodQ : ∀ᵐ p ∂(W.prod W), p.1 ∈ lfSet μ ∧ Reg R h Set.univ p.1 ∧
      probeRho μ R h p.1 ≠ 0 :=
    (measurePreserving_fst (μ := W) (ν := W)).quasiMeasurePreserving.ae hgood
  -- the integrand, a.e., is the sum over cells
  have hterm : ∀ i, Measurable fun p : Measure S × Measure S =>
      gridPsi μ R h L i g (p.1.restrict (probeRegion R (gridTime h L i))) *
        F.indicator 1 (renewAt (probeRegion R (gridTime h L i)) p) := fun i =>
    ((measurable_gridPsi hR L i hg).comp
      ((measurable_restrict_measure (hD i)).comp measurable_fst)).mul
      ((measurable_one.indicator hF).comp (measurable_renewAt (hD i)))
  have hae : (fun p : Measure S × Measure S => g (probeStep μ R h p.1) *
        F.indicator 1 (renewAt (probeRegion R (gridCeil h L (probeRho μ R h p.1))) p)) =ᵐ[W.prod W]
      fun p => ∑ i ∈ Finset.Icc 1 L, gridPsi μ R h L i g
        (p.1.restrict (probeRegion R (gridTime h L i))) *
          F.indicator 1 (renewAt (probeRegion R (gridTime h L i)) p) := by
    filter_upwards [hgoodQ] with p ⟨hlf, hreg, hne⟩
    rcases exists_grid_index hL (r := probeRho μ R h p.1) probeRho_le_h with h0 | ⟨i, hi1, hiL, hlt, hle⟩
    · exact absurd (le_antisymm h0 bot_le) hne
    · rw [gridCeil_eq hL hi1 hiL hlt hle]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_Icc.2 ⟨hi1, hiL⟩)]
      · rw [← indicator_cellIndex_eq_gridPsi hR hh hi1 hiL g hlf hreg,
          Set.indicator_of_mem (show p.1 ∈ cellIndex μ R h L i from ⟨hlt, hle⟩)]
      · intro j hj hji
        have hj' := Finset.mem_Icc.1 hj
        rw [← indicator_cellIndex_eq_gridPsi hR hh hj'.1 hj'.2 g hlf hreg,
          Set.indicator_of_notMem, zero_mul]
        exact fun hmem => Set.disjoint_left.1
          (pairwiseDisjoint_cellIndex (μ := μ) (R := R) (h := h) L hji) hmem
          (show p.1 ∈ cellIndex μ R h L i from ⟨hlt, hle⟩)
  exact (Finset.measurable_sum _ fun i _ => hterm i).aemeasurable.congr hae.symm

/-- The unexplored part after one step, Step 1: discrete stopping. -/
theorem lintegral_step_renewGrid (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) {L : ℕ}
    (hL : 0 < L) {g : Outcome S → ℝ≥0∞} (hg : Measurable g) {F : Set (Measure S)}
    (hF : MeasurableSet F) :
    ∫⁻ p, g (probeStep μ R h p.1) *
        F.indicator 1 (renewAt (probeRegion R (gridCeil h L (probeRho μ R h p.1))) p)
        ∂(W.prod W) = (∫⁻ ν, g (probeStep μ R h ν) ∂W) * W F := by
  have := hW.isProbabilityMeasure
  have hR := hP.measurable
  have hD : ∀ i, MeasurableSet (probeRegion R (gridTime h L i)) := fun i =>
    measurableSet_probeRegion hR _
  have hgs : Measurable fun ν : Measure S => g (probeStep μ R h ν) :=
    hg.comp (measurable_probeStep μ hR)
  have hgood : ∀ᵐ ν ∂W, ν ∈ lfSet μ ∧ Reg R h Set.univ ν ∧ probeRho μ R h ν ≠ 0 := by
    filter_upwards [ae_goodSet hW hP MeasurableSet.univ, ae_rho_ne_zero hW hP hh] with ν hν hne
    exact ⟨hν.1, hν.2.1, hne⟩
  have hgoodQ : ∀ᵐ p ∂(W.prod W), p.1 ∈ lfSet μ ∧ Reg R h Set.univ p.1 ∧
      probeRho μ R h p.1 ≠ 0 :=
    (measurePreserving_fst (μ := W) (ν := W)).quasiMeasurePreserving.ae hgood
  -- the integrand, a.e., is the sum over cells
  have hterm : ∀ i, Measurable fun p : Measure S × Measure S =>
      gridPsi μ R h L i g (p.1.restrict (probeRegion R (gridTime h L i))) *
        F.indicator 1 (renewAt (probeRegion R (gridTime h L i)) p) := fun i =>
    ((measurable_gridPsi hR L i hg).comp
      ((measurable_restrict_measure (hD i)).comp measurable_fst)).mul
      ((measurable_one.indicator hF).comp (measurable_renewAt (hD i)))
  have hae : (fun p : Measure S × Measure S => g (probeStep μ R h p.1) *
        F.indicator 1 (renewAt (probeRegion R (gridCeil h L (probeRho μ R h p.1))) p)) =ᵐ[W.prod W]
      fun p => ∑ i ∈ Finset.Icc 1 L, gridPsi μ R h L i g
        (p.1.restrict (probeRegion R (gridTime h L i))) *
          F.indicator 1 (renewAt (probeRegion R (gridTime h L i)) p) := by
    filter_upwards [hgoodQ] with p ⟨hlf, hreg, hne⟩
    rcases exists_grid_index hL (r := probeRho μ R h p.1) probeRho_le_h with h0 | ⟨i, hi1, hiL, hlt, hle⟩
    · exact absurd (le_antisymm h0 bot_le) hne
    · rw [gridCeil_eq hL hi1 hiL hlt hle]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_Icc.2 ⟨hi1, hiL⟩)]
      · rw [← indicator_cellIndex_eq_gridPsi hR hh hi1 hiL g hlf hreg,
          Set.indicator_of_mem (show p.1 ∈ cellIndex μ R h L i from ⟨hlt, hle⟩)]
      · intro j hj hji
        have hj' := Finset.mem_Icc.1 hj
        rw [← indicator_cellIndex_eq_gridPsi hR hh hj'.1 hj'.2 g hlf hreg,
          Set.indicator_of_notMem, zero_mul]
        exact fun hmem => Set.disjoint_left.1
          (pairwiseDisjoint_cellIndex (μ := μ) (R := R) (h := h) L hji) hmem
          (show p.1 ∈ cellIndex μ R h L i from ⟨hlt, hle⟩)
  rw [lintegral_congr_ae hae, lintegral_finsetSum _ fun i _ => hterm i]
  have hi : ∀ i ∈ Finset.Icc 1 L, ∫⁻ p, gridPsi μ R h L i g
      (p.1.restrict (probeRegion R (gridTime h L i))) *
        F.indicator 1 (renewAt (probeRegion R (gridTime h L i)) p) ∂(W.prod W) =
      (∫⁻ ν, (cellIndex μ R h L i).indicator (fun ν => g (probeStep μ R h ν)) ν ∂W) * W F := by
    intro i hi
    have hi' := Finset.mem_Icc.1 hi
    rw [lintegral_restrict_renewAt hW (hD i) (measurable_gridPsi hR L i hg) hF]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ν ⟨hlf, hreg, _⟩
    exact (indicator_cellIndex_eq_gridPsi hR hh hi'.1 hi'.2 g hlf hreg).symm
  rw [Finset.sum_congr rfl hi, ← Finset.sum_mul, ← lintegral_finsetSum]
  · congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with ν ⟨_, _, hne⟩
    exact sum_indicator_cellIndex hR hh hL g hne
  · exact fun i _ => hgs.indicator (measurableSet_cellIndex hR L i)

end Step1

end ElboimSly
