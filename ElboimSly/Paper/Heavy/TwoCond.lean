/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.EscInterface
public import ElboimSly.Paper.Heavy.TwoGap
public import ElboimSly.Paper.Heavy.CondexpLocal
public import ElboimSly.Foundations.Concentration.GapCount
public import ElboimSly.Foundations.Concentration.BernoulliConditional

/-!
# Lemma 6.2, Step 2: the conditional success probability

ES22 Lemma 6.2, Step 2.

For a stopping time `T̄ ≤ τ_V` (finite) and `i ≥ 1`, almost surely on `{s_i < T̄}`,
`P(s_{i+1} ≥ s_i + 4^n | ℱ_{s_i}) ≥ c`.  The proof covers `{s_i < T̄}` by the events
`Λ_{B''} = {s_i < T̄} ∩ {s_i = ξ_{B''}}` and localizes the conditional expectation
(localizing conditional expectations at stopping times).  The measurability of the escape events enters as `hE`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {f : Filtration ℝ≥0 m0}
  {W : Ω → ℝ → Fin d → ℤ}

/-- The success event `A_i = {s_{i+1} ≥ s_i + 4^n}`. -/
def heavyGapSet (W : Ω → ℝ → Fin d → ℤ) (n m : ℕ) (ι : Fin d → ℤ) (i : ℕ) : Set Ω :=
  {ω | heavySi (W ω) n m ι i + ENNReal.ofReal ((4 : ℝ) ^ n) ≤ heavySi (W ω) n m ι (i + 1)}

theorem measurableSet_heavyGapSet (hAd : AdaptedCyclic f W) (n m : ℕ)
    (ι : Fin d → ℤ) (i : ℕ) :
    MeasurableSet[(hAd.isStoppingTime_heavySi (n := n) m ι (i + 1)).measurableSpace]
      (heavyGapSet W n m ι i) := by
  have hs := hAd.isStoppingTime_heavySi (n := n) m ι i
  have hs1 := hAd.isStoppingTime_heavySi (n := n) m ι (i + 1)
  exact measurableSet_add_const_le_stopping hs hs1 hs1
    (fun ω => heavyEntSeq_mono (Nat.le_succ i)) (fun ω => le_rfl) ((4 : ℝ) ^ n).toNNReal

theorem measurableSet_heavyGapSet' (hAd : AdaptedCyclic f W) (n m : ℕ)
    (ι : Fin d → ℤ) (i : ℕ) : MeasurableSet (heavyGapSet W n m ι i) :=
  (hAd.isStoppingTime_heavySi (n := n) m ι (i + 1)).measurableSpace_le _
    (measurableSet_heavyGapSet hAd n m ι i)

theorem heavyEscSet_subset_gap (hAd : AdaptedCyclic f W) {n m : ℕ} (hn : 1 ≤ n)
    (hjm : heavyScaleJ n ≤ m) (ι : Fin d → ℤ) (i : ℕ) {ω : Ω}
    (hi : heavySi (W ω) n m ι i < ⊤)
    (hω : ω ∈ heavyEscSet W n (heavyScaleJ n) (fun ω => heavySi (W ω) n m ι i)) :
    ω ∈ heavyGapSet W n m ι i :=
  heavy_gap_of_escape hn (hAd.path ω) hjm i hi hω.2

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- ES22 Lemma 6.2, Step 2. -/
theorem heavy_cond_gap (hAd : AdaptedCyclic f W) {n m : ℕ} (hn : 1 ≤ n)
    (hjm : heavyScaleJ n ≤ m) (ι : Fin d → ℤ) {i : ℕ} (hi : 1 ≤ i)
    (hE : ∀ ι', MeasurableSet
      (heavyEscSet W n (heavyScaleJ n) (heavyXi W (heavyScaleJ n) ι')))
    {Tbar : Ω → ℝ≥0∞} (hT : IsStoppingTime f Tbar) (hTfin : ∀ ω, Tbar ω ≠ ⊤) {c : ℝ}
    (hTV : ∀ ω, Tbar ω ≤ heavyTauV (W ω) (heavyScaleJ n)
      (fun ι' => heavyEscVersion hAd μ n ι' ω) c) :
    ∀ᵐ ω ∂μ, heavySi (W ω) n m ι i < Tbar ω →
      c ≤ μ[(heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ)) |
        (hAd.isStoppingTime_heavySi (n := n) m ι i).measurableSpace] ω := by
  classical
  set j := heavyScaleJ n with hj
  have hS : IsStoppingTime f (fun ω => heavySi (W ω) n m ι i) :=
    hAd.isStoppingTime_heavySi (n := n) m ι i
  have hgm : MeasurableSet (heavyGapSet W n m ι i) := measurableSet_heavyGapSet' hAd n m ι i
  have hgint : Integrable ((heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hgm
  have key : ∀ ι' : Fin d → ℤ, ∀ᵐ ω ∂μ, ω ∈ ({ω | heavySi (W ω) n m ι i < Tbar ω} ∩
      {ω | heavySi (W ω) n m ι i = heavyXi W j ι' ω}) →
      c ≤ μ[(heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ)) | hS.measurableSpace] ω := by
    intro ι'
    have hξ : IsStoppingTime f (heavyXi W j ι') := hAd.isStoppingTime_entrance _
    set Λ : Set Ω := {ω | heavySi (W ω) n m ι i < Tbar ω} ∩
      {ω | heavySi (W ω) n m ι i = heavyXi W j ι' ω} with hΛ
    have hlt : MeasurableSet[hS.measurableSpace] {ω | heavySi (W ω) n m ι i < Tbar ω} := by
      have := measurableSet_inter_lt_stopping hS hS hT (fun ω => le_rfl)
        (H := Set.univ) MeasurableSet.univ
      rwa [Set.univ_inter] at this
    have heq : MeasurableSet[hS.measurableSpace] {ω | heavySi (W ω) n m ι i = heavyXi W j ι' ω} :=
      (measurableSet_eq_stopping_time_both hS hξ).1
    have hΛm : MeasurableSet[hS.measurableSpace] Λ := hlt.inter heq
    have hΛm0 : MeasurableSet Λ := hS.measurableSpace_le _ hΛm
    set Esc := heavyEscSet W n j (heavyXi W j ι') with hEsc
    have hhint : Integrable (Esc.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const 1).indicator (hE ι')
    -- pointwise comparison
    have hle : ∀ ω, Λ.indicator (Esc.indicator (fun _ => (1 : ℝ))) ω ≤
        Λ.indicator ((heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ))) ω := by
      intro ω
      by_cases hωΛ : ω ∈ Λ
      · rw [Set.indicator_of_mem hωΛ, Set.indicator_of_mem hωΛ]
        by_cases hωE : ω ∈ Esc
        · rw [Set.indicator_of_mem hωE]
          have hfin : heavySi (W ω) n m ι i < ⊤ :=
            lt_of_lt_of_le hωΛ.1 (lt_top_iff_ne_top.2 (hTfin ω)).le
          have hω' : ω ∈ heavyEscSet W n j (fun ω => heavySi (W ω) n m ι i) := by
            refine ⟨?_, ?_⟩
            · exact hfin.ne
            · have h3 : EscEvent n j (W ω) (heavyXi W j ι' ω).toReal := hωE.2
              show EscEvent n j (W ω) (heavySi (W ω) n m ι i).toReal
              rw [hωΛ.2]
              exact h3
          rw [Set.indicator_of_mem (heavyEscSet_subset_gap hAd hn hjm ι i hfin hω')]
        · rw [Set.indicator_of_notMem hωE]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      · rw [Set.indicator_of_notMem hωΛ, Set.indicator_of_notMem hωΛ]
    have h1 := condExp_indicator (m := hS.measurableSpace) (μ := μ) hgint hΛm
    have h2 := condExp_indicator (m := hS.measurableSpace) (μ := μ) hhint hΛm
    have h3 : μ[Λ.indicator (Esc.indicator (fun _ => (1 : ℝ))) | hS.measurableSpace] ≤ᵐ[μ]
        μ[Λ.indicator ((heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ))) |
          hS.measurableSpace] :=
      condExp_mono (hhint.indicator hΛm0) (hgint.indicator hΛm0) (Filter.Eventually.of_forall hle)
    have h4 := condExp_stopping_time_ae_eq_restrict_eq_stopping_time (μ := μ) hS hξ
      (Esc.indicator (fun _ => (1 : ℝ)))
    have hSξ : MeasurableSet {ω | heavySi (W ω) n m ι i = heavyXi W j ι' ω} :=
      hS.measurableSpace_le _ heq
    have h4' := (ae_restrict_iff' hSξ).1 h4
    filter_upwards [h1, h2, h3, h4'] with ω e1 e2 e3 e4 hωΛ
    have hV : c < heavyEscVersion hAd μ n ι' ω := by
      by_contra hcon
      push Not at hcon
      have hfin : heavySi (W ω) n m ι i < ⊤ :=
        lt_of_lt_of_le hωΛ.1 (lt_top_iff_ne_top.2 (hTfin ω)).le
      have hpos : 0 < heavyXi W j ι' ω := by
        rw [← hωΛ.2]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        refine lt_of_lt_of_le ?_ (heavyEntSeq_succ_ge (w := W ω) (j := j) (m := m)
          (D := (heavyD n m : ℝ≥0∞)) (ι := ι) i')
        refine lt_of_lt_of_le ?_ le_add_self
        have : 0 < heavyD n m := by unfold heavyD; positivity
        exact_mod_cast this
      have hxi : heavyXi W j ι' ω < ⊤ := hωΛ.2 ▸ hfin
      have hτ : heavyTauV (W ω) j (fun ι'' => heavyEscVersion hAd μ n ι'' ω) c ≤
          heavyXi W j ι' ω := by
        unfold heavyTauV
        exact iInf₂_le (f := fun ι (_ : ι ∈ {ι : Fin d → ℤ | 0 < entranceTime (W ω)
          (heavyBlock j ι) ∧ entranceTime (W ω) (heavyBlock j ι) < ⊤ ∧
            heavyEscVersion hAd μ n ι ω ≤ c}) => entranceTime (W ω) (heavyBlock j ι)) ι'
          ⟨hpos, hxi, hcon⟩
      exact absurd (lt_of_lt_of_le (hωΛ.2 ▸ hωΛ.1) ((hTV ω).trans hτ)) (lt_irrefl _)
    have e4' := e4 hωΛ.2
    have hmemΛ : ω ∈ Λ := hωΛ
    have hl : μ[Λ.indicator ((heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ))) |
        hS.measurableSpace] ω =
        μ[(heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ)) | hS.measurableSpace] ω := by
      rw [e1, Set.indicator_of_mem hmemΛ]
    have hr : μ[Λ.indicator (Esc.indicator (fun _ => (1 : ℝ))) | hS.measurableSpace] ω =
        heavyEscVersion hAd μ n ι' ω := by
      rw [e2, Set.indicator_of_mem hmemΛ]
      exact e4'
    have e3' : μ[Λ.indicator (Esc.indicator (fun _ => (1 : ℝ))) | hS.measurableSpace] ω ≤
        μ[Λ.indicator ((heavyGapSet W n m ι i).indicator (fun _ => (1 : ℝ))) |
          hS.measurableSpace] ω := e3
    rw [hr, hl] at e3'
    exact hV.le.trans e3'
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω hlt
  have hfin : heavySi (W ω) n m ι i < ⊤ := lt_of_lt_of_le hlt (lt_top_iff_ne_top.2 (hTfin ω)).le
  obtain ⟨ι', -, hι'⟩ := heavyEntSeq_eq_entrance (D := (heavyD n m : ℝ≥0∞)) (ι := ι)
    (hAd.path ω) hjm i hfin
  exact hω ι' ⟨hlt, hι'⟩

end ElboimSly.Paper.Heavy
