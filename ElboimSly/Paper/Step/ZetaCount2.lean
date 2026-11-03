/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaHB
public import ElboimSly.Paper.Step.AvoidStopping
public import ElboimSly.Foundations.Concentration.GapCount
public import ElboimSly.Foundations.Concentration.BinomialTail
public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import Mathlib

/-!
# Step 4 of Lemma 7.1: `P(ζ_{n³+1} ≤ t_n) ≤ e^{-n³/17}`

ES22 Lemma 7.1, Step 4 (ES22 §7); counting long gaps, binomial tails (c).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- **Step 4 of ES22 Lemma 7.1**: with probability at least `1 - e^{-n³/17}`, `ζ_{n³+1} > t_n`. -/
theorem zeta_count_prob (hd5 : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₁ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → 3 ≤ n → StepRegime d n₁ β n t₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d},
        IsSRW P Y → (∀ ω, Y ω ∈ StepPath d) → ∀ (a s₀ : ℝ≥0),
          P.real {ω | zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (n ^ 3) ω ≤
            ENNReal.ofReal (indScale t₀ n)} ≤ Real.exp (-((n : ℝ) ^ 3 / 17)) := by
  obtain ⟨C, hC, H0⟩ := step_avoid_stopping hd5
  refine ⟨C, hC, fun n₁ => ?_⟩
  obtain ⟨β41, H1⟩ := H0 n₁
  have hd1 : 1 ≤ d := by omega
  have hδ : 0 < indDelta d / 30 := by
    have := indDelta_pos' (d := d) hd1
    positivity
  obtain ⟨βC, hβC⟩ : ∃ βC : ℝ, ∀ β : ℝ, βC ≤ β → C * β ^ (-(indDelta d / 30)) ≤ 1 / 4 := by
    have ht := (tendsto_rpow_neg_atTop hδ).const_mul C
    rw [mul_zero] at ht
    obtain ⟨βC, h⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)))
    exact ⟨βC, fun β hβ => (h β hβ).le⟩
  refine ⟨max β41 βC, ?_⟩
  intro β _ n t₀ hβ hn hreg Ω _ P Y hY hYp a s₀
  have hPprob := hY.isProbabilityMeasure
  have hβ41 : β41 ≤ β := (le_max_left _ _).trans hβ
  have hc : C * β ^ (-indDelta d / 30) ≤ 1 / 4 := by
    have := hβC β ((le_max_right _ _).trans hβ)
    rwa [← neg_div] at this
  have hβ1 : 1 < β := hreg.2.1
  have hF := hY.isAdmissible_natFil
  have hav : AvoidAll β n hF (C * β ^ (-indDelta d / 30)) := fun a S hS G hG hrel =>
    H1 β n t₀ hβ41 hreg hY hYp hF a hS hG hrel
  have hz1 := zetaProc_one (β := β) hF hYp a
  have hz2 := zetaProc_two (β := β) hF hYp a s₀
  set s : ℕ → Ω → ℝ≥0∞ := fun i => zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y)
    (za2 β a s₀ Y) s₀ i with hs_def
  set r : ℕ → Ω → ℝ≥0∞ := fun i => zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y)
    (za2 β a s₀ Y) s₀ (i + 1) with hr_def
  have hs : ∀ i, IsStoppingTime (stepShiftFilt hF a) (s i) := fun i =>
    isStoppingTime_zetaN hd1 hβ1 hz1 hz2 s₀ i
  have hr : ∀ i, IsStoppingTime (stepShiftFilt hF a) (r i) := fun i =>
    isStoppingTime_zetaP hd1 hβ1 hz1 hz2 s₀ (i + 1)
  have hsr : ∀ i ω, s i ω ≤ r i ω := by
    intro i ω
    by_cases h : zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i ω = ⊤
    · have : zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (i + 1) ω = ⊤ := by
        show min (stepThitStop β (zw1 β a Y) (za1 β a Y)
            (zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i) ω : WithTop ℝ≥0)
          (stepThitStop β (zw2 β a s₀ Y) (za2 β a s₀ Y)
            (zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i) ω :
              WithTop ℝ≥0) = ⊤
        simp [stepThitStop, h]
      show _ ≤ (zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (i + 1) ω)
      rw [this]; exact le_top
    · exact (zetaN_lt_zetaP hd1 hβ1 hz1 hz2 s₀ i h).le
  have hrs : ∀ i ω, r i ω ≤ s (i + 1) ω := fun i ω => zetaP_le_zetaN s₀ (i + 1) ω
  have hmono : ∀ i j, i ≤ j → ∀ ω, s i ω ≤ s j ω := by
    intro i j hij ω
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact ih.trans ((hsr j ω).trans (hrs j ω))
  -- the data of counting long gaps
  have hT : 0 < indScale t₀ n := by
    have := hreg.2.2.2.1
    unfold indScale
    exact mul_pos (by positivity) (by linarith [this.1])
  obtain ⟨Tn, hTn⟩ : ∃ Tn : ℝ≥0, Tn = (indScale t₀ n).toNNReal := ⟨_, rfl⟩
  have hTnr : (Tn : ℝ) = indScale t₀ n := by rw [hTn]; exact Real.coe_toNNReal _ hT.le
  set G : ℕ → Set Ω := fun i => {ω | s i ω ≤ (Tn : ℝ≥0∞)} with hG_def
  have hG : ∀ i < n ^ 3, MeasurableSet[(hs i).measurableSpace] (G i) := by
    intro i _
    exact (hs i).measurableSet_le_stopping_time (isStoppingTime_const _ Tn)
  have hA : ∀ i < n ^ 3, MeasurableSet[(hs (i + 1)).measurableSpace]
      (concGapEvent s r ((4 : ℝ) ^ n) i) := fun i hi =>
    measurableSet_concGapEvent_stopping hs hr (fun i _ ω => hsr i ω) (fun i _ ω => hrs i ω) hi
  have hB : ∀ i < n ^ 3, ∀ F', MeasurableSet[(hs i).measurableSpace] F' →
      (1 / 2 : ℝ) * P.real (G i ∩ F') ≤ P.real (concGapEvent s r ((4 : ℝ) ^ n) i ∩ G i ∩ F') := by
    intro i hi F' hF'
    have key := zeta_hB (β := β) hd1 hβ1 hYp hF a s₀ (n := n) (c := C * β ^ (-indDelta d / 30))
      hc hav i (H := G i ∩ F') ((hG i hi).inter hF') (fun ω hω => by
        have := hω.1
        simp only [hG_def, mem_ofPred_eq] at this
        exact ne_top_of_le_ne_top ENNReal.coe_ne_top this)
    have e : concGapEvent s r ((4 : ℝ) ^ n) i ∩ G i ∩ F' = (G i ∩ F') ∩
        {ω | zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i ω +
          ((((4 : ℝ) ^ n).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤
          zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (i + 1) ω} := by
      ext ω
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, h1⟩
      · rintro ⟨⟨h2, h3⟩, h1⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [e]
    exact key
  have hmain := concGapCount_le (μ := P) (K := n ^ 3) (s := s) (r := r)
    (fun i _ ω => hsr i ω) (fun i _ ω => hrs i ω) (L := (4 : ℝ) ^ n) (t := indScale t₀ n)
    (by positivity) hT.le (G := G) (𝒢 := fun i => (hs i).measurableSpace)
    (fun i _ => (hs i).measurableSpace_le)
    (fun i _ => (hs i).measurableSpace_mono (hs (i + 1)) (fun ω => (hsr i ω).trans (hrs i ω)))
    hG hA (p := 1 / 2) (by norm_num) (by norm_num) hB
  -- the binomial tail
  have hfloor : ⌊indScale t₀ n / (4 : ℝ) ^ n⌋ ≤ 5 := by
    have h4 : indScale t₀ n / (4 : ℝ) ^ n ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      unfold indScale
      nlinarith [hreg.2.2.2.1.2, pow_pos (by norm_num : (0 : ℝ) < 4) n]
    have : ⌊indScale t₀ n / (4 : ℝ) ^ n⌋ < 6 := Int.floor_lt.2 (by push_cast; linarith)
    omega
  have hbin := concBinomLE_le_exp_cube (n := n) (K := n ^ 3) hn (p := 1 / 2) (by norm_num)
    (by norm_num) (by push_cast; linarith) hfloor
  refine le_trans (measureReal_mono ?_) (hmain.trans hbin)
  intro ω hω
  refine ⟨hω, ?_⟩
  intro i hi
  have : s i ω ≤ s (n ^ 3) ω := hmono i (n ^ 3) hi.le ω
  have h2 : s (n ^ 3) ω ≤ ENNReal.ofReal (indScale t₀ n) := hω
  rw [← hTnr, ENNReal.ofReal_coe_nnreal] at h2
  exact this.trans h2

end ElboimSly.Paper.Step
