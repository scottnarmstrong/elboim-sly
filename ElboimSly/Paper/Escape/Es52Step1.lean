/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Aux
public import ElboimSly.Paper.Escape.Es52Loc
public import ElboimSly.Paper.Escape.Es52Step1Aux
public import ElboimSly.Paper.Escape.Es52Meas
public import ElboimSly.Paper.Escape.Es55Stmt
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 1 (the half `W(ξ_B) ∈ B⁻`), conditional on `Es55Concl`

ES22 Proposition 5.2 proof, Step 1.  For a fixed `β'`,
`P(𝒦(β') ∩ {π_B ≤ n^{-γ}}) ≤ 2 (1 - c_{53})^{I}`, where `π_B` is `escPiG`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

section main

variable {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} {𝒢₀ : MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- The core estimate of Step 1, with all inputs as hypotheses. -/
theorem es52_step1_core (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (hn : 2000 ≤ n)
    (hlb : Real.log β ≤ (n : ℝ) ^ 40) (u : Fin (k + 2) → ℤ) (hadm : EscAdmissible (escJ n) u)
    (β' : ℕ)
    (H55 : ∀ i, 1 ≤ i → i ≤ escIstar n (escJ n) →
      ∀ᵐ ω ∂Pr, N ω ∈ escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i →
        2 * ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2))) ≤
          resPhi (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) Pr N
            (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
              (escIstar n (escJ n) + 1))
            (escConSet β n u i) ω)
    (h54 : 1 - (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n) ≤
          Pr {ω | ∃ ℓ, ℓ < escIstar n (escJ n) ∧
            (escEntry n u β' (hlog_of_params hS.params) (cycNgood N ω) ℓ).len =
              (4 : ℝ≥0∞) ^ n}) :
    Pr {ω | N ω ∈ escKSet β (indScale t₀ n) n β' u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} ≤
      2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n) := by
  have hN := hS.space.ppp
  have hN' := hS.space.ppp'
  have h𝒢 := hS.space.le
  have hI1 := hS.space.indep
  have hI2 := hS.space.indep'
  have := hN.isProbabilityMeasure
  have htn := indScale_pos' hS
  set hlog := hlog_of_params hS.params with hhlog
  set I := escIstar n (escJ n) with hI
  set tn := indScale t₀ n with htn_def
  set b : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2))) with hb
  set c : ℝ≥0∞ := ENNReal.ofReal (cline (k + 2) / 2) with hc
  have hb0 : b ≠ 0 := by
    rw [hb, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
  have hbt : b ≠ ⊤ := ENNReal.ofReal_ne_top
  set Kset := escKSet β tn n β' u with hKset
  set AU := escAUnion n u β' hlog with hAU
  set Tg := escTg N tn n u with hTg
  have hTgs := isStoppingTime_escTg hS tn u
  have hTgf : Pr {ω | Tg ω ≠ ⊤} = 1 := by
    have : {ω | Tg ω ≠ ⊤} = univ := by
      ext ω; simp [hTg, escTg_ne_top]
    rw [this]; exact measure_univ
  have hKm : MeasurableSet Kset := measurableSet_escKSet n tn u β' hlog hadm htn
  have hAUm : MeasurableSet AU := measurableSet_escAUnion n u β' hlog
  have hgood : ∀ᵐ ω ∂Pr, CycGood (N ω) := CycSchemeEnv.ae_cycGood' hN
  -- the per-`i` tower steps
  have F1 : ∀ᵐ ω ∂Pr, ∀ i, 1 ≤ i → i ≤ I →
      2 * b * resPhi (plan5 n β tn u β' i hlog) Pr N (lamT (plan5 n β tn u β' i hlog) N 1)
        (Kset ∩ escASet n u β' hlog i) ω ≤
      resPhi (plan5 n β tn u β' i hlog) Pr N (lamT (plan5 n β tn u β' i hlog) N 1)
        (Kset ∩ escASet n u β' hlog i ∩ escConSet β n u i) ω := by
    rw [ae_all_iff]
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ I
    · filter_upwards [step1_tower hS u hadm β' i hi.1 hi.2 (2 * b) (H55 i hi.1 hi.2)] with ω h
        _ _
      exact h
    · exact Filter.Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hi
  -- `Φ_𝒦 = 1` on `𝒦`
  have F3 : ∀ᵐ ω ∂Pr, N ω ∈ Kset → 1 ≤ resPhi (plan5 n β tn u β' 1 hlog) Pr N
      (lamT (plan5 n β tn u β' 1 hlog) N 1) Kset ω := by
    have hT1 := isStoppingTime_lamT1 hS n u β' 1 hlog
    have hf1 := ae_lamT1_ne_top hS n u β' 1 hlog
    have hH := measurableSet_K_S1 hS u hadm htn β' 1 hlog hT1
    have h := resPhi_le_inter (plan5 n β tn u β' 1 hlog) 𝒢₀ hN hN' hI1 hI2
      (plan5_K_pos n tn u β' 1 hlog) h𝒢 hT1 hf1 hKm MeasurableSet.univ (E := univ) hH
    filter_upwards [h] with ω hω hm
    have h1 := hω hm
    have : resPhi (plan5 n β tn u β' 1 hlog) Pr N (lamT (plan5 n β tn u β' 1 hlog) N 1) univ ω
        = 1 := by
      unfold resPhi resampleProb
      simp only [Set.mem_univ, ofPred_true]
      exact measure_univ
    rw [this, Set.inter_univ] at h1
    exact h1
  -- Markov
  have hmk : Pr {ω | 2⁻¹ ≤ resPhi (regPlan (k + 2) β) Pr N Tg ((AU)ᶜ) ω} ≤ 2 * Pr (N ⁻¹' AUᶜ) := by
    obtain ⟨hmeas, hint⟩ := es4_resample_b (regPlan (k + 2) β) 𝒢₀ hN hN' hI1 hI2
      (by simp [regPlan, closingPlan]) h𝒢 hTgs hTgf hAUm.compl
    have hm' : AEMeasurable (resPhi (regPlan (k + 2) β) Pr N Tg ((AU)ᶜ)) Pr :=
      (hmeas.mono hTgs.measurableSpace_le le_rfl).aemeasurable
    have h := meas_ge_le_lintegral_div hm' (ε := 2⁻¹) (by simp) (by simp)
    have h2 : ∫⁻ ω, resPhi (regPlan (k + 2) β) Pr N Tg ((AU)ᶜ) ω ∂Pr = Pr (N ⁻¹' AUᶜ) := by
      have := hint (MeasurableSet.univ : MeasurableSet[hTgs.measurableSpace] univ)
      simp only [Set.univ_inter, Measure.restrict_univ] at this
      exact this.symm
    rw [h2, ENNReal.div_eq_inv_mul, inv_inv] at h
    exact h
  have key : ∀ᵐ ω ∂Pr, N ω ∈ Kset ∧ escPiG Pr N n tn u ω ≤ b →
      2⁻¹ ≤ resPhi (regPlan (k + 2) β) Pr N Tg ((AU)ᶜ) ω := by
    filter_upwards [hgood, F1, F3] with ω hω h1 h3 ⟨hK, hπ⟩
    have hTeq : escT N tn (escBlock (escJ n) u) ω = Tg ω := by
      show _ = ((escT0 β tn n u (cycNgood N ω) : ℝ≥0) : WithTop ℝ≥0)
      rw [cycNgood_of_good hω]; rfl
    have hπeq : escPiG Pr N n tn u ω =
        resampleInt (regPlan (k + 2) β) Pr N Tg (fun p => escYg n tn u p.2) ω := by
      simp only [escPiG, resampleInt, cycRecStop, cycRegionStop, SRW.stopReal, hTeq]
    set M := (cycRecStop (regPlan (k + 2) β) (cycNgood N) Tg ω).rm β with hM
    set Rg := cycRegionStop (regPlan (k + 2) β) (cycNgood N) Tg ω with hRg
    have hRm : MeasurableSet Rg :=
      measurableSet_cycRegionStop (regPlan (k + 2) β) (N := cycNgood N) Tg ω
    set X : ℕ → Set (Measure (CycS ℕ (k + 2) β)) :=
      fun i => Kset ∩ escASet n u β' hlog i ∩ escConSet β n u i with hX
    have hXm : ∀ i ∈ Finset.Icc 1 I, MeasurableSet (X i) := fun i hi =>
      ((hKm.inter (measurableSet_escASet n u β' hlog (Finset.mem_Icc.1 hi).1
        (Finset.mem_Icc.1 hi).2)).inter (measurableSet_escConSet n u i))
    have hdisj : ((Finset.Icc 1 I : Finset ℕ) : Set ℕ).PairwiseDisjoint X := by
      intro i _ j _ hij
      exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
        (escConSet_disjoint hn u hij)
    have hf : ∀ i ∈ Finset.Icc 1 I, ∀ μ ∈ X i, 1 ≤ escYg n tn u μ := by
      intro i hi μ hμ
      have hi' := Finset.mem_Icc.1 hi
      rw [escYg_eq_one (escX_subset_Y hlog hn hlb hi'.1 hi'.2 hμ.1.1 hμ.1.2 hμ.2)]
    have hsum := resampleProb_sum_le_lintegral (Pr.map N) M hRm (Finset.Icc 1 I) X hXm hdisj
      (escYg n tn u) hf
    have hπ' : ∑ i ∈ Finset.Icc 1 I, resampleProb (Pr.map N) M Rg (X i) ≤ b := by
      refine hsum.trans (le_trans (le_of_eq ?_) hπ)
      rw [hπeq]; rfl
    have hloc : ∀ i, ∀ Y, resPhi (regPlan (k + 2) β) Pr N Tg Y ω =
        resPhi (plan5 n β tn u β' i hlog) Pr N (lamT (plan5 n β tn u β' i hlog) N 1) Y ω :=
      fun i Y => resPhi_reg_eq_plan5 n tn u β' i hlog hadm htn hω hK Y
    have hterm : ∀ i ∈ Finset.Icc 1 I, 2 * b *
        resampleProb (Pr.map N) M Rg (Kset ∩ escASet n u β' hlog i) ≤
        resampleProb (Pr.map N) M Rg (X i) := by
      intro i hi
      have hi' := Finset.mem_Icc.1 hi
      have e1 := hloc i (Kset ∩ escASet n u β' hlog i)
      have e2 := hloc i (X i)
      have h := h1 i hi'.1 hi'.2
      exact (le_of_eq (by rw [show resampleProb (Pr.map N) M Rg (Kset ∩ escASet n u β' hlog i) =
        resPhi (regPlan (k + 2) β) Pr N Tg (Kset ∩ escASet n u β' hlog i) ω from rfl, e1])).trans
        (h.trans (le_of_eq (by
          rw [show resampleProb (Pr.map N) M Rg (X i) =
            resPhi (regPlan (k + 2) β) Pr N Tg (X i) ω from rfl, e2])))
    have hKA : resampleProb (Pr.map N) M Rg (Kset ∩ AU) ≤
        ∑ i ∈ Finset.Icc 1 I, resampleProb (Pr.map N) M Rg (Kset ∩ escASet n u β' hlog i) := by
      refine le_trans (resampleProb_mono (Pr.map N) M Rg ?_)
        (resampleProb_biUnion_le (Pr.map N) M Rg (Finset.Icc 1 I)
          (fun i => Kset ∩ escASet n u β' hlog i))
      intro ν hν
      obtain ⟨hνK, hνg, ℓ, hℓ, hlen⟩ := hν
      simp only [mem_iUnion, Finset.mem_Icc, exists_prop]
      refine ⟨ℓ + 1, ⟨by omega, by omega⟩, hνK, hνg, ?_⟩
      simpa using hlen
    have hx : 2 * b * resampleProb (Pr.map N) M Rg (Kset ∩ AU) ≤ b := by
      calc 2 * b * resampleProb (Pr.map N) M Rg (Kset ∩ AU)
          ≤ 2 * b * ∑ i ∈ Finset.Icc 1 I,
              resampleProb (Pr.map N) M Rg (Kset ∩ escASet n u β' hlog i) := by gcongr
        _ = ∑ i ∈ Finset.Icc 1 I, 2 * b *
              resampleProb (Pr.map N) M Rg (Kset ∩ escASet n u β' hlog i) := Finset.mul_sum _ _ _
        _ ≤ ∑ i ∈ Finset.Icc 1 I, resampleProb (Pr.map N) M Rg (X i) :=
            Finset.sum_le_sum hterm
        _ ≤ b := hπ'
    have hx2 : resampleProb (Pr.map N) M Rg (Kset ∩ AU) ≤ 2⁻¹ := by
      have : b * (2 * resampleProb (Pr.map N) M Rg (Kset ∩ AU)) ≤ b * 1 := by
        rw [mul_one]; calc _ = 2 * b * resampleProb (Pr.map N) M Rg (Kset ∩ AU) := by ring
          _ ≤ b := hx
      have h2 := (ENNReal.mul_le_mul_iff_right hb0 hbt).1 this
      rw [ENNReal.le_inv_iff_mul_le]
      calc _ = resampleProb (Pr.map N) M Rg (Kset ∩ AU) * 2 := rfl
        _ = 2 * resampleProb (Pr.map N) M Rg (Kset ∩ AU) := mul_comm _ _
        _ ≤ 1 := h2
    have hz : 1 ≤ resampleProb (Pr.map N) M Rg Kset := by
      have := h3 hK
      rw [← hloc 1 Kset] at this
      exact this
    have hzxy : resampleProb (Pr.map N) M Rg Kset ≤ resampleProb (Pr.map N) M Rg (Kset ∩ AU) +
        resampleProb (Pr.map N) M Rg (AU)ᶜ := by
      refine le_trans (resampleProb_mono (Pr.map N) M Rg ?_) (resampleProb_union_le _ _ _ _ _)
      intro ν hν
      by_cases h : ν ∈ AU
      · exact Or.inl ⟨hν, h⟩
      · exact Or.inr h
    have h1' : 1 ≤ resampleProb (Pr.map N) M Rg (Kset ∩ AU) + resampleProb (Pr.map N) M Rg (AU)ᶜ :=
      hz.trans hzxy
    have : 1 - resampleProb (Pr.map N) M Rg (Kset ∩ AU) ≤ resampleProb (Pr.map N) M Rg (AU)ᶜ :=
      tsub_le_iff_left.2 h1'
    refine le_trans ?_ this
    calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
      _ ≤ _ := tsub_le_tsub_left hx2 1
  -- the event is contained in the Markov event
  have hsub : {ω | N ω ∈ Kset ∧ escPiG Pr N n tn u ω ≤ b} ≤ᵐ[Pr]
      {ω | 2⁻¹ ≤ resPhi (regPlan (k + 2) β) Pr N Tg ((AU)ᶜ) ω} := by
    filter_upwards [key] with ω hω hmem
    exact hω hmem
  have hA1 : Pr (N ⁻¹' AUᶜ) ≤ (1 - c) ^ I := by
    set S := {ω | ∃ ℓ, ℓ < I ∧ (escEntry n u β' hlog (cycNgood N ω) ℓ).len = (4 : ℝ≥0∞) ^ n}
      with hSdef
    have hae : N ⁻¹' AU =ᵐ[Pr] S := by
      filter_upwards [hgood] with ω hω
      apply propext
      constructor
      · rintro ⟨-, ℓ, hℓ, hlen⟩
        exact ⟨ℓ, hℓ, by rw [cycNgood_of_good hω]; exact hlen⟩
      · rintro ⟨ℓ, hℓ, hlen⟩
        exact ⟨hω, ℓ, hℓ, by rw [cycNgood_of_good hω] at hlen; exact hlen⟩
    have hP1 : Pr (N ⁻¹' AU) = Pr S := measure_congr hae
    have hcompl : Pr (N ⁻¹' AUᶜ) = 1 - Pr (N ⁻¹' AU) := by
      rw [Set.preimage_compl]
      exact prob_compl_eq_one_sub (hN.measurable hAUm)
    rw [hcompl, hP1]
    have hq : (1 - c) ^ I ≤ 1 := pow_le_one₀ zero_le tsub_le_self
    have : 1 ≤ Pr S + (1 - c) ^ I := by
      calc (1 : ℝ≥0∞) = (1 - (1 - c) ^ I) + (1 - c) ^ I := (tsub_add_cancel_of_le hq).symm
        _ ≤ Pr S + (1 - c) ^ I := by gcongr
    exact tsub_le_iff_left.2 this
  calc Pr {ω | N ω ∈ Kset ∧ escPiG Pr N n tn u ω ≤ b}
      ≤ Pr {ω | 2⁻¹ ≤ resPhi (regPlan (k + 2) β) Pr N Tg ((AU)ᶜ) ω} := measure_mono_ae hsub
    _ ≤ 2 * Pr (N ⁻¹' AUᶜ) := hmk
    _ ≤ 2 * (1 - c) ^ I := by gcongr

end main

end ElboimSly.Paper.Escape
