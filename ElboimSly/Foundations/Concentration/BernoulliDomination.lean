/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.BernoulliCount

/-!
# Domination of adapted Bernoulli trials by a binomial law

Domination by Bernoulli trials (a), (b). The written proof's potential
`Φ_j = ∑_s P(Γ_j ∩ {S_j = s}) F_{K-j,p}(m - s)` is written as the expectation
`E[1_{Γ_j} F_{K-j,p}(m - S_j)]`, so that the monotonicity step becomes a pointwise identity plus
the hypothesis tested against `𝒢_j`-measurable sets.
-/

public section

namespace ElboimSly

open MeasureTheory Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The potential `1_{Γ_j} F_{K-j,p}(m - S_j)`. -/
@[expose] noncomputable def concDomPotential (K : ℕ) (p : ℝ) (m : ℤ) (G A : ℕ → Set Ω) (j : ℕ)
    (ω : Ω) : ℝ :=
  (concGamma G j).indicator (fun ω => concBinomLE (K - j) p (m - concCount A j ω)) ω

section Potential

variable {K : ℕ} {p : ℝ} {m : ℤ} {G A : ℕ → Set Ω} {j : ℕ}

lemma integral_concDomPotential_zero [IsProbabilityMeasure μ] :
    ∫ ω, concDomPotential K p m G A 0 ω ∂μ = concBinomLE K p m := by
  have : concDomPotential K p m G A 0 = fun _ => concBinomLE K p m := by
    funext ω
    simp [concDomPotential, concGamma_zero, concCount_zero]
  rw [this]
  simp

lemma integral_concDomPotential_last [IsProbabilityMeasure μ]
    (hΓ : MeasurableSet (concGamma G K)) (hS : Measurable (concCount A K)) :
    ∫ ω, concDomPotential K p m G A K ω ∂μ =
      μ.real (concGamma G K ∩ {ω | (concCount A K ω : ℤ) ≤ m}) := by
  have hset : MeasurableSet {ω | (concCount A K ω : ℤ) ≤ m} :=
    hS (MeasurableSpace.measurableSet_top : MeasurableSet {s : ℕ | (s : ℤ) ≤ m})
  have : concDomPotential K p m G A K =
      (concGamma G K ∩ {ω | (concCount A K ω : ℤ) ≤ m}).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    unfold concDomPotential
    by_cases h1 : ω ∈ concGamma G K
    · by_cases h2 : (concCount A K ω : ℤ) ≤ m
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show ω ∈ concGamma G K ∩ {ω | (concCount A K ω : ℤ) ≤ m} from ⟨h1, h2⟩)]
        simp only [Nat.sub_self]
        rw [concBinomLE_of_ge]
        omega
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (fun h => h2 h.2)]
        simp only [Nat.sub_self]
        rw [concBinomLE_of_neg]
        omega
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h => h1 h.1)]
  rw [this, integral_indicator_const _ (hΓ.inter hset)]
  simp


/-- The increment `F_{n,p}(m - s) - F_{n,p}(m - s - 1)` of the lower tail. -/
@[expose] noncomputable def concDomDiff (n : ℕ) (p : ℝ) (m : ℤ) (s : ℕ) : ℝ :=
  concBinomLE n p (m - s) - concBinomLE n p (m - s - 1)

lemma concDomDiff_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℤ) (s : ℕ) :
    0 ≤ concDomDiff n p m s := by
  unfold concDomDiff
  have := concBinomLE_mono (K := n) hp0 hp1 (show m - s - 1 ≤ m - s by omega)
  linarith

/-- Pointwise decomposition for one step of the potential. -/
lemma concDomPotential_decomp (hj : j < K) (ω : Ω) :
    concDomPotential K p m G A j ω =
      concDomPotential K p m G A (j + 1) ω +
      (concGamma G j ∩ (G j)ᶜ).indicator (fun ω => concBinomLE (K - (j + 1)) p (m - concCount A j ω) -
        p * concDomDiff (K - (j + 1)) p m (concCount A j ω)) ω +
      ((concGamma G j ∩ G j ∩ A j).indicator (fun ω => concDomDiff (K - (j + 1)) p m (concCount A j ω)) ω -
        p * (concGamma G j ∩ G j).indicator (fun ω => concDomDiff (K - (j + 1)) p m (concCount A j ω)) ω) := by
  have hKj : K - j = (K - (j + 1)) + 1 := by omega
  unfold concDomPotential concDomDiff
  rw [hKj]
  simp only [concBinomLE_succ]
  by_cases h1 : ω ∈ concGamma G j
  · by_cases h2 : ω ∈ G j
    · have e : ω ∈ concGamma G (j + 1) := by rw [concGamma_succ]; exact ⟨h1, h2⟩
      by_cases h3 : ω ∈ A j
      · simp [Set.indicator, h1, h2, h3, e, concCount_succ, sub_add_eq_sub_sub]
        ring
      · simp [Set.indicator, h1, h2, h3, e, concCount_succ]
        ring
    · have e : ω ∉ concGamma G (j + 1) := by rw [concGamma_succ]; exact fun h => h2 h.2
      simp [Set.indicator, h1, h2, e]
      ring
  · have e : ω ∉ concGamma G (j + 1) := fun h => h1 (fun i hi => h i (by omega))
    simp [Set.indicator, h1, e]


/-- The σ-algebras increase along the chain up to `K`. -/
lemma concBernoulli_chain {𝒢 : ℕ → MeasurableSpace Ω} {K : ℕ}
    (h𝒢mono : ∀ i < K, 𝒢 i ≤ 𝒢 (i + 1)) : ∀ i j, i ≤ j → j ≤ K → 𝒢 i ≤ 𝒢 j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih => intro hj; exact (ih (by omega)).trans (h𝒢mono j (by omega))

/-- One step of the potential argument. -/
lemma integral_concDomPotential_succ_le [IsProbabilityMeasure μ] {𝒢 : ℕ → MeasurableSpace Ω}
    (h𝒢le : ∀ i ≤ K, 𝒢 i ≤ m0) (h𝒢mono : ∀ i < K, 𝒢 i ≤ 𝒢 (i + 1))
    (hG : ∀ i < K, MeasurableSet[𝒢 i] (G i)) (hA : ∀ i < K, MeasurableSet[𝒢 (i + 1)] (A i))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hB : ∀ i < K, ∀ F, MeasurableSet[𝒢 i] F → p * μ.real (G i ∩ F) ≤ μ.real (A i ∩ G i ∩ F))
    (hj : j < K) :
    ∫ ω, concDomPotential K p m G A (j + 1) ω ∂μ ≤ ∫ ω, concDomPotential K p m G A j ω ∂μ := by
  have hchain := concBernoulli_chain h𝒢mono
  -- measurability
  have hGm : ∀ i < K, MeasurableSet (G i) := fun i hi => h𝒢le i hi.le _ (hG i hi)
  have hAm : ∀ i < K, MeasurableSet (A i) := fun i hi => h𝒢le (i + 1) hi _ (hA i hi)
  have hΓ : MeasurableSet (concGamma G j) :=
    measurableSet_concGamma fun i hi => hGm i (by omega)
  have hΓ' : MeasurableSet (concGamma G (j + 1)) :=
    measurableSet_concGamma fun i hi => hGm i (by omega)
  have hS : Measurable (concCount A j) := measurable_concCount fun i hi => hAm i (by omega)
  have hS' : Measurable (concCount A (j + 1)) :=
    measurable_concCount fun i hi => hAm i (by omega)
  have hGj := hGm j hj
  have hAj := hAm j hj
  set n := K - (j + 1) with hn
  -- the three auxiliary functions of `S_j`
  set gU : ℕ → ℝ := fun s => concBinomLE n p (m - s) - p * concDomDiff n p m s with hgU
  set gD : ℕ → ℝ := fun s => concDomDiff n p m s with hgD
  have hI1 := integral_indicator_comp_nat (μ := μ) (hΓ.inter hGj.compl) hS
    (fun ω => concCount_le A j ω) gU
  have hI2 := integral_indicator_comp_nat (μ := μ) ((hΓ.inter hGj).inter hAj) hS
    (fun ω => concCount_le A j ω) gD
  have hI3 := integral_indicator_comp_nat (μ := μ) (hΓ.inter hGj) hS
    (fun ω => concCount_le A j ω) gD
  have hP0 := integral_indicator_comp_nat (μ := μ) hΓ hS (fun ω => concCount_le A j ω)
    (fun s : ℕ => concBinomLE (K - j) p (m - s))
  have hP1 := integral_indicator_comp_nat (μ := μ) hΓ' hS' (fun ω => concCount_le A (j + 1) ω)
    (fun s : ℕ => concBinomLE (K - (j + 1)) p (m - s))
  -- decomposition of the integrals
  have hdecomp : (fun ω => concDomPotential K p m G A j ω) = fun ω =>
      concDomPotential K p m G A (j + 1) ω +
      (concGamma G j ∩ (G j)ᶜ).indicator (fun ω => gU (concCount A j ω)) ω +
      ((concGamma G j ∩ G j ∩ A j).indicator (fun ω => gD (concCount A j ω)) ω -
        p * (concGamma G j ∩ G j).indicator (fun ω => gD (concCount A j ω)) ω) := by
    funext ω
    exact concDomPotential_decomp hj ω
  have hint_eq : ∫ ω, concDomPotential K p m G A j ω ∂μ =
      ∫ ω, concDomPotential K p m G A (j + 1) ω ∂μ +
      ∫ ω, (concGamma G j ∩ (G j)ᶜ).indicator (fun ω => gU (concCount A j ω)) ω ∂μ +
      (∫ ω, (concGamma G j ∩ G j ∩ A j).indicator (fun ω => gD (concCount A j ω)) ω ∂μ -
        p * ∫ ω, (concGamma G j ∩ G j).indicator (fun ω => gD (concCount A j ω)) ω ∂μ) := by
    rw [hdecomp]
    have i0 : Integrable (fun ω => concDomPotential K p m G A (j + 1) ω) μ := hP1.1
    have i1 : Integrable (fun ω => (concGamma G j ∩ (G j)ᶜ).indicator
        (fun ω => gU (concCount A j ω)) ω) μ := hI1.1
    have i2 : Integrable (fun ω => (concGamma G j ∩ G j ∩ A j).indicator
        (fun ω => gD (concCount A j ω)) ω) μ := hI2.1
    have i3 : Integrable (fun ω => p * (concGamma G j ∩ G j).indicator
        (fun ω => gD (concCount A j ω)) ω) μ := hI3.1.const_mul p
    have i01 : Integrable (fun ω => concDomPotential K p m G A (j + 1) ω +
        (concGamma G j ∩ (G j)ᶜ).indicator (fun ω => gU (concCount A j ω)) ω) μ := i0.add i1
    have i23 : Integrable (fun ω => (concGamma G j ∩ G j ∩ A j).indicator
        (fun ω => gD (concCount A j ω)) ω - p * (concGamma G j ∩ G j).indicator
        (fun ω => gD (concCount A j ω)) ω) μ := i2.sub i3
    rw [integral_add i01 i23, integral_add i0 i1, integral_sub i2 i3, integral_const_mul]
  -- the first remainder is nonnegative
  have hU : 0 ≤ ∫ ω, (concGamma G j ∩ (G j)ᶜ).indicator (fun ω => gU (concCount A j ω)) ω ∂μ := by
    refine integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => ?_) ω
    have h1 := concBinomLE_nonneg (K := n) hp0 hp1 (m - concCount A j ω)
    have h2 := concBinomLE_nonneg (K := n) hp0 hp1 (m - concCount A j ω - 1)
    simp only [hgU, concDomDiff]
    nlinarith
  -- the second remainder is nonnegative, by the hypothesis on the trials
  have hV : 0 ≤ ∫ ω, (concGamma G j ∩ G j ∩ A j).indicator (fun ω => gD (concCount A j ω)) ω ∂μ -
      p * ∫ ω, (concGamma G j ∩ G j).indicator (fun ω => gD (concCount A j ω)) ω ∂μ := by
    rw [hI2.2, hI3.2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun s _ => ?_
    have hF : MeasurableSet[𝒢 j] (concGamma G j ∩ {ω | concCount A j ω = s}) := by
      refine (measurableSet_concGamma (m := 𝒢 j) fun i hi => ?_).inter ?_
      · exact hchain i j (by omega) hj.le _ (hG i (by omega))
      · exact (measurable_concCount (m := 𝒢 j) fun i hi =>
          hchain (i + 1) j (by omega) hj.le _ (hA i (by omega))) (measurableSet_singleton s)
    have h := hB j hj _ hF
    have e1 : (concGamma G j ∩ G j ∩ A j) ∩ {ω | concCount A j ω = s} =
        A j ∩ G j ∩ (concGamma G j ∩ {ω | concCount A j ω = s}) := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
    have e2 : (concGamma G j ∩ G j) ∩ {ω | concCount A j ω = s} =
        G j ∩ (concGamma G j ∩ {ω | concCount A j ω = s}) := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
    rw [e1, e2]
    have hd := concDomDiff_nonneg (n := n) hp0 hp1 m s
    simp only [hgD]
    nlinarith
  linarith

/-- Domination by Bernoulli trials (a), with arbitrary active events. -/
theorem concBernoulli_lower [IsProbabilityMeasure μ] {𝒢 : ℕ → MeasurableSpace Ω}
    (h𝒢le : ∀ i ≤ K, 𝒢 i ≤ m0) (h𝒢mono : ∀ i < K, 𝒢 i ≤ 𝒢 (i + 1))
    (hG : ∀ i < K, MeasurableSet[𝒢 i] (G i)) (hA : ∀ i < K, MeasurableSet[𝒢 (i + 1)] (A i))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hB : ∀ i < K, ∀ F, MeasurableSet[𝒢 i] F → p * μ.real (G i ∩ F) ≤ μ.real (A i ∩ G i ∩ F))
    (m : ℤ) :
    μ.real (concGamma G K ∩ {ω | (concCount A K ω : ℤ) ≤ m}) ≤ concBinomLE K p m := by
  have hGm : ∀ i < K, MeasurableSet (G i) := fun i hi => h𝒢le i hi.le _ (hG i hi)
  have hAm : ∀ i < K, MeasurableSet (A i) := fun i hi => h𝒢le (i + 1) hi _ (hA i hi)
  have hΓ : MeasurableSet (concGamma G K) := measurableSet_concGamma hGm
  have hS : Measurable (concCount A K) := measurable_concCount hAm
  rw [← integral_concDomPotential_last (K := K) (p := p) hΓ hS, ← integral_concDomPotential_zero
    (μ := μ) (K := K) (p := p) (m := m) (G := G) (A := A)]
  have : ∀ j ≤ K, ∫ ω, concDomPotential K p m G A j ω ∂μ ≤
      ∫ ω, concDomPotential K p m G A 0 ω ∂μ := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
      intro hj
      exact (integral_concDomPotential_succ_le h𝒢le h𝒢mono hG hA hp0 hp1 hB (by omega)).trans
        (ih (by omega))
  exact this K le_rfl

end Potential

end ElboimSly
