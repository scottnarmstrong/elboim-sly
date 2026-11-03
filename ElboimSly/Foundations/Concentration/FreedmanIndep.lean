/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.FreedmanVector

/-!
# Freedman's inequality for independent bounded summands

Independent bounded summands. The summands `X_1, …, X_k` of the written proof are
`X 0, …, X (k-1)` here (a family indexed by `Fin k`), and the partial sums are
`∑ i ∈ range j, X i` for `0 ≤ j ≤ k`. The filtration is `ℱ j = σ(X i : i < j)`.
-/

public section

namespace ElboimSly

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {d k : ℕ}

/-- The natural filtration `ℱ j = σ(X i : i < j)` of a family indexed by `Fin k`. -/
@[expose] def concIndepFiltration (X : ℕ → Ω → Fin d → ℝ) (k : ℕ)
    (hX : ∀ i : Fin k, Measurable (X i)) : Filtration ℕ m0 where
  seq j := ⨆ (i : Fin k) (_ : (i : ℕ) < j), MeasurableSpace.comap (X i) inferInstance
  mono' _ _ h := iSup_mono fun _ => iSup_mono' fun hi => ⟨lt_of_lt_of_le hi h, le_rfl⟩
  le' _ := iSup₂_le fun i _ => (hX i).comap_le

lemma concIndepFiltration_indep {X : ℕ → Ω → Fin d → ℝ} (hX : ∀ i : Fin k, Measurable (X i))
    (hind : iIndepFun (fun i : Fin k => X i) μ) (j : Fin k) :
    Indep (MeasurableSpace.comap (X j) inferInstance) (concIndepFiltration X k hX j) μ := by
  have h := indep_iSup_of_disjoint (m := fun i : Fin k => MeasurableSpace.comap (X i) inferInstance)
    (fun i => (hX i).comap_le) hind.iIndep (S := {j}) (T := {i : Fin k | (i : ℕ) < j})
    (by
      rw [Set.disjoint_left]
      intro i hi hi'
      rw [Set.mem_singleton_iff] at hi
      subst hi
      exact absurd hi' (by simp))
  simpa [concIndepFiltration] using h

lemma concIndepFiltration_condExp {X : ℕ → Ω → Fin d → ℝ} [IsFiniteMeasure μ]
    (hX : ∀ i : Fin k, Measurable (X i)) (hind : iIndepFun (fun i : Fin k => X i) μ)
    (j : Fin k) {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) :
    μ[fun ω => g (X j ω) | concIndepFiltration X k hX j] =ᵐ[μ] fun _ => ∫ ω, g (X j ω) ∂μ := by
  refine condExp_indep_eq (m₁ := MeasurableSpace.comap (X j) inferInstance) ?_
    ((concIndepFiltration X k hX).le j) ?_ (concIndepFiltration_indep hX hind j)
  · exact (hX j).comap_le
  · exact (hg.comp (comap_measurable (X j))).stronglyMeasurable

/-- **Freedman's inequality for independent bounded summands.**
Independent bounded summands. -/
theorem concFreedman_indep [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    {X : ℕ → Ω → Fin d → ℝ} {b V x : ℝ}
    (hX : ∀ i : Fin k, Measurable (X i)) (hind : iIndepFun (fun i : Fin k => X i) μ)
    (hb : 0 ≤ b) (hbd : ∀ i : Fin k, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ b)
    (hmean : ∀ i : Fin k, ∫ ω, X i ω ∂μ = 0)
    (hvar : ∀ c : Fin d, ∑ i : Fin k, ∫ ω, (X i ω c) ^ 2 ∂μ ≤ V)
    (hx : 0 ≤ x) (hV : 0 < V) :
    μ.real {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩
        (fun j => ‖∑ i ∈ Finset.range j, X i ω‖)} ≤
      2 * d * Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) := by
  set ℱ : Filtration ℕ m0 := concIndepFiltration X k hX with hℱ
  set M : ℕ → Ω → Fin d → ℝ := fun j ω => ∑ i ∈ Finset.range (min j k), X i ω with hM
  have hXint : ∀ i : Fin k, Integrable (X i) μ := fun i =>
    Integrable.of_bound (hX i).aestronglyMeasurable b (hbd i)
  have hcoordint : ∀ (c : Fin d) (i : Fin k), Integrable (fun ω => X i ω c) μ := fun c i =>
    Integrable.of_bound ((measurable_pi_apply c).comp (hX i)).aestronglyMeasurable b
      ((hbd i).mono fun ω h => (norm_le_pi_norm (X i ω) c).trans h)
  have hcoordmean : ∀ (c : Fin d) (i : Fin k), ∫ ω, X i ω c ∂μ = 0 := fun c i => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) c).integral_comp_comm
      (hXint i)
    simpa [hmean i] using this
  -- increments
  have hincr : ∀ j (hj : j < k) ω, M (j + 1) ω - M j ω = X j ω := by
    intro j hj ω
    simp only [hM]
    rw [min_eq_left (by omega), min_eq_left (by omega), Finset.sum_range_succ]
    abel
  have hincr' : ∀ j, k ≤ j → ∀ ω, M (j + 1) ω - M j ω = 0 := by
    intro j hj ω
    simp only [hM]
    rw [min_eq_right (by omega), min_eq_right (by omega)]
    simp
  have hmart : ∀ c : Fin d, Martingale (fun j ω => M j ω c) ℱ μ := by
    intro c
    refine martingale_of_condExp_sub_eq_zero_nat ?_ ?_ ?_
    · intro j
      have : (fun ω => M j ω c) = ∑ i ∈ Finset.range (min j k), fun ω => X i ω c := by
        funext ω; simp [hM, Finset.sum_apply]
      show StronglyMeasurable[ℱ j] (fun ω => M j ω c)
      rw [this]
      refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
      have hi' : i < min j k := Finset.mem_range.1 hi
      have hik : i < k := lt_of_lt_of_le hi' (min_le_right _ _)
      have hij : i < j := lt_of_lt_of_le hi' (min_le_left _ _)
      have h1 : StronglyMeasurable[MeasurableSpace.comap (X i) inferInstance]
          (fun ω => X i ω c) :=
        ((measurable_pi_apply c).comp (comap_measurable (X i))).stronglyMeasurable
      refine h1.mono ?_
      exact le_iSup₂_of_le (⟨i, hik⟩ : Fin k) hij le_rfl
    · intro j
      have : (fun ω => M j ω c) = fun ω => ∑ i ∈ Finset.range (min j k), X i ω c := by
        funext ω; simp [hM, Finset.sum_apply]
      show Integrable (fun ω => M j ω c) μ
      rw [this]
      refine integrable_finsetSum _ fun i hi => ?_
      have hik : i < k := lt_of_lt_of_le (Finset.mem_range.1 hi) (min_le_right _ _)
      exact hcoordint c ⟨i, hik⟩
    · intro j
      by_cases hj : j < k
      · have h1 := concIndepFiltration_condExp (μ := μ) hX hind ⟨j, hj⟩
          (g := fun y => y c) (measurable_pi_apply c)
        have h2 : (fun ω => M (j + 1) ω c) - (fun ω => M j ω c) = fun ω => X j ω c := by
          funext ω
          simp [← hincr j hj ω]
        rw [h2]
        filter_upwards [h1] with ω h
        rw [h]
        simpa using hcoordmean c ⟨j, hj⟩
      · have h2 : (fun ω => M (j + 1) ω c) - (fun ω => M j ω c) = 0 := by
          funext ω
          have := hincr' j (not_lt.1 hj) ω
          have := congrFun this c
          simpa using this
        rw [h2, condExp_zero]
  -- the variance bounds `v c (j+1) = E[(X j c)^2]`
  set v : Fin d → ℕ → Ω → ℝ := fun c j _ => ∫ ω, (X (j - 1) ω c) ^ 2 ∂μ with hvdef
  have hvsucc : ∀ c j ω, v c (j + 1) ω = ∫ ω', (X j ω' c) ^ 2 ∂μ := fun c j ω => by
    simp [hvdef]
  have hsq : ∀ c : Fin d, Measurable fun y : Fin d → ℝ => (y c) ^ 2 := fun c =>
    (measurable_pi_apply c).pow_const 2
  have hres := concFreedman_vector (μ := μ) (ℱ := ℱ) hd (M := M) (v := v) (b := b) (V := V)
    (x := x) (by funext ω; simp [hM]) hmart hb
    (fun j hj => (hbd ⟨j, hj⟩).mono fun ω h => by rw [hincr j hj ω]; exact h)
    (fun c j _ => by
      have : v c (j + 1) = fun _ => ∫ ω', (X j ω' c) ^ 2 ∂μ := funext (hvsucc c j)
      rw [this]; exact stronglyMeasurable_const)
    (fun c j _ ω => by rw [hvsucc c j ω]; exact integral_nonneg fun _ => sq_nonneg _)
    (fun c j hj => by
      have h1 := concIndepFiltration_condExp (μ := μ) hX hind ⟨j, hj⟩
        (g := fun y => (y c) ^ 2) (hsq c)
      have h2 : (fun ω => M (j + 1) ω c - M j ω c) ^ 2 = fun ω => (X j ω c) ^ 2 := by
        funext ω
        have := congrFun (hincr j hj ω) c
        simp only [Pi.sub_apply] at this
        simp [this]
      rw [h2]
      filter_upwards [h1] with ω h
      rw [h, hvsucc c j ω])
    hx hV
    (fun c => Filter.Eventually.of_forall fun ω => by
      have : ∑ i ∈ Finset.range k, v c (i + 1) ω = ∑ i ∈ Finset.range k, ∫ ω', (X i ω' c) ^ 2 ∂μ :=
        Finset.sum_congr rfl fun i _ => hvsucc c i ω
      rw [this]
      have := hvar c
      rwa [Fin.sum_univ_eq_sum_range (fun i => ∫ ω', (X i ω' c) ^ 2 ∂μ) k] at this)
  refine le_of_eq_of_le (congrArg μ.real ?_) hres
  ext ω
  simp only [Set.mem_ofPred_eq]
  refine Iff.of_eq (congrArg (x ≤ ·) (Finset.sup'_congr _ rfl fun j hj => ?_)).symm
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
  simp [hM, min_eq_left hjk]

end ElboimSly
