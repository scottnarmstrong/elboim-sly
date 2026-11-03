/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.FreedmanStep

/-!
# The stopped exponential supermartingale

Freedman's inequality, maximal form, Steps 1 and 2. We build `Z_j = exp(λ M_j - ψ Q_j)` and the process
`Y_n = 1 + ∑_{i<n} 1_{E_i} (Z_{i+1} - Z_i)`, where `E_i` is the event of no exceedance of the level
`x` at times `1, …, i`. Then `Y_n = Z_{min(τ, n)}` for the first exceedance time `τ`, and
`E[Y_n] ≤ 1`.
-/

public section

namespace ElboimSly

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The standing hypotheses (F1), (F2) of Freedman's inequality, for the indices `j < k`. -/
structure ConcFreedmanSetting (μ : Measure Ω) (ℱ : Filtration ℕ m0) (M v : ℕ → Ω → ℝ) (b : ℝ)
    (k : ℕ) : Prop where
  zero : M 0 = 0
  martingale : Martingale M ℱ μ
  bound : ∀ j < k, ∀ᵐ ω ∂μ, |M (j + 1) ω - M j ω| ≤ b
  v_meas : ∀ j < k, StronglyMeasurable[ℱ j] (v (j + 1))
  v_nonneg : ∀ j < k, ∀ ω, 0 ≤ v (j + 1) ω
  var_le : ∀ j < k, μ[(M (j + 1) - M j) ^ 2 | ℱ j] ≤ᵐ[μ] v (j + 1)

/-- The predictable quadratic variation `Q_j = ∑_{i<j} v_{i+1}`. -/
@[expose] def concQ (v : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range j, v (i + 1) ω

/-- The exponential process `Z_j = exp(λ M_j - ψ Q_j)`. -/
@[expose] noncomputable def concZ (M v : ℕ → Ω → ℝ) (l ψ : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  Real.exp (l * M j ω - ψ * concQ v j ω)

/-- The event of no exceedance of the level `x` at the times `1, …, j`. -/
@[expose] def concNoExc (M : ℕ → Ω → ℝ) (x : ℝ) (j : ℕ) : Set Ω :=
  {ω | ∀ i, 1 ≤ i → i ≤ j → M i ω < x}

/-- The stopped process `Y_n = Z_{min(τ, n)}`, written as a sum of increments. -/
@[expose] noncomputable def concY (M v : ℕ → Ω → ℝ) (l ψ x : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  1 + ∑ i ∈ Finset.range n, (concNoExc M x i).indicator
    (fun ω => concZ M v l ψ (i + 1) ω - concZ M v l ψ i ω) ω

section Pointwise

variable {M v : ℕ → Ω → ℝ} {l ψ x : ℝ}

lemma concNoExc_anti {j j' : ℕ} (h : j ≤ j') : concNoExc M x j' ⊆ concNoExc M x j :=
  fun _ hω i h1 h2 => hω i h1 (h2.trans h)

lemma concZ_succ (j : ℕ) (ω : Ω) :
    concZ M v l ψ (j + 1) ω =
      concZ M v l ψ j ω * Real.exp (l * (M (j + 1) ω - M j ω) - ψ * v (j + 1) ω) := by
  unfold concZ concQ
  rw [Finset.sum_range_succ, ← Real.exp_add]
  congr 1
  ring

lemma concZ_pos (j : ℕ) (ω : Ω) : 0 < concZ M v l ψ j ω := Real.exp_pos _

lemma concY_succ (n : ℕ) (ω : Ω) :
    concY M v l ψ x (n + 1) ω = concY M v l ψ x n ω + (concNoExc M x n).indicator
      (fun ω => concZ M v l ψ (n + 1) ω - concZ M v l ψ n ω) ω := by
  unfold concY
  rw [Finset.sum_range_succ]
  ring

lemma concY_succ_of_not_mem {n : ℕ} {ω : Ω} (h : ω ∉ concNoExc M x n) :
    concY M v l ψ x (n + 1) ω = concY M v l ψ x n ω := by
  rw [concY_succ, Set.indicator_of_notMem h, add_zero]

lemma concY_eq_concZ (hM0 : M 0 = 0) : ∀ (n : ℕ) {ω : Ω}, ω ∈ concNoExc M x n →
    concY M v l ψ x n ω = concZ M v l ψ n ω := by
  intro n
  induction n with
  | zero =>
    intro ω _
    simp [concY, concZ, concQ, hM0]
  | succ n ih =>
    intro ω hω
    have hn : ω ∈ concNoExc M x n := concNoExc_anti (Nat.le_succ n) hω
    rw [concY_succ, ih hn, Set.indicator_of_mem hn]
    ring

lemma concY_nonneg (hM0 : M 0 = 0) (n : ℕ) (ω : Ω) : 0 ≤ concY M v l ψ x n ω := by
  induction n with
  | zero => simp [concY]
  | succ n ih =>
    by_cases hn : ω ∈ concNoExc M x n
    · rw [concY_succ, concY_eq_concZ hM0 n hn, Set.indicator_of_mem hn]
      have := concZ_pos (M := M) (v := v) (l := l) (ψ := ψ) (n + 1) ω
      linarith
    · rw [concY_succ_of_not_mem hn]; exact ih

/-- On an exceedance with small quadratic variation, `Y_n` is large. -/
lemma concY_ge_of_exceed (hM0 : M 0 = 0) {k : ℕ} (hψ : 0 ≤ ψ) (V : ℝ)
    (hv0 : ∀ j < k, ∀ ω, 0 ≤ v (j + 1) ω) (hl : 0 ≤ l) :
    ∀ n ≤ k, ∀ ω, (∃ i, 1 ≤ i ∧ i ≤ n ∧ x ≤ M i ω ∧ concQ v i ω ≤ V) →
      Real.exp (l * x - ψ * V) ≤ concY M v l ψ x n ω := by
  have hQmono : ∀ i i' : ℕ, i ≤ i' → i' ≤ k → ∀ ω, concQ v i ω ≤ concQ v i' ω := by
    intro i i' hii' hi'k ω
    unfold concQ
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hii') ?_
    intro a ha _
    exact hv0 a (by simp at ha; omega) ω
  intro n
  induction n with
  | zero => intro _ ω ⟨i, h1, h2, _⟩; omega
  | succ n ih =>
    intro hn ω ⟨i, h1, h2, h3, h4⟩
    by_cases hN : ω ∈ concNoExc M x n
    · have hi : i = n + 1 := by
        by_contra hne
        have := hN i h1 (by omega)
        linarith
      subst hi
      rw [concY_succ, concY_eq_concZ hM0 n hN, Set.indicator_of_mem hN]
      show Real.exp (l * x - ψ * V) ≤ concZ M v l ψ n ω + (concZ M v l ψ (n + 1) ω -
        concZ M v l ψ n ω)
      rw [add_sub_cancel]
      unfold concZ
      apply Real.exp_le_exp.2
      nlinarith
    · rw [concY_succ_of_not_mem hN]
      -- find a witness at time at most `n`
      have hex : ∃ i0, 1 ≤ i0 ∧ i0 ≤ n ∧ x ≤ M i0 ω := by
        by_contra hcon
        apply hN
        intro i' hi'1 hi'2
        by_contra hlt
        exact hcon ⟨i', hi'1, hi'2, not_lt.1 hlt⟩
      obtain ⟨i0, a1, a2, a3⟩ := hex
      by_cases hle : i ≤ n
      · exact ih (by omega) ω ⟨i, h1, hle, h3, h4⟩
      · have hi : i = n + 1 := by omega
        subst hi
        exact ih (by omega) ω ⟨i0, a1, a2, a3,
          (hQmono i0 (n + 1) (by omega) hn ω).trans h4⟩

end Pointwise

section Setting

variable {ℱ : Filtration ℕ m0} {M v : ℕ → Ω → ℝ} {b : ℝ} {k : ℕ}

lemma ConcFreedmanSetting.M_meas (S : ConcFreedmanSetting μ ℱ M v b k) (j : ℕ) :
    StronglyMeasurable[m0] (M j) :=
  ((S.martingale.stronglyAdapted j).mono (ℱ.le j))

/-- A.s. `|M_j| ≤ j b` for `j ≤ k`. -/
lemma ConcFreedmanSetting.abs_M_le (S : ConcFreedmanSetting μ ℱ M v b k) :
    ∀ j ≤ k, ∀ᵐ ω ∂μ, |M j ω| ≤ j * b := by
  intro j
  induction j with
  | zero => intro _; exact Filter.Eventually.of_forall fun ω => by simp [S.zero]
  | succ j ih =>
    intro hj
    filter_upwards [ih (by omega), S.bound j (by omega)] with ω h1 h2
    have := abs_sub_abs_le_abs_sub (M (j + 1) ω) (M j ω)
    push_cast
    nlinarith

lemma ConcFreedmanSetting.Q_nonneg (S : ConcFreedmanSetting μ ℱ M v b k) {j : ℕ} (hj : j ≤ k)
    (ω : Ω) : 0 ≤ concQ v j ω :=
  Finset.sum_nonneg fun i hi => S.v_nonneg i (by simp at hi; omega) ω

lemma ConcFreedmanSetting.Q_meas (S : ConcFreedmanSetting μ ℱ M v b k) {j : ℕ} (hj : j ≤ k) :
    StronglyMeasurable[ℱ j] (concQ v j) := by
  unfold concQ
  have : (fun ω => ∑ i ∈ Finset.range j, v (i + 1) ω) = ∑ i ∈ Finset.range j, v (i + 1) := by
    funext ω; simp
  rw [this]
  refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
  have hi' : i < j := by simpa using hi
  exact (S.v_meas i (by omega)).mono (ℱ.mono hi'.le)

lemma ConcFreedmanSetting.Z_meas (S : ConcFreedmanSetting μ ℱ M v b k) (l ψ : ℝ) {j : ℕ}
    (hj : j ≤ k) : StronglyMeasurable[ℱ j] (concZ M v l ψ j) := by
  unfold concZ
  exact Real.continuous_exp.comp_stronglyMeasurable
    (((S.martingale.stronglyAdapted j).const_mul l).sub ((S.Q_meas hj).const_mul ψ))

lemma ConcFreedmanSetting.noExc_meas (S : ConcFreedmanSetting μ ℱ M v b k) (x : ℝ) (j : ℕ) :
    MeasurableSet[ℱ j] (concNoExc M x j) := by
  have : concNoExc M x j = ⋂ i ∈ Finset.Icc 1 j, M i ⁻¹' Set.Iio x := by
    ext ω
    simp only [concNoExc, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc, Set.mem_preimage,
      Set.mem_Iio, and_imp]
  rw [this]
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun i hi => ?_
  have hi' : i ≤ j := (Finset.mem_Icc.1 hi).2
  exact ((S.martingale.stronglyAdapted i).mono (ℱ.mono hi')).measurable measurableSet_Iio

lemma ConcFreedmanSetting.Z_le (S : ConcFreedmanSetting μ ℱ M v b k) {l ψ : ℝ} (hl : 0 < l)
    (hψ : 0 ≤ ψ) (_hb : 0 ≤ b) {j : ℕ} (hj : j ≤ k) :
    ∀ᵐ ω ∂μ, concZ M v l ψ j ω ≤ Real.exp (l * (j * b)) := by
  filter_upwards [S.abs_M_le j hj] with ω h
  unfold concZ
  apply Real.exp_le_exp.2
  have := S.Q_nonneg hj ω
  have := (le_abs_self (M j ω)).trans h
  nlinarith

lemma ConcFreedmanSetting.Z_integrable [IsFiniteMeasure μ] (S : ConcFreedmanSetting μ ℱ M v b k) {l ψ : ℝ}
    (hl : 0 < l) (hψ : 0 ≤ ψ) (hb : 0 ≤ b) {j : ℕ} (hj : j ≤ k) :
    Integrable (concZ M v l ψ j) μ := by
  refine Integrable.of_bound (((S.Z_meas l ψ hj).mono (ℱ.le j)).aestronglyMeasurable)
    (Real.exp (l * (j * b))) ?_
  filter_upwards [S.Z_le hl hψ hb hj] with ω h
  rw [Real.norm_of_nonneg (concZ_pos _ _).le]; exact h

lemma ConcFreedmanSetting.condExp_diff [IsFiniteMeasure μ] (S : ConcFreedmanSetting μ ℱ M v b k)
    (j : ℕ) :
    μ[M (j + 1) - M j | ℱ j] =ᵐ[μ] 0 := by
  have h1 := condExp_sub (m := ℱ j) (S.martingale.integrable (j + 1)) (S.martingale.integrable j)
  have h2 := S.martingale.condExp_ae_eq (Nat.le_succ j)
  have h3 : μ[M j | ℱ j] = M j :=
    condExp_of_stronglyMeasurable (ℱ.le j) (S.martingale.stronglyAdapted j)
      (S.martingale.integrable j)
  filter_upwards [h1, h2] with ω a1 a2
  simp [a1, a2, h3]

/-- Freedman's inequality, maximal form, Step 2: `E[Y_n] ≤ 1` for `n ≤ k`. -/
lemma ConcFreedmanSetting.integral_Y_le (S : ConcFreedmanSetting μ ℱ M v b k)
    [IsProbabilityMeasure μ] {l x : ℝ} (hb : 0 < b) (hl : 0 < l) :
    ∀ n ≤ k, Integrable (concY M v l (concPhi (l * b) / b ^ 2) x n) μ ∧
      ∫ ω, concY M v l (concPhi (l * b) / b ^ 2) x n ω ∂μ ≤ 1 := by
  set ψ : ℝ := concPhi (l * b) / b ^ 2 with hψ
  have hψpos : 0 ≤ ψ := by
    have := sq_div_two_le_concPhi (w := l * b) (by positivity)
    have : 0 < concPhi (l * b) := lt_of_lt_of_le (by positivity) this
    positivity
  intro n
  induction n with
  | zero =>
    intro _
    have : concY M v l ψ x 0 = fun _ => 1 := by funext ω; simp [concY]
    rw [this]; simp
  | succ n ih =>
    intro hn
    obtain ⟨hint, hle⟩ := ih (by omega)
    have hmeasE : MeasurableSet (concNoExc M x n) := ℱ.le n _ (S.noExc_meas x n)
    have hZn := S.Z_integrable hl hψpos hb.le (j := n) (by omega)
    have hZn1 := S.Z_integrable hl hψpos hb.le (j := n + 1) hn
    have hind1 : Integrable ((concNoExc M x n).indicator (concZ M v l ψ (n + 1))) μ :=
      hZn1.indicator hmeasE
    have hind0 : Integrable ((concNoExc M x n).indicator (concZ M v l ψ n)) μ :=
      hZn.indicator hmeasE
    have hfun : concY M v l ψ x (n + 1) = fun ω => concY M v l ψ x n ω +
        ((concNoExc M x n).indicator (concZ M v l ψ (n + 1)) ω -
          (concNoExc M x n).indicator (concZ M v l ψ n) ω) := by
      funext ω
      rw [concY_succ]
      by_cases h : ω ∈ concNoExc M x n <;> simp [h]
    have hint' : Integrable (concY M v l ψ x (n + 1)) μ := by
      rw [hfun]; exact hint.add (hind1.sub hind0)
    refine ⟨hint', ?_⟩
    rw [hfun]
    beta_reduce
    have e := integral_add hint (hind1.sub hind0)
    simp only [Pi.sub_apply] at e
    rw [e, integral_sub hind1 hind0]
    -- the step lemma
    have hDmeas : Measurable (M (n + 1) - M n) :=
      ((S.M_meas (n + 1)).sub (S.M_meas n)).measurable
    have hstep := concFreedman_step (μ := μ) (𝒢 := ℱ n) (ℱ.le n) (b := b) (l := l) hb hl
      (D := M (n + 1) - M n) (v := v (n + 1))
      (G := (concNoExc M x n).indicator (concZ M v l ψ n)) hDmeas
      (S.bound n (by omega)) (S.condExp_diff n) (S.v_meas n (by omega))
      (S.v_nonneg n (by omega)) (S.var_le n (by omega))
      (((S.Z_meas l ψ (by omega)).indicator (S.noExc_meas x n)))
      (fun ω => Set.indicator_nonneg (fun _ _ => (concZ_pos _ _).le) ω)
      (c := Real.exp (l * (n * b))) ?_
    · have heq : (fun ω => (concNoExc M x n).indicator (concZ M v l ψ n) ω *
          Real.exp (l * (M (n + 1) - M n) ω - ψ * v (n + 1) ω)) =
          (concNoExc M x n).indicator (concZ M v l ψ (n + 1)) := by
        funext ω
        by_cases h : ω ∈ concNoExc M x n
        · simp only [Set.indicator_of_mem h, Pi.sub_apply]
          rw [concZ_succ]
        · simp [h]
      rw [heq] at hstep
      linarith
    · filter_upwards [S.Z_le hl hψpos hb.le (j := n) (by omega)] with ω h
      by_cases hω : ω ∈ concNoExc M x n
      · rw [Set.indicator_of_mem hω]; exact h
      · rw [Set.indicator_of_notMem hω]; exact (Real.exp_pos _).le

end Setting

end ElboimSly
