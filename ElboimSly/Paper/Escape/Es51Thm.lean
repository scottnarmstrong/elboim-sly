/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Prop
public import ElboimSly.Foundations.Cyclic.CycFar
public import ElboimSly.Paper.Escape.Es51Num
public import Mathlib

/-!
# ES22 Theorem 5.1: the union bound over blocks

ES22 Theorem 5.1 proof.  On `{τ_esc < t_n ∧ t_reg}` some block `B_u` of `𝓑_j` has
`ξ_{B_u} < t_n ∧ t_reg` and `π_{B_u} ≤ n^{-γ}`; either the walk leaves the box
`[-10 d t_n, 10 d t_n]^d` before `t_n` (`cyc_far`, probability `≤ e^{-t_n}`), or `B_u` is one of
the `(2K+3)^d` blocks meeting that box, each of probability `≤ e^{-c₅₂ n³}` by ES22 Proposition 5.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The corner of the block with index `a`. -/
def cornerOf (j : ℕ) (a : Fin (k + 2) → ℤ) : Fin (k + 2) → ℤ := fun c => 2 ^ j * a c

theorem escBlocks_corner {j : ℕ} {B : Set (Fin (k + 2) → ℤ)} (hB : B ∈ escBlocks k j) :
    ∃ a : Fin (k + 2) → ℤ, B = escBlock j (cornerOf j a) := by
  obtain ⟨u, hu, rfl⟩ := hB
  choose a ha using hu
  refine ⟨a, ?_⟩
  have : cornerOf j a = u := funext fun c => (ha c).symm
  rw [this]

theorem cornerOf_admissible (j : ℕ) (a : Fin (k + 2) → ℤ) : EscAdmissible j (cornerOf j a) := by
  by_cases h : cornerOf j a = 0
  · exact Or.inr h
  · left
    intro h0
    apply h
    funext c
    have h1 := h0 c
    simp only [cornerOf, Pi.zero_apply] at h1 ⊢
    have h2 : (0 : ℤ) < 2 ^ j := by positivity
    have h3 : a c ≤ 0 := by nlinarith [h1.1]
    have h4 : 0 ≤ a c := by nlinarith [h1.2]
    have : a c = 0 := le_antisymm h3 h4
    rw [this]; simp

section tau

variable {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- The bad event for the block with corner `u`: `ξ_B ≤ t_n`, `ξ_B < t_reg`, `π_B ≤ n^{-γ}`. -/
def escBadSet (Pr : Measure Ω) (N : Ω → Measure (CycS ℕ (k + 2) β)) (n : ℕ) (tn : ℝ)
    (u : Fin (k + 2) → ℤ) : Set Ω :=
  {ω | escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escPi Pr N n (escJ n) tn (escBlock (escJ n) u) ω ≤
          ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))}

/-- **The union bound of ES22 Theorem 5.1.** -/
theorem tau_esc_le (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (K : ℕ)
    (hK : 10 * ((k + 2 : ℕ) : ℝ) * indScale t₀ n ≤ K) (q : ℝ≥0∞)
    (hq : ∀ a : Fin (k + 2) → ℤ, (∀ c, -(K : ℤ) - 1 ≤ a c ∧ a c ≤ K) →
      Pr (escBadSet Pr N n (indScale t₀ n) (cornerOf (escJ n) a)) ≤ q) :
    Pr {ω | escTauEsc Pr N n (escJ n) (indScale t₀ n) (escGamma (k + 2)) ω <
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (copyEnv (N ω) 0))} ≤
      ENNReal.ofReal (Real.exp (-(indScale t₀ n))) + (2 * K + 2) ^ (k + 2) * q := by
  have hpr := hS.space.ppp.isProbabilityMeasure
  have htn : 0 < indScale t₀ n := indScale_pos' hS
  have hgood := CycSchemeEnv.ae_cycGood' hS.space.ppp
  set tn := indScale t₀ n with htn_def
  set A : Finset (Fin (k + 2) → ℤ) :=
    Fintype.piFinset (fun _ : Fin (k + 2) => Finset.Icc (-(K : ℤ) - 1) K) with hA
  set F : Set Ω := {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ tn ∧ 10 * ((k + 2 : ℕ) : ℝ) * 1 * tn ≤
      ‖ElboimSly.regenWalk (fun i => cycSlice i (N ω)) (s : ℝ)‖} with hF
  have hFle : Pr F ≤ ENNReal.ofReal (Real.exp (-(tn))) := by
    have h := cyc_far (d := k + 2) (by omega) hS.space.ppp (L := 1) (t := tn) le_rfl htn.le
    rw [← ENNReal.ofReal_toReal (measure_ne_top Pr F)]
    refine ENNReal.ofReal_le_ofReal ?_
    simpa [Measure.real, hF] using h
  have hcard : (A.card : ℝ≥0∞) = (2 * K + 2) ^ (k + 2) := by
    have h1 : (Finset.Icc (-(K : ℤ) - 1) K).card = 2 * K + 2 := by
      rw [Int.card_Icc]; omega
    have : A.card = (2 * K + 2) ^ (k + 2) := by
      rw [hA, Fintype.card_piFinset]; simp [h1]
    rw [this]; push_cast; rfl
  have hsub : {ω | escTauEsc Pr N n (escJ n) tn (escGamma (k + 2)) ω <
        min (ENNReal.ofReal tn) (cycTreg (copyEnv (N ω) 0))} ≤ᵐ[Pr]
      (F ∪ ⋃ a ∈ A, escBadSet Pr N n tn (cornerOf (escJ n) a)) := by
    filter_upwards [hgood] with ω hg h
    unfold escTauEsc at h
    rw [iInf_lt_iff] at h
    obtain ⟨B, h⟩ := h
    rw [iInf_lt_iff] at h
    obtain ⟨hB, h⟩ := h
    rw [iInf_lt_iff] at h
    obtain ⟨⟨hc1, hc2⟩, h⟩ := h
    obtain ⟨a, rfl⟩ := escBlocks_corner hB
    have hlt1 := lt_of_lt_of_le h (min_le_left _ _)
    have hlt2 := lt_of_lt_of_le h (min_le_right _ _)
    by_cases hfar : ω ∈ F
    · exact Or.inl hfar
    · right
      simp only [mem_iUnion, exists_prop]
      refine ⟨a, ?_, hc1, hlt2, hc2⟩
      have hfin : escXi (escWalk (N ω)) (escBlock (escJ n) (cornerOf (escJ n) a)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hc1
      have hmem := escWalk_xi_mem (n := n) hg hfin
      set ξ := escXi (escWalk (N ω)) (escBlock (escJ n) (cornerOf (escJ n) a)) with hξ
      have hξle : ξ.toReal ≤ tn := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc1
        rwa [ENNReal.toReal_ofReal htn.le] at this
      have hnorm : ‖escWalk (N ω) ξ.toReal‖ < 10 * ((k + 2 : ℕ) : ℝ) * 1 * tn := by
        by_contra hge
        push Not at hge
        apply hfar
        refine ⟨ξ.toReal.toNNReal, ?_, ?_⟩
        · rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg]; exact hξle
        · rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg]
          have e : escWalk (N ω) = ElboimSly.regenWalk (fun i => cycSlice i (N ω)) := by
            funext x; unfold escWalk; simp only [copyEnv_eq_cycSlice]
          rw [e] at hge; exact hge
      rw [hA, Fintype.mem_piFinset]
      intro c
      have hcoord : |(escWalk (N ω) ξ.toReal c : ℝ)| < K := by
        have h1 : ‖escWalk (N ω) ξ.toReal c‖ ≤ ‖escWalk (N ω) ξ.toReal‖ := norm_le_pi_norm _ c
        rw [Int.norm_eq_abs] at h1
        have : (|escWalk (N ω) ξ.toReal c| : ℝ) = |(escWalk (N ω) ξ.toReal c : ℝ)| := by
          rfl
        linarith [hK]
      have hW := hmem c
      simp only [cornerOf] at hW
      have hi : |escWalk (N ω) ξ.toReal c| < K := by exact_mod_cast hcoord
      rw [abs_lt] at hi
      rw [Finset.mem_Icc]
      have h2 : (0 : ℤ) < 2 ^ escJ n := by positivity
      have h1 : (1 : ℤ) ≤ 2 ^ escJ n := one_le_pow₀ (by norm_num)
      constructor
      · by_contra hlt
        push Not at hlt
        nlinarith [hW.2, hi.1]
      · by_contra hlt
        push Not at hlt
        nlinarith [hW.1, hi.2]
  calc _ ≤ Pr (F ∪ ⋃ a ∈ A, escBadSet Pr N n tn (cornerOf (escJ n) a)) := measure_mono_ae hsub
    _ ≤ Pr F + Pr (⋃ a ∈ A, escBadSet Pr N n tn (cornerOf (escJ n) a)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-tn)) + ∑ a ∈ A, Pr (escBadSet Pr N n tn (cornerOf (escJ n) a)) :=
        add_le_add hFle (measure_biUnion_finset_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-tn)) + ∑ a ∈ A, q := by
        gcongr with a ha
        exact hq a (fun c => Finset.mem_Icc.1 (Fintype.mem_piFinset.1 ha c))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

end tau

/-- The statement of ES22 Theorem 5.1: `c₅₁` depends only on `d`, `β₅` on `(d, n₀)`. -/
def Es51Concl (k : ℕ) : Prop :=
  ∃ c51 : ℝ, 0 < c51 ∧ ∃ β5 : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
    {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
    (_ : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N'), β5 n₀ ≤ β →
      Pr {ω | escTauEsc Pr N n (escJ n) (indScale t₀ n) (escGamma (k + 2)) ω <
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (copyEnv (N ω) 0))} ≤
        ENNReal.ofReal (Real.exp (-(c51 * (n : ℝ) ^ 3)))

/-- **ES22 Theorem 5.1** from ES22 Proposition 5.2, `cyc_far` and the block count. -/
theorem es5_1_of_es52 (h52 : Es52Concl k) : Es51Concl k := by
  obtain ⟨c52, hc52, β52, h52⟩ := h52
  set d : ℕ := k + 2 with hd
  set M : ℕ := max (max 2000 ⌈2 * (96 * (d : ℝ) ^ 2 + 3 * d + 1) / c52⌉₊)
    ⌈24 * (c52 / 2 + 1)⌉₊ with hM
  refine ⟨c52 / 2, by positivity, fun n₀ => max (β52 n₀) ((4 : ℝ) ^ (M + 1)), ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS hβ
  have hp := hS.params
  have h52le : β52 n₀ ≤ β := (le_max_left _ _).trans hβ
  have hMn : M ≤ n := le_of_four_pow_le hp.le_four hp.beta_lt ((le_max_right _ _).trans hβ)
  have hn0 : 2000 ≤ n := (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hMn))
  have hn1 : 2 * (96 * (d : ℝ) ^ 2 + 3 * d + 1) / c52 ≤ n := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hMn))
  have hn2 : 24 * (c52 / 2 + 1) ≤ n := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_trans (le_max_right _ _) hMn)
  have htn1 : (4 : ℝ) ^ n ≤ indScale t₀ n := by
    unfold indScale
    have := hp.one_lt
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    nlinarith
  have htn2 : indScale t₀ n ≤ 4 ^ (n + 1) := by
    unfold indScale
    rw [pow_succ]
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    nlinarith [hp.le_four]
  have htn0 : 0 < indScale t₀ n := indScale_pos' hS
  set tn := indScale t₀ n with htn_def
  set K : ℕ := ⌈10 * (d : ℝ) * tn⌉₊ with hK
  have hKle : 10 * ((k + 2 : ℕ) : ℝ) * tn ≤ K := Nat.le_ceil _
  have hKge : (K : ℝ) ≤ 10 * (d : ℝ) * tn + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hq := tau_esc_le hS K hKle (ENNReal.ofReal (Real.exp (-(c52 * (n : ℝ) ^ 3))))
    (fun a _ => h52 hS h52le (cornerOf (escJ n) a) (cornerOf_admissible _ a))
  refine hq.trans ?_
  have hreal := thm51_real (d := d) (by omega) hc52 hn0 hn1 hn2 htn1 htn2 K hKge
  have e1 : ((2 * K + 2 : ℝ≥0∞)) = ENNReal.ofReal (2 * K + 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e1, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end ElboimSly.Paper.Escape
