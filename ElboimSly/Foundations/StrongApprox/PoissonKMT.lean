/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Dyadic

/-!
# Marginals of the dyadic coupling

Written proof: proof of a1: KMT coupling for Poisson increments (marginals). The first `N` leaves of the tree of depth
`2L` have the laws `Poisson(1)^{⊗N}` and `𝒩(0,1)^{⊗N}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly
namespace StrongApprox

/-- Restricting an i.i.d. vector to its first `N` coordinates. -/
theorem measurePreserving_restrict {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    [IsProbabilityMeasure ρ] {N M : ℕ} (h : N ≤ M) :
    MeasurePreserving (fun (x : Fin M → α) (i : Fin N) => x (Fin.castLE h i))
      (Measure.pi fun _ : Fin M => ρ) (Measure.pi fun _ : Fin N => ρ) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le h
  have hc := measurePreserving_cat ρ N K (N + K) rfl
  have hr : Measurable (fun (x : Fin (N + K) → α) (i : Fin N) => x (Fin.castLE h i)) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  refine ⟨hr, ?_⟩
  rw [← hc.map_eq, Measure.map_map hr hc.measurable]
  have : ((fun (x : Fin (N + K) → α) (i : Fin N) => x (Fin.castLE h i)) ∘ cat N K (N + K) rfl) =
      Prod.fst := by
    funext x i
    simp [cat, Function.comp]
  rw [this]
  exact Measure.map_fst_prod.trans (by simp)

/-- The first `N` Poisson leaves, as real numbers. -/
noncomputable def leafP (L N : ℕ) (hN : N ≤ 2 ^ (2 * L)) (ω : ℕ × ℝ × DT (2 * L)) :
    Fin N → ℝ :=
  fun i => (LP (2 * L) ω.1 ω.2.2 (Fin.castLE hN i) : ℝ)

/-- The first `N` Gaussian leaves. -/
noncomputable def leafG (L N : ℕ) (hN : N ≤ 2 ^ (2 * L)) (ω : ℕ × ℝ × DT (2 * L)) :
    Fin N → ℝ :=
  fun i => LG (2 * L) (2 ^ L * ω.2.1) ω.2.2 (Fin.castLE hN i)

theorem leafP_law (L N : ℕ) (hN : N ≤ 2 ^ (2 * L)) :
    (Pdy (2 * L)).map (leafP L N hN) =
      Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ) := by
  have h1 : MeasurePreserving (fun ω : ℕ × ℝ × DT (2 * L) => (ω.1, ω.2.2)) (Pdy (2 * L))
      ((poissonMeasure (2 ^ (2 * L))).prod (muDT (2 * L))) :=
    (MeasurePreserving.id (poissonMeasure (2 ^ (2 * L)))).prod (measurePreserving_snd)
  have h2 := (measurePreserving_restrict (poissonMeasure 1) hN).comp (tree_law_P (2 * L))
  have h3 := h2.comp h1
  have hcast : Measurable (Nat.cast : ℕ → ℝ) := measurable_from_top
  have h4 : MeasurePreserving (fun (x : Fin N → ℕ) (i : Fin N) => ((x i : ℕ) : ℝ))
      (Measure.pi fun _ : Fin N => poissonMeasure 1)
      (Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :=
    ⟨Measurable.of_eval fun i => hcast.comp (measurable_pi_apply i),
      Measure.pi_map_pi (fun _ => hcast.aemeasurable)⟩
  have := h4.comp h3
  exact this.map_eq

theorem leafG_law (L N : ℕ) (hN : N ≤ 2 ^ (2 * L)) :
    (Pdy (2 * L)).map (leafG L N hN) = Measure.pi fun _ : Fin N => gaussianReal 0 1 := by
  have h1 : MeasurePreserving (fun ω : ℕ × ℝ × DT (2 * L) => (ω.2.1, ω.2.2)) (Pdy (2 * L))
      (saN.prod (muDT (2 * L))) :=
    measurePreserving_snd
  have hs : MeasurePreserving (fun x : ℝ => (2 : ℝ) ^ L * x) saN
      (gaussianReal 0 (2 ^ (2 * L))) := by
    refine measurePreserving_gaussian_scale _ _ _ ?_
    push_cast
    rw [pow_mul']; simp
  have h2 : MeasurePreserving (fun ω : ℕ × ℝ × DT (2 * L) => (2 ^ L * ω.2.1, ω.2.2))
      (Pdy (2 * L)) ((gaussianReal 0 (2 ^ (2 * L))).prod (muDT (2 * L))) :=
    (hs.prod (MeasurePreserving.id (muDT (2 * L)))).comp h1
  have h3 := ((measurePreserving_restrict (gaussianReal 0 1) hN).comp (tree_law_G (2 * L))).comp h2
  exact h3.map_eq

theorem sum_filter_eq (L N : ℕ) (hN : N ≤ 2 ^ (2 * L)) (ω : ℕ × ℝ × DT (2 * L)) (j : Fin N) :
    ∑ i ∈ Finset.univ.filter (· ≤ j), (leafP L N hN ω i - 1 - leafG L N hN ω i) =
      Spart (2 * L) ω.1 (2 ^ L * ω.2.1) ω.2.2 (j + 1) := by
  unfold Spart leafP leafG
  have himg : (Finset.univ.filter (· ≤ j)).image (fun i : Fin N => (i : ℕ)) =
      Finset.range ((j : ℕ) + 1) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact Nat.lt_succ_of_le hi
    · intro hk
      exact ⟨⟨k, by omega⟩, by simp [Fin.le_def]; omega, rfl⟩
  rw [← himg, Finset.sum_image (fun a _ b _ h => Fin.ext h)]
  simp

theorem c3_pos : 0 < c3 := by
  unfold c3
  have h := theta0_pos
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  positivity

theorem measurable_leafP (L N : ℕ) (hN : N ≤ 2 ^ (2 * L)) : Measurable (leafP L N hN) := by
  refine Measurable.of_eval fun i => ?_
  exact (measurable_from_top (f := (Nat.cast : ℕ → ℝ))).comp
    ((measurable_LP (2 * L) _).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem measurable_leafG (L N : ℕ) (hN : N ≤ 2 ^ (2 * L)) : Measurable (leafG L N hN) := by
  refine Measurable.of_eval fun i => ?_
  have h : Measurable (fun ω : ℕ × ℝ × DT (2 * L) => ((2 : ℝ) ^ L * ω.2.1, ω.2.2)) :=
    (measurable_const.mul (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  exact (measurable_LG (2 * L) _).comp h

/-- The KMT coupling for Poisson increments, with the statement of `ElboimSly.poisson_kmt_coupling`. -/
theorem poisson_kmt_coupling_aux :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin N → ℝ) × (Fin N → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin N => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 ≤ x →
          Q.real {p | ∃ j : Fin N,
              C * Real.log N + x ≤ |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|}
            ≤ K * Real.exp (-lam * x) := by
  have hθ := theta0_pos
  have hc3 := c3_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set AR := Real.exp (3 / 4) + Real.exp (1 / 8) with hAR
  have hAR0 : 0 < AR := by positivity
  refine ⟨2 * c3 / Real.log 2, (AR + 19) * Real.exp (2 * c3 * (theta0 / 4)), theta0 / 4,
    by positivity, by positivity, by positivity, fun N => ?_⟩
  set L := Nat.clog 2 (N + 1) with hL
  have hNL : N + 1 ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) _
  have hN : N ≤ 2 ^ (2 * L) :=
    le_trans (by omega) (le_trans hNL (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine ⟨(Pdy (2 * L)).map (fun ω => (leafP L N hN ω, leafG L N hN ω)), ?_, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Measure.map_map measurable_fst
      ((measurable_leafP L N hN).prodMk (measurable_leafG L N hN))]
    exact leafP_law L N hN
  · rw [Measure.map_map measurable_snd
      ((measurable_leafP L N hN).prodMk (measurable_leafG L N hN))]
    exact leafG_law L N hN
  intro x hx
  set Phi := fun ω : ℕ × ℝ × DT (2 * L) => (leafP L N hN ω, leafG L N hN ω) with hPhi
  have hPhim : Measurable Phi := (measurable_leafP L N hN).prodMk (measurable_leafG L N hN)
  set Cc := 2 * c3 / Real.log 2 with hCc
  set S : Set ((Fin N → ℝ) × (Fin N → ℝ)) := {p | ∃ j : Fin N,
      Cc * Real.log N + x ≤ |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|} with hS
  have hSm : MeasurableSet S := by
    have : S = ⋃ j : Fin N, {p : (Fin N → ℝ) × (Fin N → ℝ) |
        Cc * Real.log N + x ≤ |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|} := by
      ext p; simp [hS]
    rw [this]
    refine MeasurableSet.iUnion fun j => ?_
    refine measurableSet_le measurable_const ?_
    have : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
        ∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)) :=
      Finset.measurable_sum _ fun i _ =>
        (((measurable_pi_apply i).comp measurable_fst).sub measurable_const).sub
          ((measurable_pi_apply i).comp measurable_snd)
    simpa only [Real.norm_eq_abs] using this.norm
  have hQ : ((Pdy (2 * L)).map Phi).real S = ((Pdy (2 * L)) (Phi ⁻¹' S)).toReal := by
    rw [measureReal_def, Measure.map_apply hPhim hSm]
  set lam := theta0 / 4 with hlam
  set K := (AR + 19) * Real.exp (2 * c3 * lam) with hK
  have hKpos : 0 < K := by positivity
  rw [hQ]
  by_cases hxc : x < 2 * c3
  · have h1 : ((Pdy (2 * L)) (Phi ⁻¹' S)).toReal ≤ 1 := by
      have := prob_le_one (μ := Pdy (2 * L)) (s := Phi ⁻¹' S)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    refine h1.trans ?_
    have : 1 ≤ K * Real.exp (-lam * x) := by
      have e : K * Real.exp (-lam * x) = (AR + 19) * Real.exp (lam * (2 * c3 - x)) := by
        rw [hK, mul_assoc, ← Real.exp_add]; congr 2; ring
      rw [e]
      have : 1 ≤ Real.exp (lam * (2 * c3 - x)) :=
        Real.one_le_exp (by have : 0 < lam := by positivity
                            nlinarith)
      nlinarith [Real.exp_pos (lam * (2 * c3 - x))]
    exact this
  · rw [not_lt] at hxc
    have hsub : Phi ⁻¹' S ⊆ {ω | ∃ j < 2 ^ L,
        2 * c3 * L + (x - 2 * c3) ≤ |Spart (2 * L) ω.1 (2 ^ L * ω.2.1) ω.2.2 j|} := by
      intro ω ⟨j, hj⟩
      have hN1 : 1 ≤ N := by have := j.2; omega
      have hLpos : 1 ≤ L := by
        by_contra hh
        have : L = 0 := by omega
        rw [this] at hNL; simp at hNL; omega
      have hlt : 2 ^ (L - 1) < N + 1 := by
        have := Nat.pow_pred_clog_lt_self (b := 2) (x := N + 1) (by norm_num) (by omega)
        rwa [← hL] at this
      have hle : (2 : ℝ) ^ (L - 1) ≤ N := by
        have : 2 ^ (L - 1) ≤ N := by omega
        exact_mod_cast this
      have hlog : ((L : ℝ) - 1) * Real.log 2 ≤ Real.log N := by
        have := Real.log_le_log (by positivity) hle
        rw [Real.log_pow] at this
        have e : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
          rw [Nat.cast_sub hLpos]; simp
        rwa [e] at this
      have hCL : 2 * c3 * L ≤ Cc * Real.log N + 2 * c3 := by
        rw [hCc]
        have : 2 * c3 * ((L : ℝ) - 1) ≤ 2 * c3 / Real.log 2 * Real.log N := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
          nlinarith
        linarith
      refine ⟨(j : ℕ) + 1, by have := j.2; omega, ?_⟩
      have := sum_filter_eq L N hN ω j
      simp only [hPhi] at hj
      rw [this] at hj
      linarith
    have hP := prop_dyadic L (x - 2 * c3) (by linarith)
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (measure_mono hsub).trans (hP.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    refine le_of_eq ?_
    rw [hK, hAR, mul_assoc, ← Real.exp_add]
    congr 2
    rw [hlam]; ring

end StrongApprox
end ElboimSly
