/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Lemma76BM
public import ElboimSly.Foundations.StrongApprox.Lemma76Num
public import ElboimSly.Foundations.StrongApprox.SaLift
public import ElboimSly.Foundations.StrongApprox.X1Explicit
public import ElboimSly.Foundations.Brownian.Invariance
public import Mathlib

/-!
# The coupling step of Lemma 7.6, re-tuned

The coupling step of Lemma 7.6, re-tuned (with how Lemma 7.6 applies crefcor:sa-lemma76).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

universe u v w

/-- The bad set of `x1_explicit` is measurable. -/
theorem measurableSet_x1Bad (d ℓ : ℕ) (thr : ℝ) :
    MeasurableSet {p : (Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ) | ∃ j : Fin ℓ,
      thr ≤ ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖} := by
  have : {p : (Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ) | ∃ j : Fin ℓ,
      thr ≤ ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖} =
      ⋃ j : Fin ℓ, {p | thr ≤ ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖} := by
    ext p; simp
  rw [this]
  refine MeasurableSet.iUnion fun j => measurableSet_le measurable_const ?_
  refine measurable_norm.comp (Finset.measurable_sum _ fun i _ => ?_)
  exact ((measurable_pi_apply i).comp measurable_fst).sub
    ((measurable_pi_apply i).comp measurable_snd)

/-- The coupling step of Lemma 7.6, re-tuned (a)-(c): the coupling step of Lemma 7.6, re-tuned.  The block
sums are `∑_{i ≤ j} Y(w_i)` for `j : Fin ℓ` (the written proof's `j+1`), and `Δ ≥ r` is
`∃ j : Fin ℓ, r ≤ ‖√T ∑_{i ≤ j} Y(w_i) - σ B((j+1)T)‖`. -/
theorem sa_lemma76 (d : ℕ) (hd : 1 ≤ d) {n : ℕ} (hn : nX d ≤ n) {t : ℝ} (ht1 : (4 : ℝ) ^ n < t)
    (ht2 : t ≤ 4 ^ (n + 1)) {ℓ : ℕ} (hℓ1 : t ^ ((79 : ℝ) / 200) / 2 ≤ ℓ)
    (hℓ2 : (ℓ : ℝ) ≤ 2 * t ^ ((79 : ℝ) / 200)) {T : ℝ} (hT : 0 < T) (hℓT : (ℓ : ℝ) * T ≤ 2 * t)
    {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    {E : Type v} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (Y : E → Fin d → ℝ) (hY : Measurable Y) (D : Set (Fin d → ℝ)) (hD : D.Countable)
    (hYD : ∀ w, Y w ∈ D) (hnorm : ∀ w, ‖Y w‖ ≤ (n : ℝ) ^ 2)
    (hsym : ∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) →
      (ν.map Y).map (fun x => ε * x) = ν.map Y)
    (hvar : ∀ k, ∫ w, Y w k ^ 2 ∂ν = σ ^ 2)
    {G : Type u} [MeasurableSpace G] (PG : Measure G) [IsProbabilityMeasure PG]
    (V : Fin ℓ → G → E) (hVm : ∀ i, Measurable (V i)) (hVind : iIndepFun V PG)
    (hVlaw : ∀ i, PG.map (V i) = ν) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (g : Ω' → G)
      (B : ℝ≥0 → Ω' → Fin d → ℝ),
      IsProbabilityMeasure P' ∧ Measurable g ∧ P'.map g = PG ∧
      IsStandardBrownianMotion d B P' ∧
      P' {ω | ∃ j : Fin ℓ, t ^ ((41 : ℝ) / 100) / 8 ≤
          ‖√T • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i (g ω)) -
            σ • B ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T.toNNReal) ω‖} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3 / 7)) ∧
      P' {ω | ∃ j : Fin ℓ, σ * √T * (ℓ : ℝ) ^ ((1 : ℝ) / 4) * Real.log ℓ ^ 12 ≤
          ‖√T • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i (g ω)) -
            σ • B ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T.toNNReal) ω‖} ≤
        ENNReal.ofReal (Real.exp (-(Real.log ℓ ^ 3))) ∧
      ∀ {Zs : Type w} [MeasurableSpace Zs] (Z : G → Zs), Measurable Z →
        P'.map (fun ω => (Z (g ω), fun i => V i (g ω))) =
          PG.map (fun e => (Z e, fun i => V i e)) := by
  have hσ0 : 0 < σ := by linarith
  have hn4 : 10 ^ 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn4
  obtain ⟨hℓ5, hℓd⟩ := ell_ge_threshold hd hn ht1 ht2 hℓ1
  have hℓN : max (10 ^ 5) (10 * d) ≤ ℓ :=
    max_le (by exact_mod_cast hℓ5) (by exact_mod_cast hℓd)
  have hℓpos : (0 : ℝ) < ℓ := lt_of_lt_of_le (by positivity) hℓ5
  have hlog := log_ell_ge hn4 ht1 ht2 hℓ1
  set M : ℝ := 2 * (n : ℝ) ^ 2 with hMdef
  have hM1 : 1 ≤ M := by nlinarith
  have hcube : (0.53 * (n : ℝ)) ^ 3 ≤ Real.log ℓ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hlog 3
  have hM : M ≤ Real.log ℓ ^ 3 := by nlinarith [sq_nonneg (n : ℝ), pow_pos (by linarith : (0 : ℝ) < n) 3]
  have hM7 : (n : ℝ) ^ 3 / 7 ≤ Real.log ℓ ^ 3 := by
    nlinarith [pow_pos (by linarith : (0 : ℝ) < n) 3]
  -- the law μ of Υ(w) = Y(w)/σ
  set Υ : E → Fin d → ℝ := fun w => σ⁻¹ • Y w with hΥ
  have hΥm : Measurable Υ := hY.const_smul σ⁻¹
  set μ : Measure (Fin d → ℝ) := ν.map Υ with hμ
  have hμp : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hΥm.aemeasurable).2 inferInstance
  have hsupp : μ {x | ‖x‖ ≤ M} = 1 := by
    rw [hμ, Measure.map_apply hΥm (measurableSet_le measurable_norm measurable_const)]
    have : Υ ⁻¹' {x | ‖x‖ ≤ M} = univ := by
      ext w
      simp only [mem_preimage, mem_ofPred_eq, mem_univ, iff_true, hΥ, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hσ0]
      rw [hMdef, inv_mul_le_iff₀ hσ0]
      nlinarith [hnorm w, sq_nonneg (n : ℝ)]
    rw [this]; simp
  have hsymμ : ∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) → μ.map (fun x => ε * x) = μ := by
    intro ε hε
    have h := hsym ε hε
    have e1 : μ = (ν.map Y).map (fun y => σ⁻¹ • y) := by
      rw [hμ, Measure.map_map (measurable_const_smul σ⁻¹) hY]; rfl
    have hε1 : Measurable fun x : Fin d → ℝ => ε * x := by fun_prop
    have hs1 : Measurable fun y : Fin d → ℝ => σ⁻¹ • y := measurable_const_smul σ⁻¹
    rw [e1, Measure.map_map hε1 hs1]
    have : ((fun x : Fin d → ℝ => ε * x) ∘ fun y => σ⁻¹ • y) =
        (fun y => σ⁻¹ • y) ∘ (fun x : Fin d → ℝ => ε * x) := by
      funext y k; simp only [Function.comp_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, ← Measure.map_map hs1 hε1, h]
  have hsq : ∀ k, ∫ x, x k ^ 2 ∂μ = 1 := by
    intro k
    rw [hμ, integral_map hΥm.aemeasurable ((measurable_pi_apply k).pow_const 2).aestronglyMeasurable]
    have : ∀ w, Υ w k ^ 2 = σ⁻¹ ^ 2 * Y w k ^ 2 := by
      intro w; simp [hΥ]; ring
    simp_rw [this]
    rw [integral_const_mul, hvar k]
    field_simp
  obtain ⟨Q, hQp, hQ1, hQ2, hQ3⟩ := x1_explicit ℓ hℓN M hM1 hM μ hμp hsupp hsymμ hsq
  have := hQp
  -- the gluing
  set Ξ : G → Fin ℓ → Fin d → ℝ := fun e i => Υ (V i e) with hΞ
  have hΞm : Measurable Ξ := measurable_pi_iff.2 fun i => hΥm.comp (hVm i)
  have hΞlaw : PG.map Ξ = Measure.pi fun _ : Fin ℓ => μ := by
    have h1 := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hVm i).aemeasurable)).1 hVind
    simp_rw [hVlaw] at h1
    have hfam : Measurable fun (e : G) (i : Fin ℓ) => V i e := measurable_pi_iff.2 hVm
    have e : Ξ = (fun (w : Fin ℓ → E) i => Υ (w i)) ∘ (fun (e : G) (i : Fin ℓ) => V i e) := rfl
    have hm : Measurable fun (w : Fin ℓ → E) (i : Fin ℓ) => Υ (w i) :=
      measurable_pi_iff.2 fun i => hΥm.comp (measurable_pi_apply i)
    rw [e, ← Measure.map_map hm hfam, h1]
    exact Measure.pi_map_pi (μ := fun _ : Fin ℓ => ν) (f := fun _ => Υ) (fun _ => hΥm.aemeasurable)
  have hfst : Q.map Prod.fst = PG.map Ξ := hQ1.trans hΞlaw.symm
  set C : Set (Fin ℓ → Fin d → ℝ) := Set.pi univ fun _ : Fin ℓ => (fun y => σ⁻¹ • y) '' D with hCdef
  have hC : C.Countable := by
    have : C = {f | ∀ a, f a ∈ (fun y => σ⁻¹ • y) '' D} := by
      ext f; simp [hCdef, Set.mem_pi]
    rw [this]
    exact Set.countable_pi fun _ => hD.image _
  have hrange : ∀ e, Ξ e ∈ C := fun e i _ => ⟨Y (V i e), hYD _, rfl⟩
  set Γh : Measure (G × (Fin ℓ → Fin d → ℝ)) := liftMeasure PG C Ξ Q with hΓh
  have hΓ1 : Γh.map Prod.fst = PG := liftMeasure_map_fst hC hΞm hrange hfst
  have hΓ2 : Γh.map (fun p : G × (Fin ℓ → Fin d → ℝ) => (Ξ p.1, p.2)) = Q :=
    liftMeasure_map_Ξ hC hΞm hrange hfst
  have hΓp : IsProbabilityMeasure Γh :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).1 (by rw [hΓ1]; infer_instance)
  have hΦm : Measurable fun p : G × (Fin ℓ → Fin d → ℝ) => (Ξ p.1, p.2) :=
    (hΞm.comp measurable_fst).prodMk measurable_snd
  have hzlaw : Γh.map Prod.snd =
      Measure.pi fun _ : Fin ℓ => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
    have : (Prod.snd : G × (Fin ℓ → Fin d → ℝ) → _) = Prod.snd ∘ (fun p : G × (Fin ℓ → Fin d → ℝ) => (Ξ p.1, p.2)) := rfl
    rw [this, ← Measure.map_map measurable_snd hΦm, hΓ2]; exact hQ2
  obtain ⟨B', hB', hB'sum⟩ := bm_of_override Γh Prod.snd measurable_snd hzlaw
  -- the space
  set P' : Measure (((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d) :=
    (Γh.prod (PX d)).prod (PH d) with hP'
  set T' : ℝ≥0 := T.toNNReal with hT'
  have hT'coe : (T' : ℝ) = T := Real.coe_toNNReal _ hT.le
  have hT'ne : T' ≠ 0 := by
    intro h; rw [h] at hT'coe; simp at hT'coe; linarith
  have hsc : IsStandardBrownianMotion d (fun s ω => √T • B' (T'⁻¹ * s) ω) P' :=
    hB'.scaling (a := √T) (c := T'⁻¹) (inv_ne_zero hT'ne)
      (by rw [Real.sq_sqrt hT.le, NNReal.coe_inv, hT'coe]; field_simp)
  have hfst2 : P'.map (Prod.fst ∘ Prod.fst : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d → G × (Fin ℓ → Fin d → ℝ)) = Γh := by
    rw [← Measure.map_map measurable_fst measurable_fst, hP']
    simp [Measure.map_fst_prod]
  have hexpr : ∀ (ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d) (j : Fin ℓ),
      √T • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i ω.1.1.1) -
        σ • (fun s ω => √T • B' (T'⁻¹ * s) ω) ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T') ω =
      (σ * √T) • ∑ i ∈ Finset.univ.filter (· ≤ j), (Ξ ω.1.1.1 i - ω.1.1.2 i) := by
    intro ω j
    have h1 : T'⁻¹ * ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T') = (((j : ℕ) + 1 : ℕ) : ℝ≥0) := by
      rw [mul_comm _ T', ← mul_assoc, inv_mul_cancel₀ hT'ne, one_mul]
    simp only [h1]
    rw [hB'sum j ω, Finset.sum_sub_distrib]
    have h2 : ∑ i ∈ Finset.univ.filter (· ≤ j), Ξ ω.1.1.1 i =
        σ⁻¹ • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i ω.1.1.1) := by
      rw [Finset.smul_sum]
    have e1 : (σ * √T) • (σ⁻¹ • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i ω.1.1.1)) =
        √T • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i ω.1.1.1) := by
      rw [smul_smul]; congr 1; field_simp
    have e2 : (σ * √T) • ∑ i ∈ Finset.univ.filter (· ≤ j), ω.1.1.2 i =
        σ • √T • ∑ i ∈ Finset.univ.filter (· ≤ j), ω.1.1.2 i := by rw [smul_smul]
    rw [h2, smul_sub, e1, e2]
  have hgm : Measurable fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d => ω.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hbadPrf : P' {ω | ∃ j : Fin ℓ, σ * √T * (ℓ : ℝ) ^ ((1 : ℝ) / 4) * Real.log ℓ ^ 12 ≤
      ‖√T • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i ω.1.1.1) -
        σ • (fun s ω => √T • B' (T'⁻¹ * s) ω) ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T') ω‖} ≤
      ENNReal.ofReal (Real.exp (-(Real.log ℓ ^ 3))) := by
    have hpos : 0 < σ * √T := mul_pos hσ0 (Real.sqrt_pos.2 hT)
    have hset : {ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d | ∃ j : Fin ℓ,
        σ * √T * (ℓ : ℝ) ^ ((1 : ℝ) / 4) * Real.log ℓ ^ 12 ≤
        ‖√T • ∑ i ∈ Finset.univ.filter (· ≤ j), Y (V i ω.1.1.1) -
          σ • (fun s ω => √T • B' (T'⁻¹ * s) ω) ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T') ω‖} =
        (fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d => (Ξ ω.1.1.1, ω.1.1.2)) ⁻¹'
          {p : (Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ) |
          ∃ j : Fin ℓ, (ℓ : ℝ) ^ ((1 : ℝ) / 4) * Real.log ℓ ^ 12 ≤
            ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖} := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, hexpr, norm_smul, Real.norm_eq_abs,
        abs_of_pos hpos]
      refine exists_congr fun j => ?_
      rw [mul_assoc (σ * √T)]
      exact mul_le_mul_iff_of_pos_left hpos
    have hΦ' : Measurable fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d =>
        (Ξ ω.1.1.1, ω.1.1.2) :=
      (hΞm.comp hgm).prodMk (measurable_snd.comp (measurable_fst.comp measurable_fst))
    have hlawQ : P'.map (fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d =>
        (Ξ ω.1.1.1, ω.1.1.2)) = Q := by
      have : (fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d => (Ξ ω.1.1.1, ω.1.1.2)) =
          (fun p : G × (Fin ℓ → Fin d → ℝ) => (Ξ p.1, p.2)) ∘ (Prod.fst ∘ Prod.fst) := rfl
      rw [this, ← Measure.map_map hΦm (measurable_fst.comp measurable_fst), hfst2, hΓ2]
    rw [hset, ← Measure.map_apply hΦ' (measurableSet_x1Bad d ℓ _), hlawQ]
    calc Q _ = ENNReal.ofReal (Q.real _) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hQ3
  have hglaw : P'.map (fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d => ω.1.1.1) = PG := by
    have : (fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d => ω.1.1.1) = Prod.fst ∘ (Prod.fst ∘ Prod.fst) := rfl
    rw [this, ← Measure.map_map measurable_fst (measurable_fst.comp measurable_fst), hfst2, hΓ1]
  refine ⟨((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d, inferInstance, P', fun ω => ω.1.1.1,
    fun s ω => √T • B' (T'⁻¹ * s) ω, inferInstance, hgm, hglaw, hsc, ?_, hbadPrf, ?_⟩
  · refine le_trans (measure_mono ?_) (hbadPrf.trans (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_)))
    · rintro ω ⟨j, hj⟩
      refine ⟨j, le_trans ?_ hj⟩
      exact threshold_le hn4 ht1 ht2 hℓ1 hℓ2 hT hℓT hσ0 hσ2
    · linarith
  · intro Zs _ Z hZ
    have hm : Measurable fun e : G => (Z e, fun i => V i e) :=
      hZ.prodMk (measurable_pi_iff.2 hVm)
    have : (fun ω : ((G × (Fin ℓ → Fin d → ℝ)) × SX d) × SH d =>
        (Z (ω.1.1.1), fun i => V i (ω.1.1.1))) =
        (fun e : G => (Z e, fun i => V i e)) ∘ (fun ω => ω.1.1.1) := rfl
    rw [this, ← Measure.map_map hm hgm, hglaw]

end StrongApprox
end ElboimSly
