/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.BlockSetup
public import ElboimSly.Paper.Step.TravelEngine
public import ElboimSly.Foundations.StrongApprox.Lemma76
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# One probability space for Lemma 7.6

ES22 Lemma 7.6, Steps 1-2; the coupling step of Lemma 7.6, re-tuned; how Lemma 7.6 applies crefcor:sa-lemma76.

`lemma76_space` applies the coupling step `sa_lemma76` to the independent driving windows of the
canonical SRW and the block functional `Y` (`segY`). It produces a probability space `(Ω'', P'')`
carrying an SRW `X''` (every path a driving path), a standard Brownian motion `B`, and the bound
`ℙ(∃ j, ‖∑_{i ≤ j} X_i - σ B((j+1)T)‖ ≥ t_n^{θ_H}/8) ≤ e^{-n³/7}` for the truncated block
endpoints `X_i = travelX` of the natural coupling of `X''`. Because the gluing property (c) of
`sa_lemma76` is used with `Z = X`, the written proof's `Γ(w)` (a driving path from independent segments) is not needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The block endpoints of the natural coupling are `√T` times the block functional of the
windows. -/
theorem sqrt_smul_segY {Ω : Type} {X : Ω → PathSpace d} (hXp : ∀ ω, X ω ∈ StepPath d)
    {T : ℝ≥0} (hT : 0 < T) (K : ℝ) (i : ℕ) (ω : Ω) :
    Real.sqrt T • segY β T K (winSeg hXp ((i : ℝ≥0) * T) T ω) = travelX β 0 T K X i ω := by
  have h := stepWj_eq (β := β) (hXp ω) 0 (fun _ => T) i
  have hP : stepPartial (fun _ : ℕ => T) i = (i : ℝ≥0) * T := stepPartial_const T i
  rw [hP, zero_add] at h
  rw [segY_eq]
  unfold blockY travelX
  have e : stepRegStopped β T (winSeg hXp ((i : ℝ≥0) * T) T ω).1 =
      stepWj β 0 (fun _ => T) (X ω) i := h.symm
  rw [e, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 (by exact_mod_cast hT)).ne', one_smul]

theorem lemma76_space (hd : 1 ≤ d) {n : ℕ} (hn : StrongApprox.nX d ≤ n) {tn : ℝ} (ht1 : (4 : ℝ) ^ n < tn)
    (ht2 : tn ≤ 4 ^ (n + 1)) {ℓ : ℕ} (hℓ1 : tn ^ ((79 : ℝ) / 200) / 2 ≤ ℓ)
    (hℓ2 : (ℓ : ℝ) ≤ 2 * tn ^ ((79 : ℝ) / 200)) {T : ℝ≥0} (hT : 0 < T)
    (hℓT : (ℓ : ℝ) * T ≤ 2 * tn) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hvar : ∫ w, (blockY T ((n : ℝ) ^ 2 * Real.sqrt T) w ⟨0, hd⟩) ^ 2 ∂ppLaw Pe N T = σ ^ 2) :
    ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (X'' : Ω'' → PathSpace d)
      (B : ℝ≥0 → Ω'' → Fin d → ℝ), IsProbabilityMeasure P'' ∧ IsSRW P'' X'' ∧
      (∀ ω, X'' ω ∈ StepPath d) ∧ IsStandardBrownianMotion d B P'' ∧
      P'' {ω | ∃ j : Fin ℓ, tn ^ ((41 : ℝ) / 100) / 8 ≤
        ‖∑ i ∈ Finset.univ.filter (· ≤ j), travelX β 0 T ((n : ℝ) ^ 2 * Real.sqrt T) X'' i ω -
          σ • B ((((j : ℕ) + 1 : ℕ) : ℝ≥0) * T) ω‖} ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3 / 7)) := by
  obtain ⟨Ω₀, _, P₀, N₀, hP₀, hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hX₀ : IsSRW P₀ (canonical d N₀) := canonical_isSRW hN₀
  have hXp : ∀ ω, canonical d N₀ ω ∈ StepPath d := fun ω => walkPath_isDriving (N₀ ω)
  have hprob : IsProbabilityMeasure P₀ := hX₀.isProbabilityMeasure
  set X₀ := canonical d N₀ with hX₀def
  set K : ℝ := (n : ℝ) ^ 2 * Real.sqrt T with hK
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTR
  set ν : Measure (RegSeg d) := P₀.map (winSeg hXp 0 T) with hν
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_winSeg hX₀ hXp 0 T).aemeasurable).2 inferInstance
  let D : Set (Fin d → ℝ) :=
    Set.range fun z : Fin d → ℤ => (Real.sqrt T)⁻¹ • (fun c => ((z c : ℤ) : ℝ))
  have hD : D.Countable := Set.countable_range _
  have hYD : ∀ w : RegSeg d, segY β T K w ∈ D := fun w => ⟨truncEnd T K (stepReg β w.1), rfl⟩
  have hnorm : ∀ w : RegSeg d, ‖segY β T K w‖ ≤ (n : ℝ) ^ 2 := fun w => by
    have h := norm_blockY_le (T := T) (K := K) (by positivity) (stepReg β w.1)
    refine h.trans (le_of_eq ?_)
    rw [hK]; field_simp
  have hlaw := map_segY hX₀ hXp hN T K 0
  have hsym : ∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) →
      (ν.map (segY β T K)).map (fun x => ε * x) = ν.map (segY β T K) := by
    intro ε hε
    rw [hν, hlaw]
    exact blockY_signs_law hN T K ε hε
  have hvar' : ∀ k, ∫ w, (segY β T K w k) ^ 2 ∂ν = σ ^ 2 := by
    intro k
    have hm : Measurable fun x : Fin d → ℝ => (x k) ^ 2 := (measurable_pi_apply k).pow_const 2
    have e1 : ∫ w, (segY β T K w k) ^ 2 ∂ν = ∫ x, (x k) ^ 2 ∂(ν.map (segY β T K)) := by
      rw [integral_map (measurable_segY T K).aemeasurable hm.aestronglyMeasurable]
    rw [e1, hν, hlaw, integral_map (measurable_blockY T K).aemeasurable hm.aestronglyMeasurable,
      integral_blockY_sq_eq hN T K k ⟨0, hd⟩]
    exact hvar
  have hVm : ∀ i : Fin ℓ, Measurable (winSeg hXp (((i : ℕ) : ℝ≥0) * T) T) := fun i =>
    measurable_winSeg hX₀ hXp _ T
  have hVlaw : ∀ i : Fin ℓ, P₀.map (winSeg hXp (((i : ℕ) : ℝ≥0) * T) T) = ν := fun i =>
    map_winSeg hX₀ hXp _ T
  obtain ⟨Ω'', inst'', P'', g, B, hP'', hg, hmapg, hB, hE3, -, hZ⟩ := StrongApprox.sa_lemma76 d hd
    hn ht1 ht2 hℓ1 hℓ2 (T := (T : ℝ)) hTR (by exact_mod_cast hℓT) hσ1 hσ2 ν (segY β T K)
    (measurable_segY T K) D hD hYD hnorm hsym hvar' P₀
    (fun i : Fin ℓ => winSeg hXp (((i : ℕ) : ℝ≥0) * T) T) hVm (iIndepFun_winSeg hX₀ hXp T ℓ) hVlaw
  have hfst := hZ X₀ hX₀.1
  have hlaw'' : P''.map (fun ω => X₀ (g ω)) = P₀.map X₀ := by
    have h1 := congrArg (Measure.map Prod.fst) hfst
    rw [Measure.map_map measurable_fst, Measure.map_map measurable_fst] at h1
    · exact h1
    · exact hX₀.1.prodMk (measurable_pi_iff.2 hVm)
    · exact (hX₀.1.comp hg).prodMk (measurable_pi_iff.2 fun i => hVm i |>.comp hg)
  refine ⟨Ω'', inst'', P'', fun ω => X₀ (g ω), B, hP'', ⟨hX₀.1.comp hg,
    fun ω => isRegularPath_canonical N₀ (g ω), Ω₀, inferInstance, P₀, N₀, hN₀, hlaw''⟩,
    fun ω => hXp (g ω), hB, ?_⟩
  refine le_trans (le_of_eq (congrArg P'' ?_)) hE3
  ext ω
  simp only [Set.mem_ofPred_eq, Real.toNNReal_coe, Finset.smul_sum]
  refine exists_congr fun j => ?_
  have : ∑ i ∈ Finset.univ.filter (· ≤ j), Real.sqrt (T : ℝ) • segY β T K
      (winSeg hXp (((i : ℕ) : ℝ≥0) * T) T (g ω)) =
      ∑ i ∈ Finset.univ.filter (· ≤ j), travelX β 0 T K (fun ω => X₀ (g ω)) i ω :=
    Finset.sum_congr rfl fun i _ => sqrt_smul_segY (X := fun ω => X₀ (g ω)) (fun ω => hXp (g ω)) hT K i ω
  rw [this]

end ElboimSly.Paper.Step
