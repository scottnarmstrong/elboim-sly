/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.DifferenceProc
public import ElboimSly.Foundations.SRW.CountableReduction
public import Mathlib

/-!
# Difference of independent walks

Difference of independent walks.

Let `N, N'` be Poisson point processes with intensity `clockIntensity (Dir d)` on the same
probability space, with `IndepFun N N' P`, and `X = canonical d N`, `X' = canonical d N'`.  Then
`Z = X - X'` has regular paths and `Law(Z) = Law(X(2 ·))` (`difference_law`).  Consequently the
probabilities that `x + Z` avoids a set `K` forever and that `x + X` avoids it forever agree
(`difference_avoid`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {N N' : Ω → Measure (Dir d × ℝ)}
  {P : Measure Ω}

theorem IsRegularPath.sub {γ γ' : PathSpace d} (h : IsRegularPath γ) (h' : IsRegularPath γ') :
    IsRegularPath fun s => γ s - γ' s := by
  intro t
  obtain ⟨δ, hδ, hc⟩ := h t
  obtain ⟨δ', hδ', hc'⟩ := h' t
  refine ⟨min δ δ', lt_min hδ hδ', fun s hs1 hs2 => ?_⟩
  show γ s - γ' s = γ t - γ' t
  rw [hc s hs1 (hs2.trans_le (by gcongr; exact min_le_left _ _)),
    hc' s hs1 (hs2.trans_le (by gcongr; exact min_le_right _ _))]

theorem IsRegularPath.comp_two {γ : PathSpace d} (h : IsRegularPath γ) :
    IsRegularPath fun s => γ (2 * s) := by
  intro t
  obtain ⟨δ, hδ, hc⟩ := h (2 * t)
  refine ⟨δ / 2, by positivity, fun s hs1 hs2 => ?_⟩
  refine hc (2 * s) (by gcongr) ?_
  have : 2 * s < 2 * (t + δ / 2) := by gcongr
  calc 2 * s < 2 * (t + δ / 2) := this
    _ = 2 * t + δ := by ring

theorem psi_scale_apply (ν : Measure (Dir d × ℝ)) (s : ℝ≥0) :
    psi d (ν.map (Prod.map id (fun x : ℝ => x * 2⁻¹))) s = psi d ν (2 * s) := by
  simp only [psi]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hm : Measurable (Prod.map (id : Dir d → Dir d) (fun x : ℝ => x * 2⁻¹)) :=
    measurable_id.prodMap (measurable_id.mul_const _)
  rw [Measure.map_apply hm ((measurableSet_singleton v).prod measurableSet_Ioc)]
  congr 4
  ext ⟨w, x⟩
  simp only [Prod.map, mem_preimage, mem_prod, mem_singleton_iff, mem_Ioc, id, NNReal.coe_mul,
    NNReal.coe_ofNat]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩

/-- Difference of independent walks: `Z = X - X'` has regular paths and the law of `X(2 ·)`. -/
theorem difference_law (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (hN' : IsPoissonPointProcess N' (clockIntensity (Dir d)) P) (hind : IndepFun N N' P) :
    (∀ ω, IsRegularPath fun s => canonical d N ω s - canonical d N' ω s) ∧
    P.map (fun ω s => canonical d N ω s - canonical d N' ω s) =
      P.map (fun ω s => canonical d N ω (2 * s)) := by
  refine ⟨fun ω => (isRegularPath_canonical N ω).sub (isRegularPath_canonical N' ω), ?_⟩
  have hsum := isPPP_sum hN hN' hind
  have hsc := isPPP_scale hN
  have hU := hsc.map_eq_map hsum
  have h1 : (fun ω s => canonical d N ω s - canonical d N' ω s) =ᵐ[P]
      fun ω => psi d (N ω + (N' ω).map (Prod.map (negPerm d) id)) := by
    filter_upwards [ae_good hN, ae_good hN', ae_good (perm_ppp hN' (negPerm d))] with ω a b c
    funext s
    rw [psi_add a c, psi_map_negPerm, psi_of_good a, psi_of_good b]
    simp [canonical, can, sub_eq_add_neg]
  have h2 : (fun ω s => canonical d N ω (2 * s)) =ᵐ[P]
      fun ω => psi d ((N ω).map (Prod.map id (fun x : ℝ => x * 2⁻¹))) := by
    filter_upwards [ae_good hN] with ω a
    funext s
    rw [psi_scale_apply, psi_of_good a]
    rfl
  rw [Measure.map_congr h1, Measure.map_congr h2,
    IsPoissonPointProcess.map_comp (P := P) hsum.measurable (measurable_psi d),
    IsPoissonPointProcess.map_comp (P := P) hsc.measurable (measurable_psi d), hU]

/-- Difference of independent walks, consequence: for every `x` and `K`, the probabilities that
`x + Z` and `x + X` avoid `K` forever agree. -/
theorem difference_avoid (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (hN' : IsPoissonPointProcess N' (clockIntensity (Dir d)) P) (hind : IndepFun N N' P)
    (x : Fin d → ℤ) (K : Set (Fin d → ℤ)) :
    P {ω | ∀ s, x + (canonical d N ω s - canonical d N' ω s) ∉ K} =
      P {ω | ∀ s, x + canonical d N ω s ∉ K} := by
  obtain ⟨hreg, hlaw⟩ := difference_law hN hN' hind
  set Γ : Set (PathSpace d) := ⋃ r : ℚ, {γ | x + γ (ratNN r) ∈ K} with hΓ
  have hΓm : MeasurableSet Γ := MeasurableSet.iUnion fun r => by
    have hev : Measurable fun γ : PathSpace d => γ (ratNN r) := measurable_pi_apply (ratNN r)
    have := hev
      (MeasurableSet.of_discrete (s := {y : Fin d → ℤ | x + y ∈ K}))
    exact this
  have key : ∀ γ : PathSpace d, IsRegularPath γ → ((∀ s, x + γ s ∉ K) ↔ γ ∈ Γᶜ) := by
    intro γ hγ
    have := hγ.exists_Ici_iff {y | x + y ∈ K} 0
    simp only [zero_le, true_and, mem_ofPred_eq] at this
    simp only [hΓ, mem_compl_iff, mem_iUnion, mem_ofPred_eq]
    rw [← this]
    push Not
    exact ⟨fun h s => h s, fun h s => h s⟩
  have hXreg := fun ω => isRegularPath_canonical N ω
  have hZm : Measurable fun ω s => canonical d N ω s - canonical d N' ω s :=
    measurable_pi_iff.2 fun s => ((measurable_pi_apply s).comp (measurable_canonical hN.measurable)).sub
      ((measurable_pi_apply s).comp (measurable_canonical hN'.measurable))
  have hXm : Measurable fun ω s => canonical d N ω (2 * s) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply (2 * s)).comp
      (measurable_canonical hN.measurable)
  have e1 : {ω | ∀ s, x + (canonical d N ω s - canonical d N' ω s) ∉ K} =
      (fun ω s => canonical d N ω s - canonical d N' ω s) ⁻¹' Γᶜ := by
    ext ω; exact key _ (hreg ω)
  have e2 : {ω | ∀ s, x + canonical d N ω s ∉ K} =
      (fun ω s => canonical d N ω (2 * s)) ⁻¹' Γᶜ := by
    ext ω
    rw [mem_preimage, ← key _ (hXreg ω).comp_two]
    simp only [mem_ofPred_eq]
    constructor
    · intro h s; exact h _
    · intro h s
      have := h (s / 2)
      rwa [mul_div_cancel₀ _ (two_ne_zero)] at this
  rw [e1, e2, ← Measure.map_apply hZm hΓm.compl, ← Measure.map_apply hXm hΓm.compl, hlaw]

end SRW
end ElboimSly
