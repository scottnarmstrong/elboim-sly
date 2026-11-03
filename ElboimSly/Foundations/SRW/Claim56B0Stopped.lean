/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56B0
public import ElboimSly.Foundations.SRW.Lemma82B
public import Mathlib

/-!
# Claim 5.6, event `𝓑_0`: regularity and the stopped-law form

ES22 Claim 5.6, last sentence (the event is regular), and its stopped-law
consequence used by ES22 Claim 5.6, Phase 0.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem IsRegSet.inter' {A B : Set (PathSpace d)} (hA : IsRegSet A) (hB : IsRegSet B) :
    IsRegSet (A ∩ B) := by
  obtain ⟨A', hAm, hA⟩ := hA
  obtain ⟨B', hBm, hB⟩ := hB
  exact ⟨A' ∩ B', hAm.inter hBm, fun γ hγ => by
    simp only [mem_inter_iff, hA γ hγ, hB γ hγ]⟩

/-- A "for all times in `[a, b]`" event with right-open failure set is regular. -/
theorem isRegSet_forall_pred (Pc : ℝ≥0 → (Fin d → ℤ) → Prop)
    (hP : ∀ y s, ¬ Pc s y → ∃ ε > 0, ∀ s', s ≤ s' → s' < s + ε → ¬ Pc s' y) (a b : ℝ≥0) :
    IsRegSet {γ : PathSpace d | ∀ s, a ≤ s → s ≤ b → Pc s (γ s)} := by
  classical
  have hmeas : ∀ (q : ℝ≥0) (Q : (Fin d → ℤ) → Prop), MeasurableSet {γ : PathSpace d | Q (γ q)} :=
    fun q Q => (measurable_pi_apply q) (MeasurableSet.of_discrete (s := {y | Q y}))
  by_cases hab : a ≤ b
  · refine ⟨{γ | Pc b (γ b)} ∩ ⋂ r : ℚ, ({γ | ¬ (a ≤ ratNN r ∧ ratNN r < b)} ∪
      {γ | Pc (ratNN r) (γ (ratNN r))}), ?_, fun γ hγ => ?_⟩
    · refine (hmeas b (Pc b)).inter (MeasurableSet.iInter fun r => ?_)
      exact (MeasurableSet.const _).union (hmeas _ _)
    · rw [mem_ofPred_eq, hγ.forall_Icc_iff Pc hP hab]
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_union]
      refine and_congr Iff.rfl (forall_congr' fun r => ?_)
      constructor
      · intro h
        by_cases h1 : a ≤ ratNN r ∧ ratNN r < b
        · exact Or.inr (h h1.1 h1.2)
        · exact Or.inl h1
      · rintro (h | h) h1 h2
        · exact absurd ⟨h1, h2⟩ h
        · exact h
  · refine ⟨univ, MeasurableSet.univ, fun γ _ => ?_⟩
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    intro s h1 h2
    exact absurd (h1.trans h2) hab

/-- The `𝓑_0` event. -/
def claim56B0Set (j m : ℕ) (t : ℝ) (u v : Fin d → ℤ) : Set (PathSpace d) :=
  {γ | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + γ s ∈ claimBox u j) ∧
    ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
      ‖(fun i => (((v + γ s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t}

/-- The `𝓑_0` event is a regular event (ES22 Claim 5.6, last sentence). -/
theorem isRegSet_claim56B0 {d : ℕ} (j m : ℕ) (t : ℝ) (u v : Fin d → ℤ) :
    IsRegSet {γ : PathSpace d |
      (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + γ s ∈ claimBox u j) ∧
      ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
        ‖(fun i => (((v + γ s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} := by
  by_cases hτ : 0 ≤ claimTau m t
  · set b : ℝ≥0 := (0.6 * claimTau m t).toNNReal with hbdef
    set a : ℝ≥0 := (0.5 * claimTau m t).toNNReal with hadef
    have hbc : (b : ℝ) = 0.6 * claimTau m t := Real.coe_toNNReal _ (by positivity)
    have hac : (a : ℝ) = 0.5 * claimTau m t := Real.coe_toNNReal _ (by positivity)
    have hb : ∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t ↔ s ≤ b := fun s => by
      rw [← hbc]; exact NNReal.coe_le_coe
    have ha : ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s ↔ a ≤ s := fun s => by
      rw [← hac]; exact NNReal.coe_le_coe
    have hP2 : ∀ (y : Fin d → ℤ) (s : ℝ≥0),
        ¬ (‖(fun i => (((v + y) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t) →
        ∃ ε > 0, ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε →
          ¬ (‖(fun i => (((v + y) i : ℤ) : ℝ)) - claimFv j u t v s'‖ ≤ claimR0 m t) := by
      intro y s hn
      rw [not_le] at hn
      have hc : Continuous fun x : ℝ =>
          ‖(fun i => (((v + y) i : ℤ) : ℝ)) - claimFv j u t v x‖ := by
        refine continuous_norm.comp (continuous_const.sub (continuous_pi fun i => ?_))
        unfold claimFv
        fun_prop
      have hev : ∀ᶠ x in 𝓝 (s : ℝ), claimR0 m t <
          ‖(fun i => (((v + y) i : ℤ) : ℝ)) - claimFv j u t v x‖ :=
        hc.continuousAt.eventually (lt_mem_nhds hn)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      refine ⟨ε.toNNReal, by simpa using hε, fun s' hs1 hs2 => ?_⟩
      rw [not_le]
      apply hball
      have h1 : (s : ℝ) ≤ s' := hs1
      have h2 : (s' : ℝ) < s + ε := by
        have := (NNReal.coe_lt_coe.2 hs2)
        simpa [Real.coe_toNNReal _ hε.le] using this
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    have h1 := isRegSet_forall_pred (d := d) (fun _ y => v + y ∈ claimBox u j)
      (fun y s hn => ⟨1, one_pos, fun s' _ _ => hn⟩) 0 b
    have h2 := isRegSet_forall_pred (d := d)
      (fun s y => ‖(fun i => (((v + y) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t)
      hP2 a b
    have := h1.inter' h2
    convert this using 1
    ext γ
    simp only [mem_ofPred_eq, mem_inter_iff, hb, ha]
    refine and_congr ⟨fun h s _ hs => h s hs, fun h s hs => h s zero_le hs⟩ ?_
    exact ⟨fun h s h1 h2 => h s h1 h2, fun h s h1 h2 => h s h1 h2⟩
  · have hneg : ∀ s : ℝ≥0, ¬ (s : ℝ) ≤ 0.6 * claimTau m t := fun s hs => by
      have := s.coe_nonneg
      apply hτ; linarith
    refine ⟨univ, MeasurableSet.univ, fun γ _ => ?_⟩
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨fun s hs => absurd hs (hneg s), fun s _ hs => absurd hs (hneg s)⟩

theorem claim56B0Set_stop {j m : ℕ} {t : ℝ} (u v : Fin d → ℤ) (R : ℝ≥0)
    (hR : 0.6 * claimTau m t ≤ R) (γ : PathSpace d) :
    γ ∈ claim56B0Set j m t u v ↔ (fun s => γ (min s R)) ∈ claim56B0Set j m t u v := by
  have key : ∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → min s R = s := fun s hs =>
    min_eq_left (by exact_mod_cast hs.trans hR)
  simp only [claim56B0Set, mem_ofPred_eq]
  refine and_congr ?_ ?_
  · refine forall_congr' fun s => imp_congr_right fun hs => ?_
    rw [key s hs]
  · refine forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun hs => ?_
    rw [key s hs]

/-- The directly consumable form of ES22 Claim 5.6: any process whose law stopped at
`R ≥ 0.6τ` is the SRW law stopped at `R`. -/
theorem claim56_B0_stopped {d j m : ℕ} {t : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → PathSpace d} (G : Claim56Geom d j t m) (u v : Fin d → ℤ)
    (hv : v ∈ claimBox u j) (R : ℝ≥0) (hR : 0.6 * claimTau m t ≤ R)
    (hZm : Measurable fun ω s => Z ω (min s R))
    (hZr : ∀ ω, IsRegularPath fun s => Z ω (min s R))
    (hlaw : P.map (fun ω s => Z ω (min s R)) =
      (srwP d).map (fun ω s => srwZ d ω (min s R))) :
    ENNReal.ofReal (cBox ^ (201 * d) / (2 * √(claimTau m t)) ^ (201 * d * CBox)) ≤
      P {ω | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + Z ω s ∈ claimBox u j) ∧
        ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
          ‖(fun i => (((v + Z ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} := by
  have hmain := claim56_B0 (srwZ_isSRW d) G u v hv
  obtain ⟨Γ', hΓm, hΓ⟩ := isRegSet_claim56B0 (d := d) j m t u v
  have hsm : Measurable fun ω s => srwZ d ω (min s R) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply (min s R)).comp (srwZ_isSRW d).1
  have hsr : ∀ ω, IsRegularPath fun s => srwZ d ω (min s R) :=
    fun ω => ((srwZ_isSRW d).2.1 ω).stop R
  have e1 : {ω | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + Z ω s ∈ claimBox u j) ∧
        ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
          ‖(fun i => (((v + Z ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} =
      (fun ω s => Z ω (min s R)) ⁻¹' Γ' := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← hΓ _ (hZr ω)]
    exact claim56B0Set_stop u v R hR (Z ω)
  have e2 : {ω | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + srwZ d ω s ∈ claimBox u j) ∧
        ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
          ‖(fun i => (((v + srwZ d ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} =
      (fun ω s => srwZ d ω (min s R)) ⁻¹' Γ' := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← hΓ _ (hsr ω)]
    exact claim56B0Set_stop u v R hR (srwZ d ω)
  rw [e2, ← Measure.map_apply hsm hΓm, ← hlaw] at hmain
  rw [e1]
  rwa [Measure.map_apply hZm hΓm] at hmain

end SRW
end ElboimSly
