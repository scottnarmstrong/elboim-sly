/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitCoupleDrivenRegen
public import ElboimSly.Foundations.Cyclic.CycRegenLaw
public import ElboimSly.Foundations.SRW.StrongMarkovMain
public import Mathlib

/-!
# ES22 Lemma 2.1 (e): the law form

ES22 Lemma 2.1 (e). For the canonical SRW `X` of a Poisson point
process:

* `ae_shiftPath_mem_cycCF`: `P(X ∈ CF) = 1` and `P(X_{s₁} ∈ CF) = 1` for every deterministic `s₁`;
* `cyc_hit_couple_driven_regen_e`: for an admissible filtration `(F_t)`, a stopping time `T`,
  `A ∈ F_T` and a measurable `Γ`, with `W_T = W^{X_T}_reg`,
  `P(A ∩ {T < ∞} ∩ {W_T ∈ Γ}) = P(A ∩ {T < ∞}) · P(W^X_reg ∈ Γ)` (strong Markov property);
* `law_drivenRegenFrom`: `Law(W^X_reg)` is the law of the regenerated walk of regenerated cyclic walk
  (the constructions of the regenerated walk (iii));
* `ae_drivenRegenFrom_stopped`: almost surely on `{T < ∞}`,
  `W^X_reg(T + s) - W^X_reg(T) = W_T(s)` for `s ∈ [0, t_hit(T) - T]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

theorem cycCF_shiftPath_of_noJump {f : ℝ≥0 → Fin d → ℤ} {b : ℝ≥0} (hf : f ∈ CycCF b) (s₁ : ℝ≥0)
    (hno : ∀ k : ℕ, 1 ≤ k → s₁ + k * b ∉ CDisc f) : shiftPath f s₁ ∈ CycCF b := by
  obtain ⟨hdr, hi, -⟩ := hf
  refine ⟨isDrivingPath_shiftPath hdr _, fun s hs s' hs' k hk h => ?_, fun k hk hmem => ?_⟩
  · refine hi _ (mem_CDisc_of_shiftPath _ hs) _ (mem_CDisc_of_shiftPath _ hs') k hk ?_
    rw [h]; ring
  · exact hno k hk (mem_CDisc_of_shiftPath _ hmem)

/-- `P(X_{s₁} ∈ CF) = 1` for every deterministic `s₁`. -/
theorem ae_shiftPath_mem_cycCF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir d × ℝ)} (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (b : ℝ≥0) (hb : 0 < b) (s₁ : ℝ≥0) :
    ∀ᵐ ω ∂P, shiftPath (canonical d N ω) s₁ ∈ CycCF b := by
  have h2 : ∀ᵐ ω ∂P, ∀ k : ℕ, 1 ≤ k → ¬ IsJump (N ω) ((s₁ : ℝ) + (k : ℝ) * b) := by
    rw [ae_all_iff]
    intro k
    by_cases hk : 1 ≤ k
    · have hkpos : (0 : ℝ) < (s₁ : ℝ) + (k : ℝ) * b := by
        have : (0 : ℝ) < k := by exact_mod_cast hk
        have hbr : (0 : ℝ) < b := by exact_mod_cast hb
        have : (0 : ℝ) < (k : ℝ) * b := by positivity
        have h0 : (0 : ℝ) ≤ s₁ := s₁.2
        linarith
      filter_upwards [ae_not_isJump hN hkpos] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hk
  filter_upwards [ae_canonical_mem_cycCF hN b hb, h2] with ω hω1 hω2
  refine cycCF_shiftPath_of_noJump hω1 s₁ fun k hk hmem => hω2 k hk ?_
  have := isJump_of_mem_CDisc (N ω) hmem
  simpa using this

theorem isRegPath_thetaAt {Ω : Type*} {N₀ : Ω → Measure (Dir d × ℝ)} {T : Ω → WithTop ℝ≥0}
    {ω : Ω} (hω : T ω < ⊤) : IsRegPath (thetaAt T (canonical d N₀) ω) := by
  have hne : T ω ≠ ⊤ := ne_of_lt hω
  unfold thetaAt
  rw [ite_eq_right hne]
  exact isRegPath_shiftPath (walkPath_isRegPath (N₀ ω)) _

/-- **ES22 Lemma 2.1 (e)**, law form (strong Markov property): for the
canonical SRW `X` of a Poisson point process, an admissible filtration `(F_t)`, a stopping time
`T`, `A ∈ F_T` and a measurable `Γ`, with `W_T = W^{X_T}_reg`,
`P(A ∩ {T < ∞} ∩ {W_T ∈ Γ}) = P(A ∩ {T < ∞}) · P(W^X_reg ∈ Γ)`. -/
theorem cyc_hit_couple_driven_regen_e {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {N₀ : Ω → Measure (Dir d × ℝ)} (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) P)
    {b : ℝ≥0} (hb : 0 < b) {F : ℝ≥0 → MeasurableSpace Ω}
    (hF : IsAdmissible P (canonical d N₀) F) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime hF.filtration T) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) {Γ : Set (PathSpace d)} (hΓ : MeasurableSet Γ) :
    P (A ∩ {ω | T ω < ⊤} ∩ {ω | drivenRegenFrom b (thetaAt T (canonical d N₀) ω) ∈ Γ}) =
      P (A ∩ {ω | T ω < ⊤}) * P {ω | drivenRegenFrom b (canonical d N₀ ω) ∈ Γ} := by
  have hZ := canonical_isSRW hN₀
  have hΦ : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} => drivenRegenFrom b x.1 :=
    measurable_pi_iff.2 (measurable_drivenRegenFrom_subtype hb)
  obtain ⟨Γ'', hΓ'', hEq⟩ := (MeasurableSpace.measurableSet_comap).1 (hΦ hΓ)
  have key : ∀ y, IsRegPath y → (y ∈ Γ'' ↔ drivenRegenFrom b y ∈ Γ) := fun y hy => by
    have := Set.ext_iff.1 hEq ⟨y, hy⟩
    simpa using this
  have sm := hZ.strong_markov hF hT hA hΓ''
  rw [Measure.map_apply hZ.1 hΓ''] at sm
  have e1 : A ∩ {ω | T ω < ⊤} ∩ {ω | drivenRegenFrom b (thetaAt T (canonical d N₀) ω) ∈ Γ} =
      A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T (canonical d N₀) ω ∈ Γ''} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (key _ (isRegPath_thetaAt h2)).2 h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (key _ (isRegPath_thetaAt h2)).1 h3⟩
  have e2 : canonical d N₀ ⁻¹' Γ'' = {ω | drivenRegenFrom b (canonical d N₀ ω) ∈ Γ} := by
    ext ω
    exact key _ (walkPath_isRegPath (N₀ ω))
  rw [e1, sm, e2]

/-- `Law(W^X_reg)` is the law of the regenerated walk of regenerated cyclic walk (the constructions of the regenerated walk
(iii)). -/
theorem law_drivenRegenFrom {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {β : ℝ} [Fact (0 < β)] {Pe : Measure Ω} {Pd : Measure Ω'}
    {N : Ω → Measure (ℕ × RingSpace d β)} {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) :
    Pd.map (fun ω (t : ℝ≥0) => drivenRegenFrom β.toNNReal (canonical d N₀ ω) t) =
      Pe.map (fun ω (t : ℝ≥0) =>
        ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ)) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  rw [regen_law_env_cut hN hN₀]
  refine Measure.map_congr (Filter.Eventually.of_forall fun ω => ?_)
  funext t
  have h0 : canonical d N₀ ω 0 = 0 := by simp [canonical, walk_zero]
  exact (drivenRegenWalkCut_eq_drivenRegenFrom hb h0 t).symm

/-- **ES22 Lemma 2.1 (e)**, pathwise: almost surely on `{T < ∞}`,
`W^X_reg(T + s) - W^X_reg(T) = W_T(s)` for all `s ∈ [0, t_hit(T) - T]`. -/
theorem ae_drivenRegenFrom_stopped {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N₀ : Ω → Measure (Dir d × ℝ)} (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) P)
    {b : ℝ≥0} (hb : 0 < b) (T : Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂P, T ω < ⊤ → ∀ s : ℝ≥0,
      (((stopReal T ω + s : ℝ≥0)) : ℝ≥0∞) ≤ drivenThit b (canonical d N₀ ω) (stopReal T ω) →
        drivenRegenFrom b (canonical d N₀ ω) (stopReal T ω + s) -
            drivenRegenFrom b (canonical d N₀ ω) (stopReal T ω) =
          drivenRegenFrom b (thetaAt T (canonical d N₀) ω) s := by
  filter_upwards [ae_canonical_mem_cycCF hN₀ b hb] with ω hω hT s hs
  have hne : T ω ≠ ⊤ := ne_of_lt hT
  have hθ : thetaAt T (canonical d N₀) ω = shiftPath (canonical d N₀ ω) (stopReal T ω) := by
    unfold thetaAt
    rw [ite_eq_right hne]
    rfl
  rw [hθ]
  exact (cyc_hit_couple_driven_regen_b hb hω (stopReal T ω)).2.2 s hs

end ElboimSly.Cyclic

end
