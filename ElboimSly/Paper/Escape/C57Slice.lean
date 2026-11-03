/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Prob
public import Mathlib

/-!
# Measurability of the events of ES22 Claim 5.7 and the probability of a slice

ES22 Claim 5.7 ("By freezing and ES22 Claim 4.2").

* `measurableSet_Cyl57`, `measurableSet_CylFar`, `measurableSet_CylAv`;
* `setS`: the event `E₅₇ ∩ E_far ∩ E_av(A)` as a measurable subset of
  `(ℤ^d → Prop) × path space` (the first factor encodes the `ℱ_{S₂}`-measurable set `A`);
* `slice_prob`: for each admissible set `A`, the slice of `setS` at `A` has probability at least
  `c₅₇ - e^{-n_T²} - ε_far - ε_av`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

set_option linter.unusedSectionVars false

section meas

variable {k : ℕ}

theorem measurableSet_Cyl57 (n j : ℕ) (u : EscV k) (i : ℕ) (S : ℝ≥0) :
    MeasurableSet (Cyl57 n j u i S) := by
  have e : Cyl57 n j u i S = (⋂ q ∈ qSet 0 S, {z : ℝ≥0 → EscV k |
      escPoint n j u i + z q ∈ escBigBox j u}) ∩ {z | escPoint n j u i + z S ∉ escQ j u} := by
    ext z; simp [Cyl57]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.biInter (qSet_countable 0 S) fun q _ => ?_) ?_
  · exact (MeasurableSet.of_discrete (s := {v : EscV k | escPoint n j u i + v ∈ escBigBox j u})).preimage
      (measurable_pi_apply _)
  · exact (MeasurableSet.of_discrete (s := {v : EscV k | escPoint n j u i + v ∉ escQ j u})).preimage
      (measurable_pi_apply _)

theorem farTest_countable (β : ℝ) (n : ℕ) (a : ℝ) :
    {τ : ℝ≥0 | a ≤ τ ∧ (τ : ℝ) ≤ 4 ^ n ∧
      (τ ∈ qSet a.toNNReal ((4 : ℝ≥0) ^ n) ∨ ∃ m : ℕ, τ = m * β.toNNReal)}.Countable := by
  refine Set.Countable.mono ?_ ((qSet_countable a.toNNReal ((4 : ℝ≥0) ^ n)).union
    (Set.countable_range (fun m : ℕ => (m : ℝ≥0) * β.toNNReal)))
  rintro τ ⟨-, -, h | ⟨m, rfl⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, rfl⟩

theorem measurableSet_CylFar (β : ℝ) (n : ℕ) (a L : ℝ) : MeasurableSet (CylFar (k := k) β n a L) := by
  have e : CylFar (k := k) β n a L = ⋂ τ ∈ {τ : ℝ≥0 | a ≤ τ ∧ (τ : ℝ) ≤ 4 ^ n ∧
      (τ ∈ qSet a.toNNReal ((4 : ℝ≥0) ^ n) ∨ ∃ m : ℕ, τ = m * β.toNNReal)},
      {z : ℝ≥0 → EscV k | L ≤ ‖z τ‖} := by
    ext z
    simp only [CylFar, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h τ hτ; exact h τ hτ.1 hτ.2.1 hτ.2.2
    · intro h τ h1 h2 h3; exact h τ ⟨h1, h2, h3⟩
  rw [e]
  refine MeasurableSet.biInter (farTest_countable β n a) fun τ _ => ?_
  exact (MeasurableSet.of_discrete (s := {v : EscV k | L ≤ ‖v‖})).preimage (measurable_pi_apply _)

theorem measurableSet_CylAv (n : ℕ) (p : EscV k) (A : Set (EscV k)) :
    MeasurableSet (CylAv n p A) := by
  have e : CylAv n p A = ⋂ τ ∈ qSet 0 ((4 : ℝ≥0) ^ n), {z : ℝ≥0 → EscV k | p + z τ ∉ A} := by
    ext z; simp [CylAv]
  rw [e]
  refine MeasurableSet.biInter (qSet_countable 0 _) fun τ _ => ?_
  exact (MeasurableSet.of_discrete (s := {v : EscV k | p + v ∉ A})).preimage (measurable_pi_apply _)

/-- The event `E₅₇ ∩ E_far ∩ E_av`, with the avoided set given as a predicate `a`. -/
def setS (β : ℝ) (n j : ℕ) (u : EscV k) (i : ℕ) (S : ℝ≥0) (t7 L7 : ℝ) :
    Set ((EscV k → Prop) × (ℝ≥0 → EscV k)) :=
  {x | x.2 ∈ Cyl57 n j u i S ∧ x.2 ∈ CylFar β n t7 (L7 + 1) ∧
    ∀ τ ∈ qSet 0 ((4 : ℝ≥0) ^ n), ¬ x.1 (escPoint n j u i + x.2 τ)}

theorem measurableSet_setS (β : ℝ) (n j : ℕ) (u : EscV k) (i : ℕ) (S : ℝ≥0) (t7 L7 : ℝ) :
    MeasurableSet (setS β n j u i S t7 L7) := by
  have e : setS β n j u i S t7 L7 =
      (Prod.snd ⁻¹' (Cyl57 n j u i S ∩ CylFar β n t7 (L7 + 1))) ∩
      ⋂ τ ∈ qSet 0 ((4 : ℝ≥0) ^ n), {x : (EscV k → Prop) × (ℝ≥0 → EscV k) |
        ¬ x.1 (escPoint n j u i + x.2 τ)} := by
    ext x; simp [setS, and_assoc]
  rw [e]
  refine MeasurableSet.inter (measurable_snd ((measurableSet_Cyl57 n j u i S).inter
    (measurableSet_CylFar β n t7 _))) (MeasurableSet.biInter (qSet_countable 0 _) fun τ _ => ?_)
  have hF : Measurable fun x : (EscV k → Prop) × EscV k => x.1 (escPoint n j u i + x.2) :=
    measurable_from_prod_countable_left fun v =>
      (measurable_pi_apply (escPoint n j u i + v) : Measurable fun a : EscV k → Prop =>
        a (escPoint n j u i + v))
  have hG : Measurable fun x : (EscV k → Prop) × (ℝ≥0 → EscV k) => (x.1, x.2 τ) :=
    measurable_fst.prodMk ((measurable_pi_apply τ).comp measurable_snd)
  have := (hF.comp hG) (MeasurableSet.of_discrete (s := {P : Prop | ¬ P}))
  exact this

end meas

section slice

theorem compl_le_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {E : Set α} (hE : NullMeasurableSet E μ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ENNReal.ofReal (1 - ε) ≤ μ E) : μ Eᶜ ≤ ENNReal.ofReal ε := by
  rw [prob_compl_eq_one_sub₀ hE]
  have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε := by
    by_cases hε1 : ε ≤ 1
    · rw [← ENNReal.ofReal_add (by linarith) hε]
      simp
    · push Not at hε1
      refine le_trans ?_ le_add_self
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hε1.le
  calc 1 - μ E ≤ 1 - ENNReal.ofReal (1 - ε) := tsub_le_tsub le_rfl h
    _ ≤ ENNReal.ofReal ε := tsub_le_iff_left.2 this

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N N'' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem nullMeasurableSet_regenW (hN'' : IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr)
    {C : Set (ℝ≥0 → EscV k)} (hC : MeasurableSet C) :
    NullMeasurableSet {ω | regenW N'' ω ∈ C} Pr := by
  have hX : MeasurableSet {ω | avoidPath (cycNgood N'') ω ∈ C} :=
    (measurable_avoidPath_cycNgood hN''.measurable) hC
  refine hX.nullMeasurableSet.congr ?_
  filter_upwards [ae_regenW_eq hN''] with ω h
  simp only [h]

/-- **The probability of a slice.** -/
theorem slice_prob (hd : 5 ≤ k + 2) :
    ∃ C₄₃ C₄₂ : ℝ, 0 < C₄₃ ∧ 0 < C₄₂ ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
        {N N'' : Ω → Measure (CycS ℕ (k + 2) β)},
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr →
        ∀ (u : EscV k) {i : ℕ}, 1 ≤ i → i ≤ escIstar n (escJ n) → 2 ≤ n →
        (n : ℝ) ^ 20 ≤ 2 ^ escJ n → 3 ≤ escJ n →
        16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n →
        (4 : ℝ) ^ n₀ < 4 ^ escJ n → (4 : ℝ) ^ escJ n ≤ 4 ^ n →
        ((4 : ℝ) ^ escJ n) ^ indThetaH < (2 : ℝ) ^ escJ n / 64 →
        ∀ {S : ℝ≥0}, (S : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2 / 4 →
        ∀ {t7 L7 : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ t7 → t7 ≤ (4 : ℝ) ^ n → t7 ^ indThetaH ≤ L7 + 1 →
        L7 + 1 ≤ t7 ^ (1 / 2 : ℝ) → (4 : ℝ) ^ (n₀ + 1) ≤ L7 → L7 ≤ (4 : ℝ) ^ n →
        0 ≤ C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2) →
        0 ≤ C₄₂ * L7 ^ (-(1 : ℝ) / 30) →
        ∀ (A : Set (EscV k)), (∀ y ∈ A, L7 ≤ ‖y - escPoint n (escJ n) u i‖) →
        (∀ r : ℝ, L7 ≤ r → (({y | y ∈ A ∧ ‖y - escPoint n (escJ n) u i‖ ≤ r} : Set (EscV k)).ncard
          : ℝ) ≤ r ^ (8 / 3 : ℝ)) →
        ENNReal.ofReal (c57 (k + 2)) -
          ENNReal.ofReal (Real.exp (-((avoidLevel ((4 : ℝ) ^ escJ n) : ℕ) : ℝ) ^ 2)) -
          ENNReal.ofReal (C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2)) -
          ENNReal.ofReal (C₄₂ * L7 ^ (-(1 : ℝ) / 30)) ≤
        Pr {ω | ((fun y => y ∈ A), regenW N'' ω) ∈ setS β n (escJ n) u i S t7 L7} := by
  obtain ⟨C₄₃, hC43, Hfar⟩ := prob_far (k := k) hd
  obtain ⟨C₄₂, hC42, Hav⟩ := prob_av (k := k) hd
  refine ⟨C₄₃, C₄₂, hC43, hC42, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N N'' hN hN'' u i hi1 hiI hn hj1 hj3 hIlam hT1 hT2 hε S hS t7 L7
    ht71 ht72 ht7L hLt hL71 hL72 hεf hεa A hA1 hA2
  have := hN.isProbabilityMeasure
  have h57 := prob_57 hp hN'' u hi1 hiI hn hj1 hj3 hIlam hT1 hT2 hε hS
  have hfar := Hfar β n₀ n t₀ hp hN hN'' ht71 ht72 ht7L hLt
  have hav := Hav β n₀ n t₀ hp hN hN'' hL71 hL72 (escPoint n (escJ n) u i) hA1 hA2
  set E57 := {ω | regenW N'' ω ∈ Cyl57 n (escJ n) u i S} with hE57
  set Ef := {ω | regenW N'' ω ∈ CylFar β n t7 (L7 + 1)} with hEf
  set Ea := {ω | regenW N'' ω ∈ CylAv n (escPoint n (escJ n) u i) A} with hEa
  have hfarc : Pr Efᶜ ≤ ENNReal.ofReal (C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2)) := by
    refine compl_le_ofReal (nullMeasurableSet_regenW hN'' (measurableSet_CylFar _ _ _ _)) hεf ?_
    have := hfar
    rwa [show (1 : ℝ) - C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2) =
      1 - C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2) from rfl] at this
  have havc : Pr Eaᶜ ≤ ENNReal.ofReal (C₄₂ * L7 ^ (-(1 : ℝ) / 30)) :=
    compl_le_ofReal (nullMeasurableSet_regenW hN'' (measurableSet_CylAv _ _ _)) hεa hav
  have hsub : E57 ⊆ {ω | ((fun y => y ∈ A), regenW N'' ω) ∈ setS β n (escJ n) u i S t7 L7} ∪ Efᶜ ∪ Eaᶜ := by
    intro ω hω
    by_cases hf : ω ∈ Ef
    · by_cases ha : ω ∈ Ea
      · left; left
        exact ⟨hω, hf, fun τ hτ => by simpa using ha τ hτ⟩
      · right; exact ha
    · left; right; exact hf
  have h1 : Pr E57 ≤ Pr {ω | ((fun y => y ∈ A), regenW N'' ω) ∈ setS β n (escJ n) u i S t7 L7} +
      Pr Efᶜ + Pr Eaᶜ :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))
  calc _ ≤ Pr E57 - Pr Efᶜ - Pr Eaᶜ :=
        tsub_le_tsub (tsub_le_tsub h57 hfarc) havc
    _ ≤ _ := by
        rw [tsub_le_iff_right, tsub_le_iff_right]
        calc Pr E57 ≤ _ := h1
          _ = _ := by ring

end slice

end ElboimSly.Paper.Escape
