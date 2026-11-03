/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Freeze
public import ElboimSly.Paper.Escape.C56Claim
public import Mathlib

/-!
# Lemma 5.5, Step 1: the probability bound for the frozen walk

ES22 Lemma 5.5, Step 1 ("By ES22 Claim 5.6 and freezing, `P(E₅₆ | ℱ_{S₃}) ≥ n^{-γ+1}`").

`es55_prob`: for the regenerated walk of the independent Poisson process `N''`, the rational form
of `E₅₆` (and no jump at `t`) has probability at least `n^{-γ+1}`: by `es5_6` for `N`, the law of the
regenerated walk (`N` and `N''` have the same law) and the measurability of the rational form.
The null event "the regenerated walk jumps at the fixed time `t`" is a hypothesis `hjump`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.SRW ElboimSly.Brownian

variable {k : ℕ}

/-- The law of the (good version of the) regenerated walk depends only on the law of `N`. -/
theorem escW_law {β : ℝ} [Fact (0 < β)] {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pr : Measure Ω} {Pr' : Measure Ω'} {N : Ω → Measure (CycS ℕ (k + 2) β)}
    {N'' : Ω' → Measure (CycS ℕ (k + 2) β)}
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    (hN'' : IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr') :
    Pr.map (escW N) = Pr'.map (escW N'') := by
  have hG : Measurable (avoidPath (cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν))) :=
    measurable_avoidPath_cycNgood measurable_id
  have e1 : escW N = avoidPath (cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν)) ∘ N := rfl
  have e2 : escW N'' =
      avoidPath (cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν)) ∘ N'' := rfl
  rw [e1, e2, ← Measure.map_map hG hN.measurable, ← Measure.map_map hG hN''.measurable,
    hN.map_eq_map hN'']

/-- The rational form of `E₅₆` has the same probability for `N` and `N''`, and for the regenerated
walk of `N''`. -/
theorem prob_rat_regenW {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N N'' : Ω → Measure (CycS ℕ (k + 2) β)}
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    (hN'' : IsPoissonPointProcess N''
      ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr)
    (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ) :
    Pr {ω | EscRat β j u v z t (escW N ω)} =
      Pr {ω | EscRat β j u v z t (regenW N'' ω)} := by
  have hX : MeasurableSet {y : ℝ≥0 → Fin (k + 2) → ℤ | EscRat β j u v z t y} :=
    measurableSet_escRat (X := ℝ≥0 → Fin (k + 2) → ℤ) β j u (fun _ => v) (fun _ => z)
      (fun _ => t) (fun y => y) measurable_const measurable_const measurable_const measurable_id
  have hN2 : IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr := hN''
  have hm1 : Measurable (escW N) := measurable_avoidPath_cycNgood hN.measurable
  have hm2 : Measurable (escW N'') := measurable_avoidPath_cycNgood hN2.measurable
  have e1 : Pr {ω | EscRat β j u v z t (escW N ω)} = (Pr.map (escW N)) {y | EscRat β j u v z t y} :=
    (Measure.map_apply hm1 hX).symm
  have e2 : Pr {ω | EscRat β j u v z t (escW N'' ω)} =
      (Pr.map (escW N'')) {y | EscRat β j u v z t y} := (Measure.map_apply hm2 hX).symm
  rw [e1, escW_law hN hN2, ← e2]
  refine measure_congr ?_
  filter_upwards [ae_cycNgood_eq hN2] with ω hω
  have : escW N'' ω = regenW N'' ω := by
    funext s
    simp only [escW, avoidPath, avoidWalk, avoidEnv_eq_cycSlice, hω, regenW]
  simp only [this]

/-- **The probability bound of Step 1.**  By ES22 Claim 5.6, the rational form of `E₅₆` for the
regenerated walk of `N''` (without a jump at `t`) has probability at least `n^{-γ+1}`. -/
theorem es55_prob (hd : 5 ≤ k + 2) (n₀ : ℕ) :
    ∃ β56 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), β56 ≤ β →
      ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
        {N N' : Ω → Measure (CycS ℕ (k + 2) β)} (_S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N')
        {N'' : Ω → Measure (ℕ × RingSpace (k + 2) β)}
        (_hN'' : IsPoissonPointProcess N''
          ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr)
        {γ : ℝ}, max (gamma1 (k + 2)) (escGamma56 (k + 2)) ≤ γ →
        ∀ (u v z : Fin (k + 2) → ℤ) (t : ℝ), v ∈ escBoundary (escJ n) u →
          v ∈ escBlockMinus (escJ n) u → z ∈ escFace (escJ n) u →
          (4 : ℝ) ^ (escJ n - 1) ≤ t → t ≤ 4 ^ escJ n →
          Pr {ω' | ¬ noJumpRat (regenW N'' ω') t} = 0 →
          ENNReal.ofReal ((n : ℝ) ^ (-γ + 1)) ≤
            Pr {ω' | EscRat β (escJ n) u v z t (regenW N'' ω') ∧ noJumpRat (regenW N'' ω') t} := by
  obtain ⟨β56, H⟩ := es5_6 hd n₀
  refine ⟨β56, fun β _ n t₀ hβ Ω 𝒢₀ mΩ Pr N N' S N'' hN'' γ hγ u v z t hv hvm hz ht1 ht2
    hjump => ?_⟩
  have h1 := H β n t₀ hβ 𝒢₀ S hγ u v z t hv hvm hz ht1 ht2
  have ht0 : 0 ≤ t := le_trans (by positivity) ht1
  have hβ0 : 0 ≤ β := (Fact.out : 0 < β).le
  have eqset : {ω | Esc56Event β (escJ n) u v z t (escYv N v ω)} =
      {ω | EscRat β (escJ n) u v z t (escW N ω)} := by
    ext ω
    exact esc56_iff_rat hβ0 ht0 (isRegPath_escW N ω).rc
  rw [eqset, prob_rat_regenW S.space.ppp hN''] at h1
  refine h1.trans (measure_mono_ae ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hjump] with ω hω hmem
  exact ⟨hmem, not_not.1 hω⟩

end ElboimSly.Paper.Escape
