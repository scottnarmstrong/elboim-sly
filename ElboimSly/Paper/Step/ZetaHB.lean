/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaCount
public import ElboimSly.Paper.Step.ZetaSRW
public import ElboimSly.Paper.Step.ZetaGap
public import Mathlib

/-!
# The conditional success probability of one excursion

ES22 Lemma 7.1, Step 4: for `H ∈ 𝒢_{ζ_{i+1}}` with `H ⊆ {ζ_{i+1} < ∞}`,
`P(H ∩ {ζ'_{i+1} ≥ ζ_{i+1} + 4ⁿ}) ≥ ½ P(H)`, from ES22 Lemma 4.1 applied to `W` (offset
`a`, `S = ζ_{i+1}`) and to `Z₂` (offset `a + s₀`, `S = ζ_{i+1} - s₀`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

/-- Lemma 4.1 at stopping times of the driving filtration for all offsets, in the form of
`step_avoid_stopping` (with the failure constant `c`). -/
def AvoidAll (β : ℝ) (n : ℕ) (hF : IsAdmissible P Y F) (c : ℝ) : Prop :=
  ∀ (a : ℝ≥0) {S : Ω → WithTop ℝ≥0} (hS : IsStoppingTime (stepShiftFilt hF a) S) {G : Set Ω},
    MeasurableSet[hS.measurableSpace] G →
    (∀ ω ∈ G, ∃ t : ℝ≥0, S ω = t ∧
      (t : ℝ) ∈ stepRelaxedSet β (stepWr β a Y ω) (stepAr β a Y ω)) →
    ENNReal.ofReal (1 - c) * P G ≤
      P (G ∩ {ω | ∀ t : ℝ≥0, S ω = t →
        ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤
          stepThit β (stepWr β a Y ω) (stepAr β a Y ω) (t : ℝ)})

theorem toReal_avoid {G E : Set Ω} {c : ℝ} (hc : c ≤ 1) [IsProbabilityMeasure P]
    (h : ENNReal.ofReal (1 - c) * P G ≤ P (G ∩ E)) :
    (1 - c) * P.real G ≤ P.real (G ∩ E) := by
  have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h2
  exact h2

theorem zeta_hB {β : ℝ} [Fact (0 < β)] (hd : 1 ≤ d) (hβ : 1 < β) [IsProbabilityMeasure P]
    (hYp : ∀ ω, Y ω ∈ StepPath d) (hF : IsAdmissible P Y F) (a s₀ : ℝ≥0) {n : ℕ} {c : ℝ}
    (hc : c ≤ 1 / 4) (hav : AvoidAll β n hF c) (i : ℕ) {H : Set Ω}
    (hH : MeasurableSet[(isStoppingTime_zetaN hd hβ (zetaProc_one (β := β) hF hYp a)
      (zetaProc_two (β := β) hF hYp a s₀) s₀ i).measurableSpace] H)
    (hHfin : ∀ ω ∈ H, zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i ω ≠ ⊤) :
    (1 / 2) * P.real H ≤ P.real (H ∩ {ω | zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y)
      (za2 β a s₀ Y) s₀ i ω + ((((4 : ℝ) ^ n).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤
        zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (i + 1) ω}) := by
  have hz1 := zetaProc_one (β := β) hF hYp a
  have hz2 := zetaProc_two (β := β) hF hYp a s₀
  set ζ := zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ i with hζ
  have hsζ : IsStoppingTime (stepShiftFilt hF a) ζ := isStoppingTime_zetaN hd hβ hz1 hz2 s₀ i
  -- the data at a point of `H`
  have hpt : ∀ ω ∈ H, ∃ z : ℝ≥0, ζ ω = z ∧ (z : ℝ) ∈ zetaU β (zw1 β a Y) (za1 β a Y)
      (zw2 β a s₀ Y) (za2 β a s₀ Y) ω ∧ s₀ ≤ z := by
    intro ω hω
    have hne := hHfin ω hω
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 hne
    have hzs : stopReal ζ ω = z := by unfold stopReal; rw [← hz]; rfl
    refine ⟨z, hz.symm, ?_, ?_⟩
    · have := zetaN_mem hd hβ hz1 hz2 s₀ i hne
      rwa [hzs] at this
    · have h1 := le_zetaP hd hβ hz1 hz2 s₀ i ω
      have h2 := zetaP_le_zetaN (β := β) (w₁ := zw1 β a Y) (α₁ := za1 β a Y)
        (w₂ := zw2 β a s₀ Y) (α₂ := za2 β a s₀ Y) s₀ i ω
      have := h1.trans h2
      rw [← hζ, ← hz] at this
      exact_mod_cast this
  have hHm : MeasurableSet H := hsζ.measurableSpace_le _ hH
  obtain ⟨Ln, hLn⟩ : ∃ Ln : ℝ≥0, Ln = ((4 : ℝ) ^ n).toNNReal := ⟨_, rfl⟩
  have hLnr : (Ln : ℝ) = (4 : ℝ) ^ n := by rw [hLn]; exact Real.coe_toNNReal _ (by positivity)
  rw [← hLn]
  have hc1 : c ≤ 1 := by linarith
  -- Lemma 4.1 for `W`
  have rel1 : ∀ ω ∈ H, ∃ t : ℝ≥0, ζ ω = t ∧
      (t : ℝ) ∈ stepRelaxedSet β (stepWr β a Y ω) (stepAr β a Y ω) := by
    intro ω hω
    obtain ⟨z, hz, hU, -⟩ := hpt ω hω
    exact ⟨z, hz, hU.1⟩
  have hav1 := toReal_avoid hc1 (hav a hsζ hH rel1)
  -- Lemma 4.1 for `Z₂`
  have hS2 := isStoppingTime_stepSubShift hF a s₀ hsζ
  have rel2 : ∀ ω ∈ H, ∃ t : ℝ≥0, stepSubShift s₀ ζ ω = t ∧
      (t : ℝ) ∈ stepRelaxedSet β (stepWr β (a + s₀) Y ω) (stepAr β (a + s₀) Y ω) := by
    intro ω hω
    obtain ⟨z, hz, hU, hs0z⟩ := hpt ω hω
    refine ⟨z - s₀, by simp only [stepSubShift, hz]; rfl, ?_⟩
    rw [NNReal.coe_sub hs0z]
    exact (relaxed_shift_iff (β := β) a s₀ ω (hYp ω) (x := (z : ℝ))
      (by exact_mod_cast hs0z)).1 hU.2
  have hav2 := toReal_avoid hc1
    (hav (a + s₀) hS2 (measurableSet_stepSubShift hF a s₀ hsζ hH) rel2)
  -- the events
  set E₁ := zEvent β (zw1 β a Y) (za1 β a Y) ζ Ln with hE₁
  set E₂ := zEvent β (zw2 β a s₀ Y) (za2 β a s₀ Y) ζ Ln with hE₂
  have h1sub : H ∩ {ω | ∀ t : ℝ≥0, ζ ω = t → ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤
      stepThit β (stepWr β a Y ω) (stepAr β a Y ω) (t : ℝ)} ⊆ H ∩ E₁ := by
    rintro ω ⟨hω, h⟩
    exact ⟨hω, mem_zEvent_of fun t ht => by rw [hLnr]; exact h t ht⟩
  have h2sub : H ∩ {ω | ∀ t : ℝ≥0, stepSubShift s₀ ζ ω = t → ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤
      stepThit β (stepWr β (a + s₀) Y ω) (stepAr β (a + s₀) Y ω) (t : ℝ)} ⊆ H ∩ E₂ := by
    rintro ω ⟨hω, h⟩
    refine ⟨hω, mem_zEvent_of fun t ht => ?_⟩
    obtain ⟨z, hz, -, hs0z⟩ := hpt ω hω
    have htz : t = z := by
      have : (t : WithTop ℝ≥0) = z := ht.symm.trans hz
      exact WithTop.coe_injective this
    subst htz
    have h3 := h (t - s₀) (by simp only [stepSubShift, ht]; rfl)
    have h4 := stepThit_shift_ge (β := β) (y := stepShift (a + s₀) (Y ω)) s₀ t hs0z
    rw [NNReal.coe_sub hs0z] at h3
    have e : ENNReal.ofReal ((t : ℝ) + Ln) = (s₀ : ℝ≥0∞) + ENNReal.ofReal ((t : ℝ) - s₀ + Ln) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg _)
        (by linarith [NNReal.coe_nonneg Ln, (by exact_mod_cast hs0z : (s₀ : ℝ) ≤ t)])]
      congr 1; ring
    rw [e]
    refine le_trans ?_ h4
    exact add_le_add le_rfl (by rw [hLnr]; exact h3)
  have hav1' : (1 - c) * P.real H ≤ P.real (H ∩ E₁) := hav1.trans (measureReal_mono h1sub)
  have hav2' : (1 - c) * P.real H ≤ P.real (H ∩ E₂) := hav2.trans (measureReal_mono h2sub)
  have hinc : H ∩ E₁ ∩ E₂ ⊆ H ∩ {ω | ζ ω + ((Ln : ℝ≥0) : WithTop ℝ≥0) ≤
      zetaP β (zw1 β a Y) (za1 β a Y) (zw2 β a s₀ Y) (za2 β a s₀ Y) s₀ (i + 1) ω} := by
    rintro ω ⟨⟨hω, h1⟩, h2⟩
    refine ⟨hω, ?_⟩
    show ζ ω + (Ln : WithTop ℝ≥0) ≤ min (stepThitStop β (zw1 β a Y) (za1 β a Y) ζ ω : WithTop ℝ≥0)
      (stepThitStop β (zw2 β a s₀ Y) (za2 β a s₀ Y) ζ ω : WithTop ℝ≥0)
    exact le_min h1 h2
  exact half_le_inter hc hHm (measurableSet_zEvent hβ hz1 hsζ Ln) hinc hav1' hav2'

end ElboimSly.Paper.Step
