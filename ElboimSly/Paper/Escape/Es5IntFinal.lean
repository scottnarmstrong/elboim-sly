/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es5IntVer
public import ElboimSly.Paper.Escape.Es51Thm
public import ElboimSly.Paper.Escape.Es55Final
public import ElboimSly.Paper.Heavy.EscInterfaceAll
public import Mathlib

/-!
# §6's input, unconditionally

Interface with S6; ES22 Theorem 5.1; ES22 Proposition 5.2; ES22 Lemma 5.5.

`heavyEscInterfaceAll_holds`: for `d ≥ 5` there is a family `E n₀` of constants
(`c₅ = c₅₁` independent of `n₀`, `β₅ = max (β₅(n₀)) 1`) such that `HeavyEscInterfaceAll d E`.

The proof composes `es5_5`, `es5_2_of_es55` and `es5_1_of_es52`, and then shows
`{τ⁽⁶⁾_esc < t_n ∧ t_reg} ⊆ {τ_esc < t_n ∧ t_reg}` up to a null set: almost surely, for each of the
countably many blocks, the versions `V_{B'}` equal `heavyEscVersion`
(`hV`), which equals `π_{B'}` on `{ξ_{B'} ≤ t_n}` (`heavyEscVersion_ae_eq_escPi`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Paper.Heavy

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem heavyXi_eq_escXi {ω : Ω} (hω : CycGood (N ω)) (ι : Fin (k + 2) → ℤ) :
    heavyXi (avoidWalk (cycNgood N)) (heavyScaleJ n) ι ω =
      escXi (escWalk (N ω)) (escBlock (escJ n) (fun c => 2 ^ escJ n * ι c)) := by
  have hB : heavyBlock (heavyScaleJ n) ι = escBlock (escJ n) (fun c => 2 ^ escJ n * ι c) :=
    heavyBlock_eq_escBlock (heavyScaleJ n) ι
  show entranceTime (escWalk (cycNgood N ω)) (heavyBlock (heavyScaleJ n) ι) = _
  rw [cycNgood_of_good hω, hB, escXi_eq_entranceTime]

theorem escPi_le_one (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (tn : ℝ)
    (B : Set (Fin (k + 2) → ℤ)) (ω : Ω) : escPi Pr N n (escJ n) tn B ω ≤ 1 := by
  have hPr := S.space.ppp.isProbabilityMeasure
  have : IsProbabilityMeasure (Pr.map N) :=
    (Measure.isProbabilityMeasure_map_iff S.space.ppp.measurable.aemeasurable).2 hPr
  unfold escPi resampleInt
  calc _ ≤ ∫⁻ _ν, (1 : ℝ≥0∞) ∂(Pr.map N) := by
        refine lintegral_mono fun ν => ?_
        show Paper.escY n (escJ n) tn B _ ≤ 1
        unfold Paper.escY
        split_ifs <;> simp
    _ = 1 := by simp

/-- The a.e. inclusion `{τ⁽⁶⁾ < t_n ∧ t_reg} ⊆ {τ_esc < t_n ∧ t_reg}`. -/
theorem tauV_ae_subset (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (hn : 0 < n)
    (V : (Fin (k + 2) → ℤ) → Ω → ℝ)
    (hV : ∀ ι, V ι =ᵐ[Pr] heavyEscVersion (avoidWalk_cycNgood_adapted S) Pr n ι) :
    {ω | heavyTauV (avoidWalk (cycNgood N) ω) (heavyScaleJ n) (fun ι => V ι ω)
        ((n : ℝ) ^ (-escGamma (k + 2))) <
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (avoidEnv (cycNgood N) ω 0))} ≤ᵐ[Pr]
      {ω | escTauEsc Pr N n (escJ n) (indScale t₀ n) (escGamma (k + 2)) ω <
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (copyEnv (N ω) 0))} := by
  set tn := indScale t₀ n with htn
  have hgood : ∀ᵐ ω ∂Pr, CycGood (N ω) := CycSchemeEnv.ae_cycGood' S.space.ppp
  have hall : ∀ᵐ ω ∂Pr, ∀ ι : Fin (k + 2) → ℤ,
      V ι ω = heavyEscVersion (avoidWalk_cycNgood_adapted S) Pr n ι ω :=
    ae_all_iff.2 hV
  have hb : ∀ᵐ ω ∂Pr, ∀ ι : Fin (k + 2) → ℤ,
      heavyXi (avoidWalk (cycNgood N)) (heavyScaleJ n) ι ω ≤ ENNReal.ofReal tn →
      heavyEscVersion (avoidWalk_cycNgood_adapted S) Pr n ι ω =
        (escPi Pr N n (escJ n) tn (escBlock (escJ n) (fun c => 2 ^ escJ n * ι c)) ω).toReal :=
    ae_all_iff.2 fun ι => heavyEscVersion_ae_eq_escPi S tn hn ι
  filter_upwards [hall, hb, hgood] with ω h1 h2 hg hlt
  have hlt' : heavyTauV (avoidWalk (cycNgood N) ω) (heavyScaleJ n) (fun ι => V ι ω)
      ((n : ℝ) ^ (-escGamma (k + 2))) <
      min (ENNReal.ofReal tn) (cycTreg (avoidEnv (cycNgood N) ω 0)) := hlt
  unfold heavyTauV at hlt'
  rw [iInf_lt_iff] at hlt'
  obtain ⟨ι, hι⟩ := hlt'
  rw [iInf_lt_iff] at hι
  obtain ⟨⟨h0, htop, hVc⟩, hι⟩ := hι
  have hlt1 := lt_of_lt_of_le hι (min_le_left _ _)
  have hlt2 := lt_of_lt_of_le hι (min_le_right _ _)
  set u : Fin (k + 2) → ℤ := fun c => 2 ^ escJ n * ι c with hu
  set B := escBlock (escJ n) u with hB
  have hxi : escXi (escWalk (N ω)) B = entranceTime (avoidWalk (cycNgood N) ω)
      (heavyBlock (heavyScaleJ n) ι) :=
    (heavyXi_eq_escXi (n := n) hg ι).symm
  have hle : escXi (escWalk (N ω)) B ≤ ENNReal.ofReal tn := by rw [hxi]; exact hlt1.le
  have hver := h2 ι (by rw [heavyXi_eq_escXi (n := n) hg ι]; exact hle)
  rw [← h1 ι] at hver
  have hpi : escPi Pr N n (escJ n) tn B ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2))) := by
    rw [ENNReal.le_ofReal_iff_toReal_le
      (ne_top_of_le_ne_top ENNReal.one_ne_top (escPi_le_one S tn B ω))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    rw [← hver]; exact hVc
  have hBmem : B ∈ escBlocks k (escJ n) := ⟨u, fun c => dvd_mul_right _ _, rfl⟩
  have htreg : cycTreg (avoidEnv (cycNgood N) ω 0) = cycTreg (copyEnv (N ω) 0) := by
    show cycTreg (copyEnv (cycNgood N ω) 0) = _
    rw [cycNgood_of_good hg]
  have hle2 : escTauEsc Pr N n (escJ n) tn (escGamma (k + 2)) ω ≤
      escXi (escWalk (N ω)) B :=
    iInf_le_of_le B (iInf_le_of_le hBmem (iInf_le_of_le ⟨hle, hpi⟩ le_rfl))
  have hxlt : escXi (escWalk (N ω)) B <
      min (ENNReal.ofReal tn) (cycTreg (copyEnv (N ω) 0)) := by
    rw [hxi, ← htreg]; exact hι
  exact lt_of_le_of_lt hle2 hxlt

end ElboimSly.Paper.Escape

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper MeasureTheory
open scoped ENNReal NNReal

/-- **interface with S6, unconditionally.**  For every `d ≥ 5` there is a family of constants
`E n₀` with `c₅` independent of `n₀` such that the interface of §5 with §6 holds. -/
theorem heavyEscInterfaceAll_holds {d : ℕ} (hd : 5 ≤ d) :
    ∃ E : ℕ → HeavyEscConsts, HeavyEscInterfaceAll d E := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hk : 3 ≤ k := by omega
  obtain ⟨c51, hc51, β5, h51⟩ :=
    Escape.es5_1_of_es52 (Escape.es5_2_of_es55 hk (Escape.es5_5 hk))
  refine ⟨fun n₀ => ⟨c51, max (β5 n₀) 1, ⌈Real.logb 4 (max (β5 n₀) 1)⌉₊, hc51,
    lt_of_lt_of_le one_pos (le_max_right _ _)⟩, fun n₀ => rfl, ?_⟩
  intro n₀ β _ n t₀ Ω 𝒢₀ mΩ Pr N N' S hβ5 V _ hV
  have hn : 0 < n := by
    have h1 := S.params.eight_le
    have h2 := S.params.lt
    omega
  have hβ' : β5 n₀ ≤ β := (le_max_left _ _).trans hβ5
  refine le_trans (measure_mono_ae (Escape.tauV_ae_subset S hn V hV)) ?_
  exact h51 S hβ'

end ElboimSly.Paper.Heavy
