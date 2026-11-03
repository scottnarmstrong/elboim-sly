/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Meas
public import ElboimSly.Paper.Avoid.CoreMain
public import Mathlib

/-!
# ES22 Claim 5.6, event `E^b`: ES22 Lemma 4.1 in the relative form

Relative form, used in S5.  History `W_v|[a, T]` with `a` an `ℱ_T`-measurable time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ}

theorem isRCPath_add_const {d : ℕ} (v : Fin d → ℤ) {x : ℝ≥0 → Fin d → ℤ} (h : IsRCPath x) :
    IsRCPath (fun s => v + x s) := fun t => (h t).mono fun s hs => by simp [hs]

theorem es56_E2 (hd : 5 ≤ k + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
        {N N' : Ω → Measure (CycS ℕ (k + 2) β)} (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N')
        (v : Fin (k + 2) → ℤ) {Z : Ω → WithTop ℝ≥0}
        (hZ : IsStoppingTime (avoidFilt 𝒢₀ S.space) Z) (a : Ω → ℝ)
        (_ha : Measurable[hZ.measurableSpace] a) (_ha0 : ∀ ω, 0 ≤ a ω)
        (_haT : ∀ ω, a ω ≤ ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ))
        (X : Ω → ℝ≥0 → Fin (k + 2) → ℤ) (_hXm : Measurable X) (_hXrc : ∀ ω, IsRCPath (X ω))
        (_hind : Indep hZ.measurableSpace (MeasurableSpace.comap X inferInstance) Pr)
        (_hlaw : Pr.map X = Pr.map (avoidPath N)) {A : Set Ω}
        (_hA : MeasurableSet[hZ.measurableSpace] A)
        (_hArel : ∀ ω ∈ A, IsRelaxedTimeWrt β (escYv N v ω) (a ω)
          ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)),
        ENNReal.ofReal (1 - C * β ^ (-indDelta (k + 2) / 30)) * Pr A ≤
          Pr (A ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤
            hitTime β (escYv N v ω) (a ω) ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)
              (fun r => escYv N v ω ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ) +
                X ω r.toNNReal)}) := by
  obtain ⟨C, hC, H0⟩ := es4_1_core hd
  refine ⟨C, hC, fun n₀ => ?_⟩
  obtain ⟨β41, H1⟩ := H0 n₀
  refine ⟨β41, fun β _ n t₀ hβ Ω 𝒢₀ mΩ Pr N N' S v Z hZ a ha ha0 haT X hXm hXrc hind hlaw
    A hA hArel => ?_⟩
  have hPr := S.space.ppp.isProbabilityMeasure
  set Tr : Ω → ℝ := fun ω => ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ) with hTr
  have hTrm : Measurable[hZ.measurableSpace] Tr :=
    (measurable_stopReal_stop hZ).coe_nnreal_real
  set w : Ω → ℝ → Fin (k + 2) → ℤ := fun ω x => escYv N v ω x with hw
  have hmin : ∀ ω (s : ℝ), 0 ≤ min (a ω + max s 0) (Tr ω) :=
    fun ω s => le_min (by linarith [ha0 ω, le_max_right s 0]) (le_trans (ha0 ω) (haT ω))
  have hhist : Measurable[hZ.measurableSpace.prod inferInstance]
      (fun p : Ω × ℝ => w p.1 (min (a p.1 + max p.2 0) (Tr p.1))) := by
    have := escW_hist S hZ ha ha0 haT
    have e : (fun p : Ω × ℝ => w p.1 (min (a p.1 + max p.2 0) (Tr p.1))) =
        fun p => v + escW N p.1
          (min (a p.1 + max p.2 0) ((ElboimSly.SRW.stopReal Z p.1 : ℝ≥0) : ℝ)).toNNReal := rfl
    rw [e]
    exact measurable_const.add this
  have hrc : ∀ ω, IsRCPath (fun s : ℝ≥0 => w ω (min (a ω + s) (Tr ω))) := by
    intro ω
    have h0 : ∀ s : ℝ≥0, 0 ≤ min (a ω + (s : ℝ)) (Tr ω) := fun s =>
      le_min (by linarith [ha0 ω, s.2]) (le_trans (ha0 ω) (haT ω))
    have e : (fun s : ℝ≥0 => w ω (min (a ω + s) (Tr ω))) =
        fun s => v + (avoidPath (cycNgood N) ω ∘
          fun s : ℝ≥0 => (min (a ω + s) (Tr ω)).toNNReal) s := by
      funext s
      simp only [hw, escYv, escY, escW, Function.comp, avoidPath, Real.coe_toNNReal _ (h0 s)]
    rw [e]
    refine isRCPath_add_const v (isRCPath_comp_mono (isRCPath_avoidPath (cycGood_cycNgood N ω)) ?_ ?_)
    · exact continuous_real_toNNReal.comp (by fun_prop)
    · intro s s' hss
      have h : (s : ℝ) ≤ s' := by exact_mod_cast hss
      exact Real.toNNReal_mono (min_le_min (by linarith) le_rfl)
  have hcore := H1 β n t₀ hβ S.params Pr N S.space.ppp hZ.measurableSpace hZ.measurableSpace_le
    Pr a Tr w X (fun ω => haT ω) ha hTrm hhist hrc hXm hXrc hind hlaw
  exact hcore.2 hA hArel

end ElboimSly.Paper.Escape

end
