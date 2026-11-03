/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.BaseH4Meas
public import ElboimSly.Paper.Base.DriversPath
public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Foundations.StrongApprox.BaseCoupling
public import ElboimSly.Foundations.SRW.KernelDef
public import Mathlib

/-!
# The base coupling as an (H4) coupling

The base coupling in the form of (H4) (a).

* `walkPathOf`: a step path restricted to `[0,T]` is a `WalkPath`.
* `admitsBMCoupling_of_srw_law`: for `n ≥ n₁(d)` and `T ≤ 4^{n+1}`, the law of any SRW restricted
  to `[0,T]` admits a `(√2, n^10)`-coupling with failure probability `e^{-n^4}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Paper.Base ElboimSly.Cyclic

variable {d : ℕ}

/-- A step path, restricted to `[0,T]`, as an element of `WalkPath`. -/
noncomputable def walkPathOf (T : ℝ≥0) {g : ℝ≥0 → Fin d → ℤ} (hg : IsStepPath g) : WalkPath d T :=
  ⟨fun t => g t, (hg.fin T).toFinset, fun s u hsu hF => by
    have h := ElboimSly.Cyclic.const_of_no_disc hg.rc (x := (s : ℝ≥0)) (y := (u : ℝ≥0)) hsu
      (fun r hr hd => hF r (by simpa using ⟨hd, hr.2.trans u.2.2⟩) ⟨hr.1, hr.2⟩) u
      ⟨hsu, le_rfl⟩
    exact h.symm⟩

/-- The restriction of a path to `[0,T]`, as a function on `Icc 0 T`. -/
def restrictIcc (T : ℝ≥0) (γ : PathSpace d) : Set.Icc (0 : ℝ≥0) T → Fin d → ℤ := fun t => γ t

theorem measurable_restrictIcc (T : ℝ≥0) : Measurable (restrictIcc (d := d) T) :=
  measurable_pi_iff.2 fun t => measurable_pi_apply (t : ℝ≥0)

/-- **the base coupling in the form of (H4) (a)**, in the form: the law of any SRW restricted to `[0,T]` admits a
`(√2, n^10)`-coupling with failure probability `e^{-n^4}`, for `n ≥ n₁(d)` and `T ≤ 4^{n+1}`. -/
theorem admitsBMCoupling_of_srw_law (d : ℕ) (hd : 1 ≤ d) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ T : ℝ, 0 ≤ T → T ≤ 4 ^ (n + 1) →
      ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) (Z₀ : Ω₀ → PathSpace d),
        IsSRW P₀ Z₀ →
        AdmitsBMCoupling d T.toNNReal
          (P₀.map fun ω (t : Set.Icc (0 : ℝ≥0) T.toNNReal) => Z₀ ω t)
          (Real.sqrt 2) ((n : ℝ) ^ 10) (Real.exp (-(n : ℝ) ^ 4)) := by
  obtain ⟨n₁, hn₁⟩ := StrongApprox.sa_base_coupling d hd
  refine ⟨n₁, fun n hn T hT0 hT Ω₀ _ P₀ Z₀ hZ₀ => ?_⟩
  obtain ⟨Ω', mΩ', P', N', B, hP', hN', hB, hX, hbd⟩ := hn₁ n hn T hT0 hT
  have := hP'
  set T' : ℝ≥0 := T.toNNReal with hT'
  let X : Ω' → PathSpace d := canonical d N'
  let Bp : Ω' → C(ℝ≥0, Fin d → ℝ) := fun ω => ⟨fun t => B t ω, (hB.continuous_zero ω).1⟩
  have hBp : Measurable Bp := Bridge.measurable_pathC hB
  have hXm : Measurable X := hX.1
  let Fm : Ω' → WalkPath d T' × C(ℝ≥0, Fin d → ℝ) := fun ω =>
    (walkPathOf T' (isDrivingPath_canonical N' ω).step, Bp ω)
  have hF1 : Measurable fun ω => (walkPathOf T' (isDrivingPath_canonical N' ω).step) := by
    refine Measurable.subtype_mk ?_
    exact (measurable_restrictIcc T').comp hXm
  have hFm : Measurable Fm := hF1.prodMk hBp
  refine ⟨P'.map Fm, ⟨by rw [Measure.map_apply hFm MeasurableSet.univ]; simp⟩, ?_, ?_, ?_⟩
  · -- the walk marginal
    have hg : Measurable fun p : WalkPath d T' × C(ℝ≥0, Fin d → ℝ) => p.1.1 :=
      measurable_subtype_coe.comp measurable_fst
    rw [Measure.map_map hg hFm]
    have e1 : ((fun p : WalkPath d T' × C(ℝ≥0, Fin d → ℝ) => p.1.1) ∘ Fm) =
        fun ω => restrictIcc T' (X ω) := rfl
    have e2 : (fun ω (t : Set.Icc (0 : ℝ≥0) T') => Z₀ ω t) =
        restrictIcc T' ∘ Z₀ := rfl
    rw [e1, e2, show (fun ω => restrictIcc T' (X ω)) = restrictIcc T' ∘ X from rfl,
      ← Measure.map_map (measurable_restrictIcc T') hZ₀.1,
      ← Measure.map_map (measurable_restrictIcc T') hXm, hZ₀.map_eq_model, hX.map_eq_model]
  · rw [Measure.map_map measurable_snd hFm]
    exact Bridge.isWienerMeasure_map_pathC hB
  · have hA := measurableSet_failEvent (d := d) (T := T') (Real.sqrt 2) ((n : ℝ) ^ 10)
    refine (Measure.map_apply hFm hA).trans_le (le_trans (measure_mono ?_) hbd)
    intro ω hω
    simp only [mem_preimage, mem_ofPred_eq, failTime, Fm] at hω ⊢
    refine hω.trans (iSup_le fun t => ?_)
    have ht : ((t : ℝ≥0) : ℝ) ≤ T := by
      have h1 : (t : ℝ≥0) ≤ T.toNNReal := t.2.2
      have h2 := NNReal.coe_le_coe.2 h1
      rwa [Real.coe_toNNReal _ hT0] at h2
    exact le_iSup (fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => ENNReal.ofReal
      ‖(fun i => ((walk d (N' ω) (t : ℝ≥0) i : ℤ) : ℝ)) - √2 • B (t : ℝ≥0) ω‖) ⟨t, ht⟩

end ElboimSly.Paper

end
