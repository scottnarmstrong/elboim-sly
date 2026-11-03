/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78H1Rat
public import ElboimSly.Paper.Step.Lemma78Setting2
public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Foundations.Brownian.Oscillation
public import ElboimSly.Frozen.Defs.AdmitsBMCoupling
public import Mathlib

/-!
# `Osc` from a Brownian coupling

Support for the event cH_1 (the event `Osc_1`, via oscillation). If the law of the path
`F ω` on `[0, T']` admits a `(σ, ε)`-coupling with failure probability `η`, then the probability
that some pair of rational times `a, b ∈ [0, c]` with `|a - b| ≤ h` has `‖F a - F b‖ > r` is at most
`η + 4d⌈T'/h⌉ exp(-(r/2)²/(16σ²h))`, provided `2ε ≤ r/2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Bridge ElboimSly.Brownian

variable {d : ℕ}

/-- The event cH_1, the `Osc` part, from the Brownian coupling and oscillation. -/
theorem step78_osc_pathbound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T' : ℝ≥0} (c : ℝ≥0) (F : Ω → (Set.Icc (0 : ℝ≥0) T' → Fin d → ℤ)) (hT : 0 < T')
    (hFae : AEMeasurable F P) {σ ε η h r : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hh : 0 < h)
    (hr : 0 < r) (hεr : 2 * ε ≤ r / 2) (hc : AdmitsBMCoupling d T' (P.map F) σ ε η) :
    P (F ⁻¹' h1OscBad (d := d) T' c h r) ≤
      ENNReal.ofReal η + (4 * d * (⌈T' / h.toNNReal⌉₊ : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(r / 2) ^ 2 / (16 * σ ^ 2 * h))) := by
  obtain ⟨Q, hQ, hlaw, hB, -, hfail⟩ := exists_standardBrownianMotion_of_admitsBMCoupling hc
  set fv : WalkPath d T' × C(ℝ≥0, Fin d → ℝ) → (Set.Icc (0 : ℝ≥0) T' → Fin d → ℤ) :=
    fun p => p.1.1 with hfv
  have hfvm : Measurable fv := measurable_subtype_coe.comp measurable_fst
  set A := h1OscBad (d := d) T' c h r with hA
  have h2 : P (F ⁻¹' A) ≤ (P.map F) A := Measure.le_map_apply hFae A
  have h3 : (P.map F) A = Q (fv ⁻¹' A) := by
    rw [← hlaw, Measure.map_apply hfvm (measurableSet_h1OscBad T' c h r)]
  -- the pointwise decomposition on `Q`
  set B := zeroMod (Prod.snd : WalkPath d T' × C(ℝ≥0, Fin d → ℝ) → _) with hBdef
  set Fl : Set (WalkPath d T' × C(ℝ≥0, Fin d → ℝ)) := {p | ENNReal.ofReal ε ≤
        ⨆ t : Set.Icc (0 : ℝ≥0) T',
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖} with hFl
  set Bo : Set (WalkPath d T' × C(ℝ≥0, Fin d → ℝ)) :=
    {p | ∃ s s' : ℝ≥0, s ≤ T' ∧ s' ≤ T' ∧ dist s s' ≤ h.toNNReal ∧
      r / 2 ≤ ‖σ • B s p - σ • B s' p‖} with hBo
  have hdec : fv ⁻¹' A ⊆ Fl ∪ Bo := by
    intro p hp
    by_contra hnot
    rw [mem_union, not_or] at hnot
    obtain ⟨hnFl, hnBo⟩ := hnot
    obtain ⟨x, hx, hxr⟩ := mem_iUnion₂.1 hp
    have hlt : r < ‖p.1.1 x.1 - p.1.1 x.2‖ := hxr
    have hall : ∀ t : Set.Icc (0 : ℝ≥0) T',
        ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖ < ε := by
      intro t
      have h4 : ¬ ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) T',
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖ := hnFl
      rw [not_le] at h4
      exact (ENNReal.ofReal_lt_ofReal_iff hε).1
        ((le_iSup (fun t : Set.Icc (0 : ℝ≥0) T' =>
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖) t).trans_lt h4)
    have hB1 : ‖σ • B (x.1 : ℝ≥0) p - σ • B (x.2 : ℝ≥0) p‖ < r / 2 := by
      by_contra hge
      push Not at hge
      refine hnBo ⟨(x.1 : ℝ≥0), (x.2 : ℝ≥0), x.1.2.2, x.2.2.2, ?_, hge⟩
      rw [NNReal.dist_eq, Real.coe_toNNReal _ hh.le]
      exact hx.2.2.1
    have e1 := hall x.1
    have e2 := hall x.2
    have hnorm : ‖p.1.1 x.1 - p.1.1 x.2‖ =
        ‖(fun i => ((p.1.1 x.1 i : ℤ) : ℝ)) - (fun i => ((p.1.1 x.2 i : ℤ) : ℝ))‖ := by
      rw [← norm_intCast_pi]
      congr 1
      ext i; simp
    have htri : ‖(fun i => ((p.1.1 x.1 i : ℤ) : ℝ)) - (fun i => ((p.1.1 x.2 i : ℤ) : ℝ))‖ ≤
        ‖(fun i => ((p.1.1 x.1 i : ℤ) : ℝ)) - σ • B (x.1 : ℝ≥0) p‖ +
        ‖σ • B (x.1 : ℝ≥0) p - σ • B (x.2 : ℝ≥0) p‖ +
        ‖σ • B (x.2 : ℝ≥0) p - (fun i => ((p.1.1 x.2 i : ℤ) : ℝ))‖ := by
      calc _ = ‖((fun i => ((p.1.1 x.1 i : ℤ) : ℝ)) - σ • B (x.1 : ℝ≥0) p) +
            (σ • B (x.1 : ℝ≥0) p - σ • B (x.2 : ℝ≥0) p) +
            (σ • B (x.2 : ℝ≥0) p - (fun i => ((p.1.1 x.2 i : ℤ) : ℝ)))‖ := by congr 1; abel
        _ ≤ _ := (norm_add₃_le)
    rw [norm_sub_rev (σ • B (x.2 : ℝ≥0) p)] at htri
    linarith
  have h5 : Q (fv ⁻¹' A) ≤ Q Fl + Q Bo := (measure_mono hdec).trans (measure_union_le _ _)
  have h6 : Q Bo ≤ (4 * d * (⌈T' / h.toNNReal⌉₊ : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-(r / 2) ^ 2 / (16 * σ ^ 2 * h))) := by
    have := hQ
    have hT0 : T' ≠ 0 := hT.ne'
    have hh0 : h.toNNReal ≠ 0 := by simpa using hh
    have := hB.oscillation_le hT0 hh0 (l := r / 2) (σ := σ) (by positivity) hσ
    have hhc : ((h.toNNReal : ℝ≥0) : ℝ) = h := Real.coe_toNNReal _ hh.le
    calc Q Bo ≤ _ := this
      _ = _ := by rw [hhc]
  calc _ ≤ (P.map F) A := h2
    _ = Q (fv ⁻¹' A) := h3
    _ ≤ Q Fl + Q Bo := h5
    _ ≤ _ := add_le_add hfail h6

end ElboimSly.Paper.Step

end
