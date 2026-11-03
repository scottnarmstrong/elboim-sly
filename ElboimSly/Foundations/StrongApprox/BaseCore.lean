/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseGood
public import ElboimSly.Foundations.Brownian.Oscillation
public import Mathlib

/-!
# The union bound of the base coupling

ES22 (8.3): base coupling with precision n^10 ("Bad events", "Good event").

`base_core` is the form of the theorem for a fixed horizon `N` and a fixed level `a`, for a coupling
`μN` supplied by a1: KMT coupling for Poisson increments.  It is a conditional helper: the Kmt tail bound `hkmt` is
an input, and the theorem ES22 (8.3): base coupling with precision n^10 is derived from it in `BaseCoupling.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

variable {d N : ℕ} {μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))} [IsProbabilityMeasure μN]

theorem measurable_Sdef (J : Fin N) : Measurable fun p : (Fin N → ℝ) × (Fin N → ℝ) => Sdef p J := by
  unfold Sdef
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (((measurable_pi_apply i).comp measurable_fst).sub measurable_const).sub
    ((measurable_pi_apply i).comp measurable_snd)

/-- The bad set of the coupling coordinates. -/
def A1set (N : ℕ) (c : ℝ) : Set ((Fin N → ℝ) × (Fin N → ℝ)) :=
  {p | ∃ J : Fin N, c ≤ |Sdef p J|}

theorem measurableSet_A1set (c : ℝ) : MeasurableSet (A1set N c) := by
  have : A1set N c = ⋃ J : Fin N, {p | c ≤ |Sdef p J|} := by ext p; simp [A1set]
  rw [this]
  exact MeasurableSet.iUnion fun J => measurableSet_le measurable_const
    (measurable_Sdef J).abs

theorem measurePreserving_coord (v : Dir d) :
    MeasurePreserving (fun ω : OmBase d N => ω.1.1.1 v) (PBase d N μN) μN := by
  have h1 : MeasurePreserving (fun ω : OmBase d N => ω.1.1.1) (PBase d N μN) (PA d N μN) :=
    measurePreserving_fst.comp (measurePreserving_fst.comp measurePreserving_fst)
  exact (measurePreserving_eval (fun _ : Dir d => μN) v).comp h1

/-- The bound for the bad event `𝒜₁` (probability of one direction). -/
theorem prob_A1 {C K lam : ℝ} (hkmt : ∀ x : ℝ, 0 ≤ x →
      μN.real {p | ∃ j : Fin N, C * Real.log N + x ≤
        |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|} ≤ K * Real.exp (-lam * x))
    {a : ℝ} (ha : 0 ≤ a) :
    PBase d N μN {ω | ∃ v : Dir d, ∃ J : Fin N,
        C * Real.log N + a / 2 ≤ |Sdef (ω.1.1.1 v) J|} ≤
      (Fintype.card (Dir d) : ℝ≥0∞) * ENNReal.ofReal (K * Real.exp (-lam * (a / 2))) := by
  have hset : {ω : OmBase d N | ∃ v : Dir d, ∃ J : Fin N,
      C * Real.log N + a / 2 ≤ |Sdef (ω.1.1.1 v) J|} =
      ⋃ v : Dir d, (fun ω : OmBase d N => ω.1.1.1 v) ⁻¹' A1set N (C * Real.log N + a / 2) := by
    ext ω; simp [A1set]
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hv : ∀ v : Dir d, PBase d N μN ((fun ω : OmBase d N => ω.1.1.1 v) ⁻¹'
      A1set N (C * Real.log N + a / 2)) ≤ ENNReal.ofReal (K * Real.exp (-lam * (a / 2))) := by
    intro v
    rw [(measurePreserving_coord v).measure_preimage
      (measurableSet_A1set _).nullMeasurableSet]
    have := hkmt (a / 2) (by positivity)
    calc μN (A1set N (C * Real.log N + a / 2))
        = ENNReal.ofReal (μN.real (A1set N (C * Real.log N + a / 2))) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal this
  refine (Finset.sum_le_sum fun v _ => hv v).trans ?_
  simp

/-- The core estimate of ES22 (8.3): base coupling with precision n^10 for a fixed horizon `N` and level `a`. -/
theorem base_core (hd : 1 ≤ d) (hN : 1 ≤ N)
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ))
    (hμ2 : μN.map Prod.snd = Measure.pi fun _ : Fin N => gaussianReal 0 1)
    {C K lam : ℝ} (hkmt : ∀ x : ℝ, 0 ≤ x →
      μN.real {p | ∃ j : Fin N, C * Real.log N + x ≤
        |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|} ≤ K * Real.exp (-lam * x))
    {a : ℝ} (ha : 0 < a) (hCa : C * Real.log N + a / 2 ≤ a) {T : ℝ} (_hT : 0 ≤ T)
    (hTN : T ≤ N) :
    ∃ B : ℝ≥0 → OmBase d N → Fin d → ℝ,
      IsStandardBrownianMotion d B (PBase d N μN) ∧
      PBase d N μN {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧
          4 * a ≤ ‖Xr d (Nproc d N ω.1) t - √2 • B t ω‖} ≤
        (Fintype.card (Dir d) : ℝ≥0∞) * ENNReal.ofReal (K * Real.exp (-lam * (a / 2))) +
        ENNReal.ofReal (((N : ℝ) / 1 + 1) * Real.exp (4 * d * 1 * (Real.exp 1 - 1) - a)) +
        (4 * d * N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-a ^ 2 / (16 * √2 ^ 2 * 1))) := by
  obtain ⟨B, hB, hBsum⟩ := base_brownian (d := d) hμ2
  refine ⟨B, hB, ?_⟩
  set A1 : Set (OmBase d N) := {ω | ∃ v : Dir d, ∃ J : Fin N,
    C * Real.log N + a / 2 ≤ |Sdef (ω.1.1.1 v) J|} with hA1
  set A2 : Set (OmBase d N) := {ω | ∃ s s' : ℝ, 0 ≤ s ∧ s ≤ s' ∧ s' ≤ N ∧ s' - s ≤ 1 ∧
    a ≤ incrL1 d (Nproc d N ω.1) s s'} with hA2
  set A3 : Set (OmBase d N) := {ω | ∃ s s' : ℝ≥0, s ≤ (N : ℝ≥0) ∧ s' ≤ (N : ℝ≥0) ∧
    dist s s' ≤ ((1 : ℝ≥0) : ℝ) ∧ a ≤ ‖√2 • B s ω - √2 • B s' ω‖} with hA3
  set Nul : Set (OmBase d N) := {ω | ¬ (Nproc d N ω.1 ∈ goodSet d ∧ ∀ j : ℕ, j ≤ N →
    ∀ i : Fin d, ((walk d (Nproc d N ω.1) j i : ℤ) : ℝ) -
      √2 * ∑ m ∈ Finset.range j, Xfam d N ω.1 m i =
        Sfun ω.1.1.1 (i, true) j - Sfun ω.1.1.1 (i, false) j)} with hNul
  have hNul0 : PBase d N μN Nul = 0 := by
    have hmp : MeasurePreserving (fun ω : OmBase d N => ω.1) (PBase d N μN) (PMain d N μN) :=
      measurePreserving_fst
    have := hmp.quasiMeasurePreserving.ae (ae_walk_identity (μN := μN) hd hμ1)
    rwa [ae_iff] at this
  have hsub : {ω : OmBase d N | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧
      4 * a ≤ ‖Xr d (Nproc d N ω.1) t - √2 • B t ω‖} ⊆ Nul ∪ (A1 ∪ A2 ∪ A3) := by
    rintro ω ⟨t, htT, hbig⟩
    by_cases hω : (Nproc d N ω.1 ∈ goodSet d ∧ ∀ j : ℕ, j ≤ N →
      ∀ i : Fin d, ((walk d (Nproc d N ω.1) j i : ℤ) : ℝ) -
        √2 * ∑ m ∈ Finset.range j, Xfam d N ω.1 m i =
          Sfun ω.1.1.1 (i, true) j - Sfun ω.1.1.1 (i, false) j)
    swap
    · exact Or.inl hω
    right
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨h1, h2⟩, h3⟩ := hnot
    have hS : ∀ v : Dir d, ∀ j : ℕ, 1 ≤ j → j ≤ N → |Sfun ω.1.1.1 v j| < a := by
      intro v j hj1 hjN
      rw [Sfun_eq_Sdef' _ v hj1 hjN]
      have : ¬ ∃ J : Fin N, C * Real.log N + a / 2 ≤ |Sdef (ω.1.1.1 v) J| :=
        fun ⟨J, hJ⟩ => h1 ⟨v, J, hJ⟩
      push Not at this
      exact lt_of_lt_of_le (this _) hCa
    have hA2' : ∀ s s' : ℝ, 0 ≤ s → s ≤ s' → s' ≤ N → s' - s ≤ 1 →
        incrL1 d (Nproc d N ω.1) s s' < a := by
      intro s s' hs hss' hs'N hdiff
      by_contra hge
      exact h2 ⟨s, s', hs, hss', hs'N, hdiff, not_lt.1 hge⟩
    have hA3' : ∀ s s' : ℝ≥0, (s : ℝ) ≤ N → (s' : ℝ) ≤ N → dist s s' ≤ 1 →
        ‖√2 • B s ω - √2 • B s' ω‖ < a := by
      intro s s' hs hs' hdist
      by_contra hge
      refine h3 ⟨s, s', ?_, ?_, ?_, not_lt.1 hge⟩
      · exact_mod_cast hs
      · exact_mod_cast hs'
      · simpa using hdist
    have := good_bound (Nproc d N ω.1) (Xfam d N ω.1) (fun s => B s ω) (Sfun ω.1.1.1) a ha hN
      hω.2 (fun j => by rw [hBsum j ω]; funext i; simp [Finset.sum_apply]) hS hA2' hA3' t (htT.trans hTN)
    linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hNul0, zero_add]
  refine (measure_union_le _ _).trans ?_
  refine add_le_add ((measure_union_le _ _).trans (add_le_add (prob_A1 hkmt ha.le) ?_)) ?_
  · have := unit_windows (base_ppp hd hμ1) (T := (N : ℝ)) (h := 1) (Nat.cast_nonneg N) one_pos a
    exact this
  · have := hB.oscillation_le (T := (N : ℝ≥0)) (h := 1) (by simpa using (by omega : N ≠ 0))
      one_ne_zero (l := a) (σ := √2) ha (by positivity)
    refine le_trans (measure_mono ?_) (this.trans (le_of_eq ?_))
    · intro ω hω
      exact hω
    · simp

end StrongApprox
end ElboimSly
