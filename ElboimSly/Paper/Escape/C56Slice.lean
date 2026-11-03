/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Gam
public import ElboimSly.Paper.Escape.C56Param
public import ElboimSly.Paper.Escape.C56Law
public import ElboimSly.Paper.Escape.C56Meas
public import Mathlib

/-!
# ES22 Claim 5.6, phase `i`: the slice probability of `E^a ∩ E^d`

ES22 Claim 5.6, "`E^a`" and "`E^d`".  For every start `(x, a')` of the phase, the walk
satisfies the tube condition and the relaxed-path condition with probability at least
`c_tube - 2 e^{-n_T²}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- The joint event `E^a ∩ E^d` of phase `i`, as a set of `((x, a'), p)`. -/
def gamFam (β : ℝ) (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ) (i : ℕ) :
    Set (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) :=
  tubeFam (fun a r => escCurve j u v z t (a + r)) (fun a => es56B t (escPhaseM β t) i - a)
    (escR t (escPhaseM β t) i) (24 / 100 * escR t (escPhaseM β t) i) ∩
  relFam β (fun a => es56B t (escPhaseM β t) i - a)

theorem measurableSet_gamFam {β : ℝ} (hβ : 0 < β) (j : ℕ) (u v z : Fin (k + 2) → ℤ) {t : ℝ}
    (ht : t ≠ 0) (i : ℕ) : MeasurableSet (gamFam β j u v z t i) := by
  have hT : Measurable (fun a : ℝ => es56B t (escPhaseM β t) i - a) :=
    measurable_const.sub measurable_id
  refine MeasurableSet.inter ?_ (measurableSet_relFam hβ hT)
  refine measurableSet_tubeFam _ ?_ hT _ _
  have hc := continuous_escCurve j u v z t ht
  exact (hc.comp (continuous_fst.add continuous_snd)).measurable

theorem tubeRat_mono {x : Fin (k + 2) → ℤ} {f : ℝ → Fin (k + 2) → ℝ} {R R' R2 R2' T : ℝ}
    (h1 : R ≤ R2) (h2 : R' ≤ R2') : tubeRat x f R R' T ⊆ tubeRat x f R2 R2' T := by
  rintro p ⟨a, b, c, d⟩
  exact ⟨fun q h0 h1' => (a q h0 h1').trans h1, b.trans h1,
    fun q h0 h1' => (c q h0 h1').trans h2, d.trans h2⟩

section Slice

variable {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}

/-- **The slice bound.** -/
theorem slice_lower (hp : Es4Params (k + 2) β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr) {j : ℕ}
    {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {t : ℝ}
    (hβ0 : 0 < β) (hsb : Real.sqrt β ≤ t)
    (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j) (hjn : (4 : ℝ) ^ j ≤ 4 ^ n)
    (hn0 : (4 : ℝ) ^ n₀ < 9 / 10 * Real.sqrt β)
    {i : ℕ} (hm3 : 3 ≤ escPhaseM β t) (hi1 : 1 ≤ i) (him : i ≤ 2 * escPhaseM β t)
    (hθ : (4864 / 10 * es56Rho t (escPhaseM β t) i ^ 2) ^ indThetaH ≤
      escR t (escPhaseM β t) i / 30)
    {a' : ℝ} (hT1 : escPhaseA t (escPhaseM β t) (i - 1) ≤ a')
    (hT2 : a' ≤ es56B t (escPhaseM β t) (i - 1)) (x : Fin (k + 2) → ℤ)
    (hx : ‖escCast x - escCurve j u v z t a'‖ ≤
      if i = 1 then es56Rho t (escPhaseM β t) 0 else
        (24 / 100) * escR t (escPhaseM β t) (i - 1)) :
    ENNReal.ofReal (ctube (k + 2) escKstar - 2 * Real.exp
        (-((avoidLevel (es56B t (escPhaseM β t) i - a') : ℕ) : ℝ) ^ 2)) ≤
      Pr {ω | escCPath N ω ∈ {p | ((x, a'), p) ∈ gamFam β j u v z t i}} := by
  have := hN.isProbabilityMeasure
  have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 hβ0) hsb
  set m := escPhaseM β t with hm
  set T := es56B t m i - a' with hTdef
  have hlen := phase_length_ge hβ0 hsb hi1 him
  have hTlen : 9 / 10 * Real.sqrt β ≤ T := by
    have := hT2
    rw [hTdef]; linarith
  have h1 : (4 : ℝ) ^ n₀ < T := lt_of_lt_of_le hn0 hTlen
  have ha0 : 0 ≤ a' := (escPhaseA_nonneg ht0.le m (i - 1)).trans hT1
  have h2 : T ≤ (4 : ℝ) ^ n := by
    have := es56B_le_t ht0.le m i
    rw [hTdef]; linarith
  have hK : (1 : ℝ) ≤ escKstar := by unfold escKstar; norm_num
  obtain ⟨hρ, hb, hc, hd, he⟩ := tube_params hgeom ht1 ht2 hm3 hi1 him hT1 hT2 hx
  set ρ := 29 / 30 * escR t m i with hρdef
  set f : ℝ → Fin (k + 2) → ℝ := fun r => escCurve j u v z t (a' + r) with hf
  have htube := walk_tube_prob (N := N) hp hN h1 h2 hK hρ hb hc (f := f) hd x he
  set η := Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2) with hη
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  -- the error `T^θ ≤ R_i / 30`
  have hwin := phase_window ht0 hi1 hT1 hT2
  have hTθ : T ^ indThetaH ≤ escR t m i / 30 := by
    have h0 : 0 ≤ T := by linarith
    have : T ^ indThetaH ≤ (4864 / 10 * es56Rho t m i ^ 2) ^ indThetaH :=
      Real.rpow_le_rpow h0 hwin.2.1 (by unfold indThetaH; norm_num)
    exact this.trans hθ
  have hRpos := escR_pos ht0 m i
  have hsub : tubeRat x f (ρ + T ^ indThetaH) (ρ / 5 + T ^ indThetaH) T ⊆
      tubeRat x f (escR t m i) (24 / 100 * escR t m i) T := by
    refine tubeRat_mono ?_ ?_
    · rw [hρdef]; linarith
    · rw [hρdef]; linarith
  have hrel := relPathSet_prob (N := N) hp hN h1 h2
  have hNg := measurable_avoidPath_cycNgood hN.measurable
  have hXm := measurable_escCPath hNg
  have hrelm : MeasurableSet (relPathSet (k := k) β T) := measurableSet_relPathSet hβ0 T
  -- measure estimates
  set E1 : Set Ω := {ω | escCPath N ω ∈ tubeRat x f (ρ + T ^ indThetaH) (ρ / 5 + T ^ indThetaH) T}
  set E2 : Set Ω := {ω | escCPath N ω ∈ relPathSet β T}
  have hE2m : MeasurableSet E2 := hXm hrelm
  have hcompl : Pr E2ᶜ ≤ ENNReal.ofReal η := by
    rw [prob_compl_eq_one_sub hE2m]
    have : ENNReal.ofReal (1 - η) ≤ Pr E2 := hrel
    calc 1 - Pr E2 ≤ 1 - ENNReal.ofReal (1 - η) := tsub_le_tsub_left this _
      _ ≤ ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by
          have : η ≤ 1 := by
            rw [hη]; exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ((avoidLevel T : ℕ) : ℝ)])
          linarith)]
        apply ENNReal.ofReal_le_ofReal; linarith
  have hS : {ω | escCPath N ω ∈ {p | ((x, a'), p) ∈ gamFam β j u v z t i}} ⊇
      {ω | escCPath N ω ∈ tubeRat x f (escR t m i) (24 / 100 * escR t m i) T} ∩ E2 := by
    rintro ω ⟨h1', h2'⟩
    exact ⟨h1', h2'⟩
  have hE1 : ENNReal.ofReal (ctube (k + 2) escKstar) - ENNReal.ofReal η ≤ Pr E1 := htube
  have hmono : Pr E1 ≤ Pr ({ω | escCPath N ω ∈ tubeRat x f (escR t m i) (24 / 100 * escR t m i) T}) :=
    measure_mono fun ω hω => hsub hω
  have hsplit : Pr {ω | escCPath N ω ∈ tubeRat x f (escR t m i) (24 / 100 * escR t m i) T} ≤
      Pr ({ω | escCPath N ω ∈ tubeRat x f (escR t m i) (24 / 100 * escR t m i) T} ∩ E2) +
        Pr E2ᶜ := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases h : ω ∈ E2
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr h
  have hfinal : ENNReal.ofReal (ctube (k + 2) escKstar) ≤
      Pr {ω | escCPath N ω ∈ {p | ((x, a'), p) ∈ gamFam β j u v z t i}} +
        (ENNReal.ofReal η + ENNReal.ofReal η) := by
    have h3 : ENNReal.ofReal (ctube (k + 2) escKstar) ≤ Pr E1 + ENNReal.ofReal η :=
      tsub_le_iff_right.1 hE1
    calc ENNReal.ofReal (ctube (k + 2) escKstar) ≤ Pr E1 + ENNReal.ofReal η := h3
      _ ≤ (Pr ({ω | escCPath N ω ∈ tubeRat x f (escR t m i) (24 / 100 * escR t m i) T} ∩ E2) +
            ENNReal.ofReal η) + ENNReal.ofReal η := by
          gcongr
          exact hmono.trans (hsplit.trans (add_le_add le_rfl hcompl))
      _ ≤ _ := by
          rw [add_assoc]
          gcongr
  have h2η : (0 : ℝ) ≤ 2 * η := by positivity
  rw [ENNReal.ofReal_sub _ h2η]
  refine tsub_le_iff_right.2 ?_
  have : ENNReal.ofReal η + ENNReal.ofReal η = ENNReal.ofReal (2 * η) := by
    rw [← ENNReal.ofReal_add hη0 hη0]; congr 1; ring
  rw [← this]
  exact hfinal

end Slice

end ElboimSly.Paper.Escape

end
