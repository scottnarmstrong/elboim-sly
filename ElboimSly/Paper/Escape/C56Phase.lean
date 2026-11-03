/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Point2
public import ElboimSly.Paper.Escape.C56Core
public import ElboimSly.Paper.Escape.C56Freeze
public import ElboimSly.Paper.Escape.C56MeasG
public import ElboimSly.Paper.Avoid.Lem41
public import Mathlib

/-!
# ES22 Claim 5.6, phase `i`: `P(ℬ_i | ℱ_{ζ_{i-1}}) ≥ c_*` on `G_{i-1}`

ES22 Claim 5.6, "Phase `i ∈ [1, 2m]`".  In integrated form: for `A = G_{i-1} ∈ ℱ_{ζ_{i-1}}`,
`c_* P(A) ≤ P(A ∩ ℬ_i)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

theorem ctube_le_one (d : ℕ) {K : ℝ} (hK : 0 ≤ K) : ctube d K ≤ 1 := by
  unfold ctube
  have h1 := tubeC0_le_one d (K := 8 * K) (by positivity)
  have h2 := tubeC0_le_one d (K := 52 * K) (by positivity)
  have h3 := tubeC0_pos' d (8 * K)
  have h4 := tubeC0_pos' d (52 * K)
  nlinarith

/-- The history start `a = ζ_{i-2}` (`0` for `i = 1`) as a random variable. -/
noncomputable def histStart {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (t : ℝ) (m i : ℕ) (ω : Ω) : ℝ :=
  if i - 1 = 0 then 0 else ((escZt N t m (i - 1 - 1) ω : ℝ≥0) : ℝ)

theorem histStart_eq {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (v : Fin (k + 2) → ℤ) {t : ℝ} (ht : 0 ≤ t)
    (m i : ℕ) (ω : Ω) : escZetaPrev β (escYv N v ω) t m (i - 1) = histStart N t m i ω := by
  unfold escZetaPrev histStart
  split_ifs
  · rfl
  · exact escZeta_yv v ht ω m (i - 1 - 1)

theorem combine_bounds {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {A E1 E2 : Set Ω} (hE1 : MeasurableSet E1) {q c2 cs : ℝ≥0∞}
    (h1 : q * Pr A ≤ Pr (A ∩ E1)) (h2 : c2 * Pr A ≤ Pr (A ∩ E2)) (hsum : 1 + cs ≤ q + c2) :
    cs * Pr A ≤ Pr (A ∩ (E1 ∩ E2)) := by
  have hsplit : Pr (A ∩ E2) ≤ Pr (A ∩ (E1 ∩ E2)) + Pr (A \ E1) := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    by_cases h : ω ∈ E1
    · exact Or.inl ⟨hω.1, h, hω.2⟩
    · exact Or.inr ⟨hω.1, h⟩
  have hdiff : Pr (A ∩ E1) + Pr (A \ E1) = Pr A := measure_inter_add_sdiff A hE1
  have hfin : Pr A ≠ ⊤ := measure_ne_top _ _
  have key : Pr A + cs * Pr A ≤ Pr (A ∩ (E1 ∩ E2)) + Pr A := by
    calc Pr A + cs * Pr A = (1 + cs) * Pr A := by rw [add_mul, one_mul]
      _ ≤ (q + c2) * Pr A := by gcongr
      _ = q * Pr A + c2 * Pr A := add_mul _ _ _
      _ ≤ Pr (A ∩ E1) + Pr (A ∩ E2) := add_le_add h1 h2
      _ ≤ Pr (A ∩ E1) + (Pr (A ∩ (E1 ∩ E2)) + Pr (A \ E1)) := by gcongr
      _ = Pr (A ∩ (E1 ∩ E2)) + (Pr (A ∩ E1) + Pr (A \ E1)) := by ring
      _ = Pr (A ∩ (E1 ∩ E2)) + Pr A := by rw [hdiff]
  exact (ENNReal.add_le_add_iff_right hfin).1 (by rw [add_comm (cs * Pr A) (Pr A)]; exact key)

/-- **Phase `i`.** -/
theorem phase_prob (hd : 5 ≤ k + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
        {N N' : Ω → Measure (CycS ℕ (k + 2) β)} (_S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N')
        {j : ℕ} {u v z : Fin (k + 2) → ℤ} (_hgeom : EscGeom j u v z) {t : ℝ}
        (_hβ : (2 : ℝ) ^ 40 ≤ β) (_hβj : β < 4 ^ j) (_ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (_ht2 : t ≤ 4 ^ j)
        (_hjn : (4 : ℝ) ^ j ≤ 4 ^ n) (_hsb : Real.sqrt β ≤ t)
        (_hn0 : (4 : ℝ) ^ n₀ < 9 / 10 * Real.sqrt β) (_hm3 : 3 ≤ escPhaseM β t)
        (_hθ : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * escPhaseM β t →
          (4864 / 10 * es56Rho t (escPhaseM β t) i ^ 2) ^ indThetaH ≤
            escR t (escPhaseM β t) i / 30)
        (η : ℝ) (_hη : ∀ T : ℝ, 9 / 10 * Real.sqrt β ≤ T → T ≤ (4 : ℝ) ^ n →
          Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2) ≤ η)
        (_hconst : escCstar (k + 2) + 2 * η + C * β ^ (-indDelta (k + 2) / 30) ≤
          ctube (k + 2) escKstar)
        {i : ℕ} (_hi1 : 1 ≤ i) (_him : i ≤ 2 * escPhaseM β t),
        ENNReal.ofReal (escCstar (k + 2)) *
            Pr {ω | EscG β j u v z t (escYv N v ω) (i - 1)} ≤
          Pr ({ω | EscG β j u v z t (escYv N v ω) (i - 1)} ∩
            {ω | EscBi β j u v z t (escYv N v ω) i}) := by
  obtain ⟨C, hC, H0⟩ := es56_E2 hd
  refine ⟨C, hC, fun n₀ => ?_⟩
  obtain ⟨β41, H1⟩ := H0 n₀
  refine ⟨β41, fun β _ n t₀ hβ41 Ω 𝒢₀ mΩ Pr N N' S j u v z hgeom t hβ hβj ht1 ht2 hjn hsb hn0
    hm3 hθ η hη hconst i hi1 him => ?_⟩
  have := S.space.ppp.isProbabilityMeasure
  have hβ0 : 0 < β := Fact.out
  have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 hβ0) hsb
  set m := escPhaseM β t with hm
  have hZ := isStoppingTime_escZt S ht0.le m (i - 1)
  have hfin : ∀ᵐ ω ∂Pr, ((fun ω => ((escZt N t m (i - 1) ω : ℝ≥0) : WithTop ℝ≥0)) ω) ≠ ⊤ :=
    ae_of_all _ fun ω => WithTop.coe_ne_top
  obtain ⟨M, hM, ⟨hXm, hXrc, hind, hlaw⟩, hcpl⟩ := es4_couple S hZ hfin
  set A : Set Ω := {ω | EscG β j u v z t (escYv N v ω) (i - 1)} with hAdef
  have hA : MeasurableSet[hZ.measurableSpace] A := measurableSet_EscG S j u v z ht0 (i - 1)
  have hAm : MeasurableSet A := hZ.measurableSpace_le _ hA
  have hNg : Measurable (avoidPath (cycNgood N)) :=
    measurable_avoidPath_cycNgood S.space.ppp.measurable
  have hXc : Measurable (escCPath M) := measurable_escCPath hXm
  -- the parameters of the phase
  set tnf : Ω → ℝ≥0 := fun ω => escZt N t m (i - 1) ω with htnf
  have htnm : Measurable[hZ.measurableSpace] tnf := measurable_stopReal_stop hZ
  have hUx : Measurable[hZ.measurableSpace] (fun ω => v + escW N ω (tnf ω)) := by
    have h := @measurable_fn_at (Fin (k + 2) → ℤ) _ _ _ Ω hZ.measurableSpace
      (fun ω => stopP N t m (i - 1) ω) (measurable_stopP S ht0.le m (i - 1)) tnf htnm
    have e : (fun ω => (stopP N t m (i - 1) ω).fn (tnf ω)) = fun ω => escW N ω (tnf ω) := by
      funext ω; simp [stopP, CPath.stop_fn, tnf, escCPath_fn]
    rw [e] at h
    exact (measurable_of_countable (fun x : Fin (k + 2) → ℤ => v + x)).comp h
  have hU : Measurable[hZ.measurableSpace]
      (fun ω => ((v + escW N ω (tnf ω), ((tnf ω : ℝ≥0) : ℝ)))) :=
    hUx.prodMk htnm.coe_nnreal_real
  have hΓm := measurableSet_gamFam hβ0 j u v z ht0.ne' i
  have hyvat : ∀ ω, escYv N v ω ((tnf ω : ℝ≥0) : ℝ) = v + escW N ω (tnf ω) := by
    intro ω; simp [escYv, escY]
  -- (E1) the tube and relaxed-path events
  have hq : ∀ ω ∈ A, ENNReal.ofReal (ctube (k + 2) escKstar - 2 * η) ≤
      (Pr.map (escCPath M)) {p | ((v + escW N ω (tnf ω), ((tnf ω : ℝ≥0) : ℝ)), p) ∈
        gamFam β j u v z t i} := by
    intro ω hω
    have hset : MeasurableSet {p : CPath (Fin (k + 2) → ℤ) |
        ((v + escW N ω (tnf ω), ((tnf ω : ℝ≥0) : ℝ)), p) ∈ gamFam β j u v z t i} :=
      measurable_prodMk_left hΓm
    rw [map_escCPath_eq hXm S.space.ppp hlaw,
      Measure.map_apply (measurable_escCPath hNg) hset]
    have hTmem := escZeta_mem β (escYv N v ω) ht0.le m (i - 1)
    have hz : escZeta β (escYv N v ω) t m (i - 1) = ((tnf ω : ℝ≥0) : ℝ) :=
      escZeta_yv v ht0.le ω m (i - 1)
    have hx : ‖escCast (v + escW N ω (tnf ω)) - escCurve j u v z t ((tnf ω : ℝ≥0) : ℝ)‖ ≤
        if i = 1 then es56Rho t m 0 else (24 / 100) * escR t m (i - 1) := by
      by_cases h1 : i = 1
      · subst h1
        have := hω.1.2.2
        simp only [Nat.sub_self] at this ⊢
        simp only [ite_true]
        rw [hz, hyvat] at this
        exact this
      · simp only [ite_eq_right h1]
        have := (hω.2 (i - 1) (by omega) le_rfl).2.2
        rw [hz, hyvat] at this
        exact this
    have hs := slice_lower S.params S.space.ppp hgeom hβ0 hsb ht1 ht2 hjn hn0 hm3 hi1 him
      (hθ i hi1 him) (a' := ((tnf ω : ℝ≥0) : ℝ)) (by rw [← hz]; exact hTmem.1)
      (by rw [← hz]; exact hTmem.2) (v + escW N ω (tnf ω)) hx
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hs
    have hlen := phase_length_ge hβ0 hsb hi1 him
    have hbt := es56B_le_t ht0.le m i
    have hT1 : 9 / 10 * Real.sqrt β ≤ es56B t m i - ((tnf ω : ℝ≥0) : ℝ) := by
      have := hTmem.2; rw [hz] at this; linarith
    have ha0 : 0 ≤ ((tnf ω : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have hT2 : es56B t m i - ((tnf ω : ℝ≥0) : ℝ) ≤ (4 : ℝ) ^ n := by
      have : t ≤ (4 : ℝ) ^ n := ht2.trans hjn
      linarith
    have := hη _ hT1 hT2
    linarith
  have hfreeze := freeze_ge hZ.measurableSpace Pr hZ.measurableSpace_le hU hXc
    (indep_escCPath hind) hA hΓm hq
  -- (E2) the hitting-time event
  have hHm : Measurable[hZ.measurableSpace] (histStart N t m i) := by
    unfold histStart
    by_cases h0 : i - 1 = 0
    · simp only [h0, ite_true]; exact measurable_const
    · simp only [h0, ite_false]
      exact measurable_escZt_real_mono S ht0.le m (by omega : i - 1 - 1 ≤ i - 1)
  have hH0 : ∀ ω, 0 ≤ histStart N t m i ω := fun ω => by
    unfold histStart; split_ifs
    · exact le_rfl
    · exact NNReal.coe_nonneg _
  have hHT : ∀ ω, histStart N t m i ω ≤
      ((ElboimSly.SRW.stopReal (fun ω => ((escZt N t m (i - 1) ω : ℝ≥0) : WithTop ℝ≥0)) ω :
        ℝ≥0) : ℝ) := by
    intro ω; unfold histStart; split_ifs
    · exact NNReal.coe_nonneg _
    · exact_mod_cast escZt_mono N ht0.le m (by omega : i - 1 - 1 ≤ i - 1) ω
  have hArel : ∀ ω ∈ A, IsRelaxedTimeWrt β (escYv N v ω) (histStart N t m i ω)
      ((ElboimSly.SRW.stopReal (fun ω => ((escZt N t m (i - 1) ω : ℝ≥0) : WithTop ℝ≥0)) ω :
        ℝ≥0) : ℝ) := by
    intro ω hω
    have h := EscG_relaxed ht0.le (escYv N v ω) (escYv_hrc N v ω) hω
    rw [histStart_eq N v ht0.le m i ω, escZeta_yv v ht0.le ω m (i - 1)] at h
    exact h
  have hcore := H1 β n t₀ hβ41 𝒢₀ S v hZ (histStart N t m i) hHm hH0 hHT (escW M) hXm hXrc
    hind hlaw hA hArel
  have hE1m : MeasurableSet {ω | ((v + escW N ω (tnf ω), ((tnf ω : ℝ≥0) : ℝ)), escCPath M ω) ∈
      gamFam β j u v z t i} := ((hU.mono hZ.measurableSpace_le le_rfl).prodMk hXc) hΓm
  have hη0 : 0 ≤ η := by
    have h := hη (9 / 10 * Real.sqrt β) le_rfl (by
      have := ht2.trans hjn
      nlinarith [hsb, Real.sqrt_nonneg β])
    exact le_trans (Real.exp_pos _).le h
  have hcst := escCstar_pos (k + 2)
  have hct1 := ctube_le_one (k + 2) (K := escKstar) (by unfold escKstar; norm_num)
  have hCb : 0 ≤ C * β ^ (-indDelta (k + 2) / 30) :=
    mul_nonneg hC.le (Real.rpow_nonneg hβ0.le _)
  have hsum : 1 + ENNReal.ofReal (escCstar (k + 2)) ≤
      ENNReal.ofReal (ctube (k + 2) escKstar - 2 * η) +
        ENNReal.ofReal (1 - C * β ^ (-indDelta (k + 2) / 30)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hcst.le,
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hcomb := combine_bounds hE1m hfreeze hcore hsum
  refine hcomb.trans (measure_mono_ae ?_)
  filter_upwards [ae_cycNgood_eq S.space.ppp, ae_cycNgood_eq hM, hcpl] with ω hωN hωM hωc hω
  obtain ⟨hωA, hωE1, hωE2⟩ := hω
  refine ⟨hωA, ?_⟩
  have hE2' : ENNReal.ofReal ((4 : ℝ) ^ n) ≤ hitTime β (escYv N v ω) (histStart N t m i ω)
      ((escZt N t m (i - 1) ω : ℝ≥0) : ℝ)
      (fun r => escYv N v ω ((escZt N t m (i - 1) ω : ℝ≥0) : ℝ) + escW M ω r.toNNReal) := hωE2
  rw [← histStart_eq N v ht0.le m i ω] at hE2'
  exact phase_pointwise hωN hωM hgeom hβ hβj ht1 ht2 hjn hi1 him
    (hωc (escZt N t m (i - 1) ω) rfl) hωA hωE1 hE2'

end ElboimSly.Paper.Escape

end
