/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Es61Env
public import ElboimSly.Paper.Step.PairLaw
public import ElboimSly.Paper.Step.PairRC
public import ElboimSly.Paper.Step.DrivenLaw
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# From Theorem 6.1 (environment picture) to `StepEs61` (driven picture)

ES22 Theorem 6.1 and the opening of ES22 Lemma 7.1.

The event of `StepEs61` is a measurable functional of the pair `(W, α)` of the driven regenerated
walk and its regeneration function; the event of Theorem 6.1 is the same functional of the pair
`(regenWalk, regenStart)` of a Poisson environment.  The two pairs have the same law
(`regen_pair_law_env_cut_map` and the law of the SRW), so the probability bound transfers.

* `exists_pairBad_set`: a measurable subset of the path-pair space that agrees with the event on
  right-constant pairs (`measurableSet_not_winOK` on the subtype of right-constant pairs).
* `stepEs61_of_envEs61`: `StepEs61Env d c₆ β₆ → StepEs61 d c₆ β₆`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.SRW

/-- The space of pairs `(W, α)` of paths. -/
abbrev PairSp (d : ℕ) := (ℝ≥0 → Fin d → ℤ) × (ℝ≥0 → ℝ)

/-- Both coordinates are right-locally constant. -/
def PairRC {d : ℕ} (p : PairSp d) : Prop :=
  (∀ s : ℝ≥0, ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, p.1 u = p.1 s) ∧
    (∀ s : ℝ≥0, ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, p.2 u = p.2 s)

/-- The failure of the window event for the pair `(W, α)`. -/
def PairBad {d : ℕ} (β : ℝ) [Fact (0 < β)] (T h : ℝ) (n : ℕ) (p : PairSp d) : Prop :=
  ¬ WinOK T h n {t : ℝ | 0 ≤ t ∧ IsRelaxedTimeWrt β (stepExt p.1) (p.2 t.toNNReal) t}

theorem exists_pairBad_set {d : ℕ} (β : ℝ) [Fact (0 < β)] (T h : ℝ) (n : ℕ) :
    ∃ B : Set (PairSp d), MeasurableSet B ∧ ∀ p, PairRC p → (p ∈ B ↔ PairBad β T h n p) := by
  have hm : MeasurableSet {s : {p : PairSp d // PairRC p} | PairBad β T h n s.1} :=
    measurableSet_not_winOK (β := β) (Ω := {p : PairSp d // PairRC p}) (fun s => s.1.1)
      (fun s => s.1.2)
      (fun t => (measurable_pi_apply t).comp (measurable_fst.comp measurable_subtype_coe))
      (fun t => (measurable_pi_apply t).comp (measurable_snd.comp measurable_subtype_coe))
      (fun s u => s.2.1 u) (fun s u => s.2.2 u) T h n
  obtain ⟨B, hB, hEq⟩ := (MeasurableSpace.measurableSet_comap).1 hm
  refine ⟨B, hB, fun p hp => ?_⟩
  have := Set.ext_iff.1 hEq ⟨p, hp⟩
  simpa using this

/-- The pair attached to a path `x`: `(W^x_reg, α^x)`. -/
noncomputable def stepPair (β : ℝ) {d : ℕ} (x : ℝ≥0 → Fin d → ℤ) : PairSp d :=
  (stepReg β x, fun t => (stepAlpha β x t : ℝ))

theorem measurable_stepPair {d : ℕ} (β : ℝ) [Fact (0 < β)] :
    Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} => stepPair β x.1 := by
  have hb : 0 < β.toNNReal := toNNReal_pos'
  have hX : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} => mkCPath x.1 x.2 := by
    unfold mkCPath
    rw [CPath.measurable_iff]
    exact ⟨measurable_const, fun s => (measurable_pi_apply s).comp measurable_subtype_coe⟩
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.2 fun t => measurable_drivenRegenFrom_subtype hb t
  · exact measurable_pi_iff.2 fun t =>
      (measurable_drivenRegenAlpha_at hb (X := fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} =>
        mkCPath x.1 x.2) hX t).coe_nnreal_real

/-- Laws of regular-path valued maps push forward through a map measurable on regular paths. -/
theorem map_comp_of_regular' {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {d : ℕ} {Y : Ω → PathSpace d} {Z : Ω' → PathSpace d}
    (hY : Measurable Y) (hZ : Measurable Z) (hYr : ∀ ω, IsRegPath (Y ω))
    (hZr : ∀ ω, IsRegPath (Z ω)) (hlaw : P.map Y = P'.map Z) {γ : Type*} [MeasurableSpace γ]
    (F : (ℝ≥0 → Fin d → ℤ) → γ) (hF : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} =>
      F x.1) : P.map (fun ω => F (Y ω)) = P'.map (fun ω => F (Z ω)) := by
  have hYs : Measurable fun ω => (⟨Y ω, hYr ω⟩ : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}) :=
    hY.subtype_mk
  have hZs : Measurable fun ω => (⟨Z ω, hZr ω⟩ : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}) :=
    hZ.subtype_mk
  have m1 : Measurable fun ω => F (Y ω) := hF.comp hYs
  have m2 : Measurable fun ω => F (Z ω) := hF.comp hZs
  ext Γ hΓ
  rw [Measure.map_apply m1 hΓ, Measure.map_apply m2 hΓ]
  obtain ⟨Γ'', hΓ'', hEq⟩ := (MeasurableSpace.measurableSet_comap).1 (hF hΓ)
  have key : ∀ y, IsRegPath y → (y ∈ Γ'' ↔ F y ∈ Γ) := fun y hy => by
    have := Set.ext_iff.1 hEq ⟨y, hy⟩
    simpa using this
  have e1 : (fun ω => F (Y ω)) ⁻¹' Γ = Y ⁻¹' Γ'' := by
    ext ω; exact (key _ (hYr ω)).symm
  have e2 : (fun ω => F (Z ω)) ⁻¹' Γ = Z ⁻¹' Γ'' := by
    ext ω; exact (key _ (hZr ω)).symm
  rw [e1, e2, ← Measure.map_apply hY hΓ'', ← Measure.map_apply hZ hΓ'', hlaw]

/-- The law of the driven pair equals the law of the pair of the canonical SRW. -/
theorem stepPair_law {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Y : Ω → PathSpace d} (hY : IsSRW P Y)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) {Pd : Measure Ω'} {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) :
    P.map (fun ω => stepPair β (stepShift a (Y ω))) =
      Pd.map (fun ω => stepPair β (canonical d N₀ ω)) := by
  have hlaw : P.map (fun ω => stepShift a (Y ω)) = Pd.map (canonical d N₀) :=
    (hY.map_theta a).trans ((IsSRW.map_eq_model hY).trans
      (IsSRW.map_eq_model (canonical_isSRW hN₀)).symm)
  exact map_comp_of_regular' ((measurable_theta a).comp hY.1) (measurable_canonical hN₀.measurable)
    (fun ω => (stepShift_mem (hYp ω) a).toIsRegPath) (fun ω => walkPath_isRegPath (N₀ ω)) hlaw
    (stepPair β) (measurable_stepPair β)

theorem measurable_stepPair_comp {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → PathSpace d} (hX : Measurable X) (hr : ∀ ω, IsRegPath (X ω)) :
    Measurable fun ω => stepPair β (X ω) := by
  have h : Measurable fun ω => (⟨X ω, hr ω⟩ : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}) :=
    hX.subtype_mk
  have h2 := (measurable_stepPair (d := d) β).comp h
  exact h2

/-- The driven event is the preimage of `B`. -/
theorem driven_event_eq {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} {Y : Ω → PathSpace d}
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) (T h : ℝ) (n : ℕ) (B : Set (PairSp d))
    (hB : ∀ p, PairRC p → (p ∈ B ↔ PairBad β T h n p)) :
    {ω | ¬ WinOK T h n (stepRelaxedSet β (stepWr β a Y ω) (stepAr β a Y ω))} =
      (fun ω => stepPair β (stepShift a (Y ω))) ⁻¹' B := by
  ext ω
  have hrc : PairRC (stepPair β (stepShift a (Y ω))) :=
    ⟨fun s => (step_pair_rc (stepShift_mem (hYp ω) a) s).1,
      fun s => (step_pair_rc (stepShift_mem (hYp ω) a) s).2⟩
  exact (hB _ hrc).symm

/-- The environment pair. -/
noncomputable def envPair {d : ℕ} {β : ℝ} [Fact (0 < β)] (ν : Measure (ℕ × RingSpace d β)) :
    PairSp d :=
  (fun t : ℝ≥0 => regenWalk (fun k => cycSlice k ν) (t : ℝ),
    fun t : ℝ≥0 => regenStart (fun k => cycSlice k ν) (t : ℝ))

theorem envPair_bad {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace d β)}
    (T h : ℝ) (n : ℕ) :
    PairBad β T h n (envPair ν) ↔ ¬ WinOK T h n
      {s : ℝ | 0 ≤ s ∧ IsRelaxedTime (fun k => cycSlice k ν) s} := by
  have hset : {s : ℝ | 0 ≤ s ∧ IsRelaxedTime (fun k => cycSlice k ν) s} =
      {t : ℝ | 0 ≤ t ∧ IsRelaxedTimeWrt β (stepExt (envPair ν).1) ((envPair ν).2 t.toNNReal) t} := by
    ext t
    refine and_congr_right fun ht => ?_
    have hst : ((envPair ν).2 t.toNNReal) = regenStart (fun k => cycSlice k ν) t := by
      show regenStart (fun k => cycSlice k ν) ((t.toNNReal : ℝ≥0) : ℝ) = _
      rw [Real.coe_toNNReal _ ht]
    rw [hst]
    unfold IsRelaxedTime
    exact (ind_isRelaxedTimeWrt_congr (fun s hs => by
      simp [stepExt, envPair, Real.coe_toNNReal _ hs]) ENNReal.toReal_nonneg ht).symm
  unfold PairBad
  rw [hset]

theorem envPair_rc {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace d β)}
    (hg : CycGood ν) : PairRC (envPair ν) :=
  ⟨fun s => (regen_pair_rc hg s).1, fun s => (regen_pair_rc hg s).2⟩

theorem aemeasurable_envPair {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
    {Pe : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe) :
    AEMeasurable (fun ω => envPair (N ω)) Pe := by
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  have hmenv := (regPlan d β).measurable_envFinalOr CycRec.empty
  have hm : Measurable fun ω => (regRecProc ((regPlan d β).envFinalOr CycRec.empty (N ω)),
      regRecAlphaProc ((regPlan d β).envFinalOr CycRec.empty (N ω))) :=
    (measurable_regRecProc.prodMk measurable_regRecAlphaProc).comp (hmenv.comp hN.1)
  refine hm.aemeasurable.congr ?_
  filter_upwards [ae_cycGood hN] with ω h2
  refine Prod.ext ?_ ?_
  · funext t
    rw [(regPlan d β).envFinalOr_of_good _ h2]
    exact regRecWalk_envFinal_eq_regenWalk h2 t
  · funext t
    rw [(regPlan d β).envFinalOr_of_good _ h2]
    exact regRecAlpha_envFinal h2 t

/-- **Transfer of ES22 Theorem 6.1 to the driven picture.** The environment form of Theorem 6.1 gives
`StepEs61`. -/
theorem stepEs61_of_envEs61 {d : ℕ} {c6 : ℝ} {β6 : ℕ → ℝ} (H : StepEs61Env d c6 β6) :
    StepEs61 d c6 β6 := by
  intro n₁ h8 β _ n t₀ hβ hR Ω _ P Y hY hYp a
  obtain ⟨B, hBm, hB⟩ := exists_pairBad_set (d := d) β (indScale t₀ n)
    (indScale t₀ n ^ heavyEps d) n
  obtain ⟨Ωe, _, Pe, N, hPe, hN, -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  obtain ⟨Ω', _, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hEnv := H n₁ h8 β n t₀ hβ hR Ωe Pe N hN
  have hlawE : Pe.map (fun ω => envPair (N ω)) =
      Pd.map (fun ω => stepPair β (canonical d N₀ ω)) :=
    regen_pair_law_env_cut_map hN hN₀ (T := id) measurable_id
  have hlawD := stepPair_law (β := β) hY hYp a hN₀
  have hgd : Measurable fun ω => stepPair β (stepShift a (Y ω)) :=
    measurable_stepPair_comp (β := β) ((measurable_theta a).comp hY.1)
    (fun ω => (stepShift_mem (hYp ω) a).toIsRegPath)
  have hcan := measurable_stepPair_comp (β := β) (measurable_canonical hN₀.measurable)
    (fun ω => walkPath_isRegPath (N₀ ω))
  have hfe_ae := aemeasurable_envPair hN
  have hae : (fun ω => envPair (N ω)) ⁻¹' B =ᵐ[Pe] {ω | ¬ WinOK (indScale t₀ n)
      (indScale t₀ n ^ heavyEps d) n {s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s}} := by
    filter_upwards [ae_cycGood hN] with ω hg
    exact propext ((hB _ (envPair_rc hg)).trans (envPair_bad _ _ n))
  have hchain : P ((fun ω => stepPair β (stepShift a (Y ω))) ⁻¹' B) =
      Pe {ω | ¬ WinOK (indScale t₀ n) (indScale t₀ n ^ heavyEps d) n
        {s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s}} := by
    rw [← Measure.map_apply hgd hBm, hlawD, ← hlawE, Measure.map_apply_of_aemeasurable hfe_ae hBm]
    exact measure_congr hae
  rw [measureReal_def, driven_event_eq hYp a _ _ n B hB, hchain]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) hEnv

end ElboimSly.Paper.Step

end
