/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenLaw
public import ElboimSly.Foundations.Cyclic.CycRegenLawMeas
public import ElboimSly.Foundations.Cyclic.CycRegenEnvGlue
public import ElboimSly.Foundations.Cyclic.CycDrivenRegenMeas
public import ElboimSly.Foundations.Cyclic.CycRegenDrivenShift
public import Mathlib

/-!
# The regenerated walk together with its regeneration function: joint law

The constructions of the regenerated walk (i) = (iii), for the pair `(W_reg, α)`.

The constructions of the regenerated walk identifies the law of the regenerated walk of a Poisson environment with the law
of the regenerated walk `W^X_reg` driven by a canonical SRW `X`. The relaxed times of ES22 also
involve the regeneration function `α(t) = σ_{𝔑_t}`, which is not a function of the walk. Here the
same law transfer (`law_transfer`) is run with the functional `ρ ↦ (W_reg(ρ), α(ρ))` of the record:

* `regRecAlpha ρ t`: the last cumulative length `Λ_N ≤ t` of the record;
* `cum_cycFinal`: the cumulative lengths of a final record are the partial sums of the closing times;
* `regen_pair_law_env_cut_map`: for every measurable functional `T` of the pair of paths
  `(t ↦ W(t), t ↦ α(t))`, the environment picture and the driven picture give the same law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

/-- The regeneration function `α` of a record: the last `Λ_N ≤ t`. -/
noncomputable def regRecAlpha {I : Type*} (ρ : CycRec I d) (t : ℝ≥0) : ℝ≥0 :=
  (ρ.cum (gluedCount (fun k => ρ.cum k) t)).toNNReal

/-- `α` of a record, as a process with real values. -/
noncomputable def regRecAlphaProc {I : Type*} (ρ : CycRec I d) : ℝ≥0 → ℝ :=
  fun t => (regRecAlpha ρ t : ℝ)

theorem measurable_regRecAlpha {I : Type*} [MeasurableSpace I] [Nonempty (CycEntry I d)]
    (t : ℝ≥0) : Measurable fun ρ : CycRec I d => regRecAlpha ρ t := by
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  have hσ : ∀ n, Measurable fun ρ : CycRec I d => ρ.cum n := fun n => measurable_cum junk n
  exact measurable_index (measurable_gluedCount_of hσ t)
    (fun n => ENNReal.measurable_toNNReal.comp (hσ n))

theorem measurable_regRecAlphaProc {I : Type*} [MeasurableSpace I] [Nonempty (CycEntry I d)] :
    Measurable (regRecAlphaProc (I := I) (d := d)) :=
  measurable_pi_iff.2 fun t => (measurable_regRecAlpha t).coe_nnreal_real

namespace CycPlan

variable {I : Type*} [MeasurableSpace I] {β : ℝ} [Fact (0 < β)]
  (P : CycPlan I d β) (path : PathRule I d)

omit [Fact (0 < β)] in
/-- The cumulative lengths of the final record are the partial sums of the closing times. -/
theorem cum_cycFinal (hK : P.K = ⊤) (τ : ℕ → ℝ≥0∞)
    (hE1 : ∀ k, P.AllFin path k → (P.E path k).len = τ k) (k : ℕ) :
    (P.cycFinal path).cum k = partialSums τ k := by
  classical
  set ρ := P.cycFinal path with hρ
  have hnth := P.cycFinal_nth path hK
  induction k with
  | zero => simp [CycRec.cum, partialSums]
  | succ k ih =>
    rw [partialSums_succ, ← ih]
    unfold CycRec.cum
    rw [Finset.sum_range_succ]
    by_cases hA : P.AllFin path k
    · have hn : ρ.nth k = some (P.E path k) := by rw [hnth k, ite_eq_left hA]
      have : ρ.lenAt k = τ k := by
        show (ρ.nth k).elim 0 CycEntry.len = τ k
        rw [hn]; exact hE1 k hA
      rw [this]
    · have hT : partialSums τ k = ⊤ := P.partialSums_top_of_not_allFin path τ hE1 hA
      have h2 : ∑ i ∈ Finset.range k, ρ.lenAt i = ⊤ := by
        have := ih
        unfold CycRec.cum at this
        rw [this]; exact hT
      rw [h2]; simp

omit [Fact (0 < β)] in
/-- `α` of the final record, in terms of the partial sums of the closing times. -/
theorem regRecAlpha_cycFinal (hK : P.K = ⊤) (τ : ℕ → ℝ≥0∞)
    (hE1 : ∀ k, P.AllFin path k → (P.E path k).len = τ k) (t : ℝ≥0) :
    regRecAlpha (P.cycFinal path) t =
      (partialSums τ (gluedCount (partialSums τ) t)).toNNReal := by
  have hfun : (fun k => (P.cycFinal path).cum k) = partialSums τ :=
    funext (P.cum_cycFinal path hK τ hE1)
  unfold regRecAlpha
  rw [hfun, P.cum_cycFinal path hK τ hE1]

end CycPlan

section Alpha

variable {α : Type*} [MeasurableSpace α] {b : ℝ≥0}

theorem measurable_drivenRegenAlpha_at (hb : 0 < b) {X : α → CPath (Fin d → ℤ)}
    (hX : Measurable X) (t : ℝ≥0) :
    Measurable fun a => drivenRegenAlpha b (X a).fn t :=
  measurable_index (measurable_gluedCount hb hX t)
    (fun n => ENNReal.measurable_toNNReal.comp (measurable_drivenSigma hb hX n))

end Alpha

variable {β : ℝ} [Fact (0 < β)]

/-- Environment: `α` of the environment final record is `regenStart`. -/
theorem regRecAlpha_envFinal {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (t : ℝ≥0) :
    (regRecAlpha ((regPlan d β).envFinal ν) t : ℝ) =
      ElboimSly.regenStart (fun k => cycSlice k ν) (t : ℝ) := by
  have h := (regPlan d β).regRecAlpha_cycFinal
    (fun k ρ => envPath ν ((regPlan d β).start k ρ)) rfl
    (fun k => ElboimSly.cycTreg (cycSlice k ν)) (fun k _ => (regPlan_E_env hν k).1) t
  have h' : regRecAlpha ((regPlan d β).envFinal ν) t =
      (partialSums (fun k => ElboimSly.cycTreg (cycSlice k ν))
        (gluedCount (partialSums fun k => ElboimSly.cycTreg (cycSlice k ν)) t)).toNNReal := h
  rw [h', gluedCount_coe]
  unfold ElboimSly.regenStart ElboimSly.regenSigma
  rw [ENNReal.coe_toNNReal_eq_toReal]
  rfl

/-- Driven picture: `α` of the driven final record is `drivenRegenAlpha`, for a coincidence-free
driving path. -/
theorem regRecAlpha_drivenFinal_cut (X : CycPath d) (hX : X.1.fn ∈ CycCF β.toNNReal) (t : ℝ≥0)
    (h0 : X.1.fn 0 = 0) :
    regRecAlpha ((regPlan d β).drivenFinal (J := Unit) (fun _ _ => ()) (fun _ => X)) t =
      drivenRegenAlpha β.toNNReal X.1.fn t := by
  rw [drivenFinal_cut]
  have h := (regPlan d β).regRecAlpha_cycFinal (drivenCutRule β X) rfl (cutTau β.toNNReal X.1.fn)
    (fun k hk => (regen_cut_E X hX k hk).1) t
  rw [h, ← cutTimes_eq_partialSums]
  have hc : cutTimes β.toNNReal X.1.fn = drivenSigma β.toNNReal X.1.fn :=
    funext fun k => (cutTimes_eq_drivenSigma h0 k).1
  rw [hc]
  rfl

/-- Construction (iii), almost surely, for the pair `(W_reg, α)`. -/
theorem regen_cut_pair_ae {Ω' : Type*} [MeasurableSpace Ω'] {Pd : Measure Ω'}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) :
    ∀ᵐ Ñ ∂(Pd.map fun ω => drvUnit (N₀ ω)),
      (regRecProc ((regPlan d β).drivenFinal (J := Unit) (fun _ _ => ())
        (fun j => srwPath Ñ j)),
        regRecAlphaProc ((regPlan d β).drivenFinal (J := Unit) (fun _ _ => ())
          (fun j => srwPath Ñ j))) =
        (fun t => drivenRegenFrom β.toNNReal (srwPath Ñ ()).1.fn t,
          fun t => (drivenRegenAlpha β.toNNReal (srwPath Ñ ()).1.fn t : ℝ)) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have hWd : IsPoissonPointProcess (fun Ñ : Measure ((Dir d × Unit) × ℝ) => Ñ)
      (drvIntensity d Unit) (Pd.map fun ω => drvUnit (N₀ ω)) := (isPPP_drvUnit hN₀).isPPPLaw_map
  have hcf := ae_canonical_mem_cycCF (N := fun Ñ : Measure ((Dir d × Unit) × ℝ) =>
    subProcess (fun Ñ => Ñ) () Ñ) (subProcess_ppp (ι := Unit) hWd ()) β.toNNReal hb
  filter_upwards [regen_cut_ae (β := β) hN₀, hcf] with Ñ h1 h2
  have h0 : (srwPath Ñ ()).1.fn 0 = 0 := (walkPath_isDriving _).zero
  refine Prod.ext h1 (funext fun t => ?_)
  exact congrArg (fun x : ℝ≥0 => (x : ℝ))
    (regRecAlpha_drivenFinal_cut (srwPath Ñ ()) h2 t h0)

/-- **the constructions of the regenerated walk (i) = (iii), for the pair `(W_reg, α)`**, after a measurable functional
`T` of the pair of paths. -/
theorem regen_pair_law_env_cut_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pe : Measure Ω} {Pd : Measure Ω'} {N : Ω → Measure (ℕ × RingSpace d β)}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd)
    {γ : Type*} [MeasurableSpace γ]
    {T : (ℝ≥0 → Fin d → ℤ) × (ℝ≥0 → ℝ) → γ} (hT : Measurable T) :
    Pe.map (fun ω => T (fun t : ℝ≥0 =>
        ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ),
        fun t : ℝ≥0 => ElboimSly.regenStart (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ))) =
      Pd.map (fun ω => T (fun t : ℝ≥0 =>
        drivenRegenFrom β.toNNReal (canonical d N₀ ω) t,
        fun t : ℝ≥0 => (drivenRegenAlpha β.toNNReal (canonical d N₀ ω) t : ℝ))) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  have hNd := isPPP_drvUnit hN₀
  have hmenv := (regPlan d β).measurable_envFinalOr CycRec.empty
  have hΦ : Measurable fun ρ : CycRec ℕ d => (regRecProc ρ, regRecAlphaProc ρ) :=
    measurable_regRecProc.prodMk measurable_regRecAlphaProc
  have hB : Measurable fun Ñ : Measure ((Dir d × Unit) × ℝ) =>
      T (fun t => drivenRegenFrom β.toNNReal (srwPath Ñ ()).1.fn t,
        fun t => (drivenRegenAlpha β.toNNReal (srwPath Ñ ()).1.fn t : ℝ)) := by
    refine hT.comp (Measurable.prodMk ?_ ?_)
    · exact measurable_pi_iff.2 fun t => measurable_drivenRegenFrom_at hb
        (X := fun Ñ => (srwPath Ñ ()).1) (measurable_srwPath ()) t
    · exact measurable_pi_iff.2 fun t =>
        (measurable_drivenRegenAlpha_at hb (X := fun Ñ => (srwPath Ñ ()).1)
          (measurable_srwPath ()) t).coe_nnreal_real
  have key := law_transfer (jx := fun _ _ => ()) () (regPlan d β) (fun _ => measurable_const)
    hK_regPlan hN hNd (ae_cycGood hN) (Φ := T ∘ fun ρ => (regRecProc ρ, regRecAlphaProc ρ))
    (hT.comp hΦ)
    (A := fun ν => T (regRecProc ((regPlan d β).envFinalOr CycRec.empty ν),
      regRecAlphaProc ((regPlan d β).envFinalOr CycRec.empty ν)))
    (hT.comp (hΦ.comp hmenv)) hB
    (fun ν hν => by
      show T (regRecProc ((regPlan d β).envFinal ν), regRecAlphaProc ((regPlan d β).envFinal ν)) = _
      rw [(regPlan d β).envFinalOr_of_good _ hν])
    (by
      filter_upwards [regen_cut_pair_ae (β := β) hN₀] with Ñ h
      exact congrArg T h)
  have e1 : Pe.map (fun ω => T (fun t : ℝ≥0 =>
        ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ),
        fun t : ℝ≥0 => ElboimSly.regenStart (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ))) =
      Pe.map (fun ω => T (regRecProc ((regPlan d β).envFinalOr CycRec.empty (N ω)),
        regRecAlphaProc ((regPlan d β).envFinalOr CycRec.empty (N ω)))) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_cycGood hN] with ω h2
    refine congrArg T (Prod.ext ?_ ?_)
    · funext t
      rw [(regPlan d β).envFinalOr_of_good _ h2]
      exact (regRecWalk_envFinal_eq_regenWalk h2 t).symm
    · funext t
      rw [(regPlan d β).envFinalOr_of_good _ h2]
      exact (regRecAlpha_envFinal h2 t).symm
  rw [e1, ← key]
  refine Measure.map_congr (Filter.Eventually.of_forall fun ω => ?_)
  have hc : (srwPath (drvUnit (N₀ ω)) ()).1.fn = canonical d N₀ ω :=
    funext (srwPath_drvUnit_fn (N₀ ω))
  show T (fun t => drivenRegenFrom β.toNNReal (srwPath (drvUnit (N₀ ω)) ()).1.fn t,
      fun t => (drivenRegenAlpha β.toNNReal (srwPath (drvUnit (N₀ ω)) ()).1.fn t : ℝ)) = _
  rw [hc]

end ElboimSly.Cyclic

end
