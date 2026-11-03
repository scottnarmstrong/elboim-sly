/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Ae
public import ElboimSly.Paper.Escape.ResampleTower
public import Mathlib

/-!
# ES22 Claim 5.7, with the numerical thresholds as explicit hypotheses

ES22 Claim 5.7.

`es5_7_cond`: for the plan `𝒫₅(B, β', i)`, the stopping time `S₂ = Λ_{I+1}` and the set of
environments `exitSet` (the event `{r_i ≤ 4^{j-1}, W_i^←(r_i) ∈ F_B}`):
`P(exitSet | ℱ^{(i)}_{S₂}) ≥ c` almost surely, where `c` is at most
`c₅₇ - e^{-n_T²} - ε_far - ε_av` (the error terms of the proof of the claim).

The hypotheses are the thresholds of the proof of ES22 Claim 5.7 (levels, `L₇`, `t₇`,...) and the
counting bound `hcount` for the avoided set `A₇` (vertices visited by an explored walk (b) and density of the explored walks around p_i).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Brownian ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

theorem es5_7_cond (hd : 5 ≤ k + 2) :
    ∃ C₄₃ C₄₂ : ℝ, 0 < C₄₃ ∧ 0 < C₄₂ ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
        {Pr : Measure Ω} {N N' N'' : Ω → Measure (CycS ℕ (k + 2) β)},
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        IsPoissonPointProcess N' (cycIntensity ℕ (k + 2) β) Pr →
        IsPoissonPointProcess N''
          ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr →
        Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr →
        Indep (MeasurableSpace.comap N' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr →
        Indep (MeasurableSpace.comap N'' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
            cycNull Pr) Pr →
        𝒢₀ ≤ mΩ → ∀ (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β),
        1 ≤ i → i ≤ escIstar n (escJ n) → 2 ≤ n → (n : ℝ) ^ 20 ≤ 2 ^ escJ n → 4 ≤ escJ n →
        16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n →
        (4 : ℝ) ^ n₀ < 4 ^ escJ n → (4 : ℝ) ^ escJ n ≤ 4 ^ n →
        ((4 : ℝ) ^ escJ n) ^ indThetaH < (2 : ℝ) ^ escJ n / 64 →
        ∀ {S : ℝ≥0}, (S : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2 / 4 → 0 < S → (S : ℝ) ≤ 4 ^ n →
        ∀ {t7 L7 : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ t7 → t7 ≤ (4 : ℝ) ^ n → t7 ^ indThetaH ≤ L7 + 1 →
        L7 + 1 ≤ t7 ^ (1 / 2 : ℝ) → (4 : ℝ) ^ (n₀ + 1) ≤ L7 → L7 ≤ (4 : ℝ) ^ n →
        0 ≤ C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2) →
        0 ≤ C₄₂ * L7 ^ (-(1 : ℝ) / 30) →
        max (Real.log β) 10 ≤ L7 + 1 →
        t7 + 4 * (L7 + 1) ^ 2 * Real.log (L7 + 1) ^ 2 < β →
        L7 + 1 < (n : ℝ) ^ 17 / 6 - 2 →
        (∀ ν : Measure (CycS ℕ (k + 2) β), CycGood ν → ∀ r : ℝ, L7 ≤ r →
          (({y | y ∈ avoidSet (escPoint n (escJ n) u i) L7 (ent5 n tn u β' i hlog ν)
              (escIstar n (escJ n)) ∧ ‖y - escPoint n (escJ n) u i‖ ≤ r} : Set (EscV k)).ncard : ℝ)
            ≤ r ^ (8 / 3 : ℝ)) →
        ∀ {c : ℝ≥0∞}, c ≤ ENNReal.ofReal (c57 (k + 2)) -
          ENNReal.ofReal (Real.exp (-((avoidLevel ((4 : ℝ) ^ escJ n) : ℕ) : ℝ) ^ 2)) -
          ENNReal.ofReal (C₄₃ * (L7 + 1) ^ (k + 2 - 2) * t7 ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2)) -
          ENNReal.ofReal (C₄₂ * L7 ^ (-(1 : ℝ) / 30)) →
        ∀ᵐ ω ∂Pr, c ≤ resPhi (plan5 n β tn u β' i hlog) Pr N
          (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 1))
          (exitSet (β := β) (escJ n) u S
            (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2))) ω := by
  obtain ⟨C₄₃, C₄₂, hC43, hC42, Hslice⟩ := slice_prob (k := k) hd
  refine ⟨C₄₃, C₄₂, hC43, hC42, ?_⟩
  intro β _ n₀ n t₀ hp Ω 𝒢₀ mΩ Pr N N' N'' hN hN' hN'' hI1 hI2 hI3 h𝒢 tn u β' i hlog hi1 hiI hn
    hj1 hj4 hIlam hT1 hT2 hε S hS hS0 hS4 t7 L7 ht71 ht72 ht7L hLt hL71 hL72 hεf hεa hL7
    hβ hnL hcount c hc
  have := hN.isProbabilityMeasure
  set P := plan5 n β tn u β' i hlog with hP
  set I := escIstar n (escJ n) with hI
  have hPfin : PlanFin P := plan5_planFin n β tn u β' i hlog
  have hKeq : P.K = ((I + 2 : ℕ) : ℕ∞) := rfl
  have hKpos : 0 < P.K := by rw [hKeq]; exact_mod_cast Nat.succ_pos _
  have hk1 : ((I + 1 : ℕ) : ℕ∞) < P.K := by rw [hKeq]; exact_mod_cast Nat.lt_succ_self _
  have hk1' : ((I + 1 : ℕ) : ℕ∞) ≤ P.K := hk1.le
  have hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) (lamT P N (I + 1)) :=
    isStoppingTime_lam 𝒢₀ P hN.measurable h𝒢 Pr hPfin hk1
  have hfin : ∀ ω, lamT P N (I + 1) ω ≠ ⊤ := fun ω => lamT_ne_top P hPfin ω hk1'
  have hfin1 : Pr {ω | lamT P N (I + 1) ω ≠ ⊤} = 1 := by
    have : {ω | lamT P N (I + 1) ω ≠ ⊤} = univ := by ext ω; simp [hfin ω]
    rw [this, measure_univ]
  have hδ : Measurable[hT.measurableSpace]
      (fun _ : Ω => ((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : Ω → CycData ℕ (k + 2)) :=
    measurable_const
  -- the random set `A₇` is `ℱ_{S₂}`-measurable
  have hZm : Measurable[hT.measurableSpace] (fun ω => recAvoid P.junk (escPoint n (escJ n) u i) L7 I
      (cycRecStop P (cycNgood N) (lamT P N (I + 1)) ω)) := by
    have h1 := (cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hKpos h𝒢 hT).2.1
    exact (measurable_recAvoid P.junk (escPoint n (escJ n) u i) L7 I).comp h1
  -- the lower bound on every slice
  have hslice : ∀ ω, c ≤ Pr {ω' | (recAvoid P.junk (escPoint n (escJ n) u i) L7 I
      (cycRecStop P (cycNgood N) (lamT P N (I + 1)) ω), regenW N'' ω') ∈
        setS β n (escJ n) u i S t7 L7} := by
    intro ω
    set ν := cycNgood N ω with hν
    have hνgood : CycGood ν := cycGood_cycNgood N ω
    have hE : ∀ m, 1 ≤ m → m ≤ I →
        (cycRecStop P (cycNgood N) (lamT P N (I + 1)) ω).coord P.junk m =
          ent5 n tn u β' i hlog ν m := by
      intro m _ hm
      exact coord_trunc_lam hPfin hνgood hk1' (Nat.lt_succ_of_le hm)
    have hpred : recAvoid P.junk (escPoint n (escJ n) u i) L7 I
        (cycRecStop P (cycNgood N) (lamT P N (I + 1)) ω) =
        fun y => y ∈ avoidSet (escPoint n (escJ n) u i) L7 (ent5 n tn u β' i hlog ν) I := by
      funext y
      exact propext (recAvoid_iff P.junk _ _ _ _ _ hE y)
    rw [hpred]
    refine hc.trans (Hslice β n₀ n t₀ hp hN (hN'' : IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr) u hi1 hiI hn hj1 (by omega) hIlam hT1 hT2
      hε hS ht71 ht72 ht7L hLt hL71 hL72 hεf hεa _ (fun y hy => hy.1) (hcount ν hνgood))
  have ht7 : 0 ≤ t7 := le_trans (by positivity) ht71
  have hae := c57_ae 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢 tn u β' i hlog ⟨hi1, hiI⟩ hn hj4 hIlam hS hS0
    hS4 ht7 hL7 hβ hnL
  set X := exitSet (β := β) (escJ n) u S
    (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)) with hX
  have hXm : MeasurableSet X := measurableSet_exitSet _ _ _ _
  have hmain : ∀ {A : Set Ω}, MeasurableSet[hT.measurableSpace] A →
      c * Pr A ≤ Pr (A ∩ {ω | N ω ∈ X}) := by
    intro A hA
    have hfr := plan_regen_freeze P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hKpos h𝒢 hT hfin hδ hZm hA
      (measurableSet_setS β n (escJ n) u i S t7 L7) (q := c) (fun ω _ => hslice ω)
    refine hfr.trans (measure_mono_ae ?_)
    filter_upwards [hae] with ω h hmem
    exact ⟨hmem.1, h hmem.2⟩
  obtain ⟨hmB, hBint⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hKpos h𝒢 hT hfin1 hXm
  have hle := hT.measurableSpace_le
  refine ae_le_of_setLIntegral_le_sub hle Pr (f := fun _ => c) measurable_const hmB ?_
  intro A hA
  rw [setLIntegral_const]
  have h := hBint hA
  have h' : ∫⁻ ω in A, resPhi P Pr N (lamT P N (I + 1)) X ω ∂Pr = Pr (A ∩ {ω | N ω ∈ X}) :=
    h.symm
  rw [h']
  exact hmain hA

end ElboimSly.Paper.Escape
