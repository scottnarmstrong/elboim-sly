/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Inner
public import ElboimSly.Paper.Escape.Es53Num
public import ElboimSly.Foundations.Cyclic.CycPlanCoupling
public import Mathlib

/-!
# ES22 Lemma 5.3

ES22 Lemma 5.3.  Under (S1)–(S2) with `β ≥ β_{53}(d, n₀)`: for every admissible block `B`,
every `β'` and `i ≤ I`, `P(𝒜_i | 𝒢_{i-1}) ≥ c_{53} = c_line/2`, i.e.
`c_{53} P(G) ≤ P(G ∩ 𝒜_i)` for every `G ∈ 𝒢_{i-1} = ℱ_{Λ_{i-1}}`.

Here `𝒜_i = {τ_i = 4^n}` is expressed through the plan `𝒫_𝒜`: `τ_i` is the length of the entry
`i - 1` of its final record, and `𝒢_{i-1}` is the stopped σ-algebra of the joint exploration
filtration at the stopping time `Λ_{i-1} = escLam`.  The stopped fresh environment is the `Ñ_T` of
Plan-level coupling after a stopping time; its walk `W'_i - p_i` is not regenerated, but is compared with the
regenerated walk through the first piece (`prob_envWalk_ge`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

theorem hlog_of_params {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ}
    (hp : Es4Params d β n₀ n t₀) : 1 < Real.log β := by
  have h1 : (10 : ℝ) ^ 14 ≤ β := hp.beta_sigma
  have : Real.exp 1 < β := by
    have := Real.exp_one_lt_d9
    linarith [show (10 : ℝ) ^ 14 = 100000000000000 by norm_num]
  exact (Real.lt_log_iff_exp_lt (lt_of_lt_of_le (Real.exp_pos 1) this.le)).2 this

theorem inner_bound {β : ℝ} [Fact (0 < β)] {n₀ n m₁ nD : ℕ} {t₀ : ℝ}
    (hk : 3 ≤ k) {CB CB' CC CD cD : ℝ}
    (hJb : ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} (_hp : Es4Params (k + 2) β n₀ n t₀)
        {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}
        (_hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
        (_hn53 : n53 (k + 2) ≤ n) (u : Fin (k + 2) → ℤ) {i : ℕ} (_hi1 : 1 ≤ i)
        (_hiI : i ≤ escIstar n (escJ n)) (_hIn : escIstar n (escJ n) ≤ n ^ 3)
        (_hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n) (_hj2 : 2 ≤ escJ n)
        (_hT1 : (4 : ℝ) ^ (n₀ + 1) ≤ (escJ n : ℝ) * 4 ^ escJ n)
        (_hT2 : (escJ n : ℝ) * 4 ^ escJ n ≤ 4 ^ n)
        (_hε1 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ (n : ℝ) ^ 17 / 30)
        (_hε2 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ 3 * (2 : ℝ) ^ escJ n / 40)
        {m₁ : ℕ} (_hm₁ : n₀ + 1 ≤ m₁)
        (_hθB : ∀ m : ℕ, 1 ≤ m → ((4 : ℝ) ^ m) ^ indThetaH ≤ 2 ^ (m + 3) / m)
        (_hθB' : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ 2 ^ escJ n)
        (A : Set (Fin (k + 2) → ℤ)) {L : ℝ} (_hL1 : (4 : ℝ) ^ (n₀ + 1) ≤ L)
        (_hL2 : L ≤ (4 : ℝ) ^ n)
        (_hA1 : ∀ z ∈ A, L ≤ ‖z - escPoint n (escJ n) u i‖)
        (_hA2 : ∀ r : ℝ, L ≤ r →
          ((A ∩ {z | ‖z - escPoint n (escJ n) u i‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)),
        ENNReal.ofReal (cline (k + 2)) -
          ENNReal.ofReal (Real.exp (-((avoidLevel ((escJ n : ℝ) * 4 ^ escJ n) : ℕ) : ℝ) ^ 2)) -
          errB CB k m₁ n -
          ENNReal.ofReal (CB' * ((2 : ℝ) ^ escJ n) ^ k *
            ((escJ n : ℝ) * 4 ^ escJ n) ^ (-(k : ℝ) / 2)) -
          ENNReal.ofReal (CC * L ^ (-(1 : ℝ) / 30)) - errD CD cD m₁ n ≤
        Pr {ω | EsJ n m₁ (escJ n) (escIstar n (escJ n)) u i A
          (absPath (escPoint n (escJ n) u i) N ω)})
    (hp : Es4Params (k + 2) β n₀ n t₀) (hnum : Es53Num k n₀ n m₁ nD β CB CB' CC CD cD)
    {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr) {u : Fin (k + 2) → ℤ}
    (hadm : EscAdmissible (escJ n) u) {b : ℕ} {m : ℕ} (hm : m < escIstar n (escJ n))
    (hlog : 1 < Real.log β) (ν : Measure (CycS ℕ (k + 2) β)) (hν : CycGood ν)
    (hdens : escVneG n (escJ n) β (escIstar n (escJ n)) u (escWalkE n u b ν)
      (escBlockMinus (escJ n) u) (escTauE n u b hlog ν) (m + 1) ⊆
        {y | (n : ℝ) ^ 17 / 6 - 2 < ‖y - escPoint n (escJ n) u (m + 1)‖} ∧
      ∀ r : ℝ, (n : ℝ) ^ 17 / 7 ≤ r →
        ((escVneG n (escJ n) β (escIstar n (escJ n)) u (escWalkE n u b ν)
          (escBlockMinus (escJ n) u) (escTauE n u b hlog ν) (m + 1) ∩
            {y | ‖y - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) / 2) :
    ENNReal.ofReal (cline (k + 2) / 2) ≤
      Pr {ω' | EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1)
        ({0} ∪ escVisNbr n u b hlog ν m)
        (fun q => envWalk (N ω') (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true) q)} := by
  obtain ⟨hA1, hA2⟩ := A_density (n₀ := n₀) hν hm hadm hnum.hj2 hnum.hj1 hnum.hn2 hnum.hIlam
    hnum.hL1 hnum.hL3 hdens.1 hdens.2
  have hmI : 1 ≤ m + 1 ∧ m + 1 ≤ escIstar n (escJ n) := ⟨by omega, Nat.succ_le_of_lt hm⟩
  have h1 := hJb hp hN hnum.hn53 u hmI.1 hmI.2 hnum.hIn hnum.hj1 hnum.hj2 hnum.hT1 hnum.hT2
    hnum.hε1 hnum.hε2 hnum.hm₁ hnum.hθB hnum.hθB' ({0} ∪ escVisNbr n u b hlog ν m) hnum.hL1
    hnum.hL2 hA1 hA2
  have h2 := prob_envWalk_ge hk hN (n := n) (m₁ := m₁) (j := escJ n)
    (I := escIstar n (escJ n)) u (m + 1) (b : ℝ) ({0} ∪ escVisNbr n u b hlog ν m)
    (by have := hnum.hm8; omega) hnum.hm1n
    (hnum.hm1b.trans (Real.log_le_self (Fact.out : 0 < β).le)) hnum.hT2
  exact hnum.herr.trans (h1.trans h2)

theorem es5_3 (hk : 3 ≤ k) :
    ∃ β53 : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
      {𝒢₀ : MeasurableSpace Ω} [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
      {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
      (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N'), β53 n₀ ≤ β →
      ∀ (u : Fin (k + 2) → ℤ), EscAdmissible (escJ n) u → ∀ (b : ℕ) {m : ℕ},
      m < escIstar n (escJ n) →
      ∃ hT : IsStoppingTime (cycMultiFilt (planA n β u b (hlog_of_params hS.params)) 𝒢₀
          hS.space.ppp.measurable hS.space.le Pr)
          (escLam n u b (hlog_of_params hS.params) N m),
        ∀ G : Set Ω, MeasurableSet[hT.measurableSpace] G →
          ENNReal.ofReal (cline (k + 2) / 2) * Pr G ≤
            Pr (G ∩ {ω | (escEntry n u b (hlog_of_params hS.params) (cycNgood N ω) m).len =
              (4 : ℝ≥0∞) ^ n}) := by
  obtain ⟨CB, CB', CC, CD, cD, hCB, hCB', hCC, hCD, hcD, hJb⟩ := prob_J_bound (k := k) hk
  obtain ⟨nD, hnD4, hD⟩ := escDensityG k
  have key := fun n₀ : ℕ => es53_num k hk nD CB CB' CC CD cD hCB hCB' hCC hCD hcD n₀
  choose β53 hβ53 using key
  refine ⟨β53, ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS hβ u hadm b m hm
  obtain ⟨m₁, hnum⟩ := hβ53 n₀ hS.params hβ
  set hlog := hlog_of_params hS.params with hhlog
  have hN := hS.space.ppp
  have hN' := hS.space.ppp'
  have h𝒢 := hS.space.le
  have hI1 := hS.space.indep
  have hI2 := hS.space.indep'
  have := hN.isProbabilityMeasure
  set P := planA n β u b hlog with hP
  have hK : 0 < P.K := by
    have hK' : P.K = ((escIstar n (escJ n) : ℕ) : ℕ∞) := rfl
    rw [hK']
    exact_mod_cast Nat.zero_lt_of_lt hm
  have hT := isStoppingTime_escLam (u := u) (b := b) (hlog := hlog) 𝒢₀ hN h𝒢 hm
  refine ⟨hT, fun G hG => ?_⟩
  have hGm : MeasurableSet G := hT.measurableSpace_le _ hG
  set T := escLam n u b hlog N m with hTdef
  have hTfin : ∀ ω, T ω ≠ ⊤ := fun ω => WithTop.coe_ne_top
  have hTset : {ω | T ω ≠ ⊤} = univ := by ext ω; simp [hTfin ω]
  have hTfin1 : Pr {ω | T ω ≠ ⊤} = 1 := by rw [hTset]; exact measure_univ
  set δ : CycData ℕ (k + 2) := (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true) with hδ
  have hδm : Measurable[hT.measurableSpace] (fun _ : Ω => δ) := measurable_const
  obtain ⟨-, hlaw, -⟩ := cyc_plan_coupling.{0} P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hδm
  have hagree := cyc_plan_coupling_agree P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT (fun _ => δ)
  obtain ⟨-, hrec, -, -, -, -, h7, -, -⟩ := cyc_multi_exploration_a P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT
  have hgoodN := CycSchemeEnv.ae_cycGood' hN
  have hgoodTilde : ∀ᵐ ω ∂Pr,
      CycGood (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) := by
    have hFm : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν} :=
      measurableSet_cycGood.compl
    have h0 := h7 hTfin1 MeasurableSet.univ hFm
    have h1 : (Pr.map N) {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν} = 0 := by
      rw [Measure.map_apply hN.measurable hFm]
      exact ae_iff.1 hgoodN
    rw [h1, mul_zero, univ_inter] at h0
    have : ∀ᵐ ω ∂Pr, ω ∉ {ω | tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω ∈
        {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν}} := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [this] with ω hω
    simpa using hω
  -- measurability of `A`
  have hAm : ∀ z : Fin (k + 2) → ℤ,
      MeasurableSet[hT.measurableSpace] {ω | z ∈ escA n u b hlog N m ω} := by
    intro z
    have : {ω | z ∈ escA n u b hlog N m ω} = {_ω | z = 0} ∪
        (cycRecStop P (cycNgood N) T) ⁻¹' {ρ | visPred m P.junk ρ z} := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_preimage]
      exact escA_iff N hm ω z
    rw [this]
    exact (@MeasurableSet.const Ω hT.measurableSpace _).union
      (hrec (measurableSet_visPred m P.junk z))
  -- the set `S`
  have hRm : MeasurableSet {y : ℝ≥0 → Fin (k + 2) → ℤ |
      EsB n m₁ (escPoint n (escJ n) u (m + 1)) y ∧ EsB' n (escJ n) (escPoint n (escJ n) u (m + 1)) y ∧
        EsD n m₁ y ∧ EsG n (escJ n) (escIstar n (escJ n)) u (m + 1) y} := by
    simpa [zero_add] using measurableSet_EsRest n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1) 0
  set S : Set (Ω × (ℝ≥0 → Fin (k + 2) → ℤ)) := {q | q.1 ∈ G ∧
    EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1) (escA n u b hlog N m q.1) q.2} with hSdef
  have hSm : MeasurableSet[hT.measurableSpace.prod inferInstance] S := by
    have e : S = (G ×ˢ {y : ℝ≥0 → Fin (k + 2) → ℤ |
        EsB n m₁ (escPoint n (escJ n) u (m + 1)) y ∧
          EsB' n (escJ n) (escPoint n (escJ n) u (m + 1)) y ∧
          EsD n m₁ y ∧ EsG n (escJ n) (escIstar n (escJ n)) u (m + 1) y}) ∩
        {q | EsC n (escA n u b hlog N m q.1) q.2} := by
      ext q
      simp only [hSdef, EsJ, mem_ofPred_eq, mem_inter_iff, mem_prod]
      tauto
    rw [e]
    refine MeasurableSet.inter (@MeasurableSet.prod Ω _ hT.measurableSpace _ G _ hG hRm) ?_
    have e2 : {q : Ω × (ℝ≥0 → Fin (k + 2) → ℤ) | EsC n (escA n u b hlog N m q.1) q.2} =
        (⋃ q' ∈ qSet 0 (tn ((4 : ℝ) ^ n)), ⋃ z : Fin (k + 2) → ℤ,
          ({ω | z ∈ escA n u b hlog N m ω} ×ˢ {y : ℝ≥0 → Fin (k + 2) → ℤ | y q' = z}))ᶜ := by
      ext q
      simp only [EsC, mem_ofPred_eq, mem_compl_iff, mem_iUnion, mem_prod, exists_prop]
      constructor
      · rintro h ⟨q', hq', z, hz1, hz2⟩
        exact h ⟨q', hq', by rw [hz2]; exact hz1⟩
      · rintro h ⟨q', hq', hmem⟩
        exact h ⟨q', hq', q.2 q', hmem, rfl⟩
    rw [e2]
    refine MeasurableSet.compl ?_
    exact MeasurableSet.biUnion (qSet_countable 0 _) fun q' _ => MeasurableSet.iUnion fun z =>
      @MeasurableSet.prod Ω _ hT.measurableSpace _ _ _ (hAm z)
        (show MeasurableSet {y : ℝ≥0 → Fin (k + 2) → ℤ | y q' = z} from
          (measurableSet_singleton z).preimage (measurable_pi_apply q'))
  have hF : Measurable[hT.measurableSpace.prod inferInstance]
      (S.indicator (fun _ => (1 : ℝ≥0∞))) :=
    Measurable.indicator (m := hT.measurableSpace.prod inferInstance)
      (f := fun _ => (1 : ℝ≥0∞))
      (@measurable_const ℝ≥0∞ _ _ (hT.measurableSpace.prod inferInstance) 1) hSm
  have key := hlaw hF
  rw [hTset, Measure.restrict_univ] at key
  have hmI : 1 ≤ m + 1 ∧ m + 1 ≤ escIstar n (escJ n) := ⟨by omega, Nat.succ_le_of_lt hm⟩
  -- the upper bound of the left side
  have hLHS : ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
      (ω, envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) δ) ∂Pr ≤
      Pr (G ∩ {ω | (escEntry n u b hlog (cycNgood N ω) m).len = (4 : ℝ≥0∞) ^ n}) := by
    refine (lintegral_mono_ae ?_).trans (lintegral_indicator_one_le _)
    filter_upwards [hgoodN, hgoodTilde, hagree] with ω hgN hgT hag
    by_cases hω : (ω, envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) δ) ∈ S
    · have hS1 : S.indicator (fun _ => (1 : ℝ≥0∞))
          (ω, envWalk (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω) δ) = 1 :=
        indicator_of_mem hω _
      obtain ⟨hωG, hJ⟩ := hω
      have hcng : cycNgood N ω = N ω := by unfold cycNgood; rw [ite_eq_left hgN]
      have hAi : (escEntry n u b hlog (cycNgood N ω) m).len = (4 : ℝ≥0∞) ^ n := by
        refine step_A (cycNgood N ω) (tildeMeasure N N' (cycRegionStop P (cycNgood N) T) ω)
          (cycGood_cycNgood N ω) hgT hm hnum.hm8 hnum.hm1n hnum.hm1a hnum.hm1b hnum.hβ hnum.hn2
          hnum.hj1 hnum.hIlam hnum.hT2 δ rfl ?_ hJ
        intro r hdisj s hs
        have h1 := hag (hTfin ω) r (Or.inr hdisj) s hs
        rw [hcng]
        exact h1
      have hmem : ω ∈ G ∩ {ω | (escEntry n u b hlog (cycNgood N ω) m).len = (4 : ℝ≥0∞) ^ n} :=
        ⟨hωG, hAi⟩
      rw [hS1, indicator_of_mem hmem]
      exact le_rfl
    · rw [indicator_of_notMem hω]
      exact bot_le
  -- the lower bound of the right side
  have hwalk : Measurable fun ν : Measure (CycS ℕ (k + 2) β) => envWalk ν δ := by
    refine measurable_pi_iff.2 fun s => ?_
    exact (measurable_pi_apply s).comp
      (measurable_envWalk.comp (measurable_id.prodMk (measurable_const (a := δ))))
  have hRHS : ENNReal.ofReal (cline (k + 2) / 2) * Pr G ≤
      ∫⁻ ω, ∫⁻ ν, S.indicator (fun _ => (1 : ℝ≥0∞)) (ω, envWalk ν δ) ∂(Pr.map N) ∂Pr := by
    calc ENNReal.ofReal (cline (k + 2) / 2) * Pr G =
        ∫⁻ ω, G.indicator (fun _ => ENNReal.ofReal (cline (k + 2) / 2)) ω ∂Pr :=
          (lintegral_indicator_const hGm _).symm
      _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        by_cases hωG : ω ∈ G
        · rw [indicator_of_mem hωG]
          set ν := cycNgood N ω with hν
          have hνg : CycGood ν := cycGood_cycNgood N ω
          have hQ : MeasurableSet {ν' : Measure (CycS ℕ (k + 2) β) |
              EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1) (escA n u b hlog N m ω)
                (envWalk ν' δ)} := by
            have := (measurableSet_EsJ_x n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1)
              (escA n u b hlog N m ω) 0).preimage hwalk
            simpa [zero_add] using this
          have hdens := hD (n := n) (j := escJ n) (β := β) (I := escIstar n (escJ n)) (u := u)
            (W := escWalkE n u b ν) (Bm := escBlockMinus (escJ n) u)
            (τ := escTauE n u b hlog ν) (i := m + 1)
            (escBefore_planA (hlog := hlog) hνg) hnum.hnD hnum.hβ hnum.hlb hnum.hj1 hnum.hj1'
            hnum.hIn hnum.hIlam hmI.1 hmI.2 (escWalkE_zero hνg) (escWalkE_nn hνg)
          have hin := inner_bound hk hJb hS.params hnum hN hadm hm hlog ν hνg hdens
          calc ENNReal.ofReal (cline (k + 2) / 2) ≤ _ := hin
            _ = (Pr.map N) {ν' | EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1)
                (escA n u b hlog N m ω) (envWalk ν' δ)} :=
                (Measure.map_apply hN.measurable hQ).symm
            _ = ∫⁻ ν', {ν' | EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1)
                (escA n u b hlog N m ω) (envWalk ν' δ)}.indicator (fun _ => (1 : ℝ≥0∞)) ν'
                ∂(Pr.map N) := (lintegral_indicator_one hQ).symm
            _ = _ := by
                refine lintegral_congr fun ν' => ?_
                by_cases hh : EsJ n m₁ (escJ n) (escIstar n (escJ n)) u (m + 1)
                    (escA n u b hlog N m ω) (envWalk ν' δ)
                · rw [indicator_of_mem (show ν' ∈ _ from hh),
                    indicator_of_mem (show (ω, envWalk ν' δ) ∈ S from ⟨hωG, hh⟩)]
                · rw [indicator_of_notMem (show ν' ∉ _ from hh),
                    indicator_of_notMem (show (ω, envWalk ν' δ) ∉ S from fun h => hh h.2)]
        · rw [indicator_of_notMem hωG]
          exact bot_le
  exact hRHS.trans (key.symm.le.trans hLHS)

end ElboimSly.Paper.Escape
