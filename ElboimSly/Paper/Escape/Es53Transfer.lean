/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Prob
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingLaw
public import ElboimSly.Foundations.Concentration.GeometricEvents
public import ElboimSly.Foundations.Cyclic.CycFastPath
public import Mathlib

/-!
# From the regenerated walk to the cyclic walk of a fresh environment

ES22 Lemma 5.3 ("`W'_i = \tilde P` up to the first regeneration time of `W'_i - p_i`").

* `EsJ`: the event `ℬ ∩ ℬ' ∩ 𝒞 ∩ 𝒟 ∩ 𝒢` in countable form, and its measurability and locality;
* on `ℬ` the regenerated walk does not regenerate before `4^n`, so it equals the first piece, the
  cyclic walk `envWalk (N ω) (0, 0, 0, +1)`, on `[0, 4^n]` (`avoidPath_eq_envWalk`);
* `prob_envWalk_ge`: the cyclic walk of any fresh environment, started at `p`, satisfies `𝒥`
  with at least the probability of the regenerated walk (`law_envWalk`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Interchange ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `𝒥 = ℬ ∩ ℬ' ∩ 𝒞 ∩ 𝒟 ∩ 𝒢` for the path `y`. -/
def EsJ (n m₁ j I : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) (A : Set (Fin (k + 2) → ℤ))
    (y : ℝ≥0 → Fin (k + 2) → ℤ) : Prop :=
  EsB n m₁ (escPoint n j u i) y ∧ EsB' n j (escPoint n j u i) y ∧ EsC n A y ∧ EsD n m₁ y ∧
    EsG n j I u i y

theorem mem_qSet_le {a b q : ℝ≥0} (h : q ∈ qSet a b) : q ≤ b := by
  rcases h with ⟨-, h2, -⟩ | rfl
  · exact h2
  · exact le_rfl

theorem coe_le_of_le_tn {X : ℝ} (hX : 0 ≤ X) {q : ℝ≥0} (h : q ≤ tn X) : (q : ℝ) ≤ X := by
  have := NNReal.coe_le_coe.2 h
  rwa [tn, Real.coe_toNNReal _ hX] at this

theorem exists_qSet_congr {a b : ℝ≥0} {P Q : ℝ≥0 → Prop} (h : ∀ q ∈ qSet a b, (P q ↔ Q q)) :
    (∃ q ∈ qSet a b, P q) ↔ ∃ q ∈ qSet a b, Q q :=
  exists_congr fun q => and_congr_right fun hq => h q hq

theorem EsJ_congr {n m₁ j I : ℕ} {u : Fin (k + 2) → ℤ} {i : ℕ} {A : Set (Fin (k + 2) → ℤ)}
    (hjn : (j : ℝ) * 4 ^ j ≤ 4 ^ n) {y y' : ℝ≥0 → Fin (k + 2) → ℤ}
    (h : ∀ q : ℝ≥0, (q : ℝ) ≤ 4 ^ n → y q = y' q) :
    EsJ n m₁ j I u i A y ↔ EsJ n m₁ j I u i A y' := by
  have key : ∀ (X : ℝ) (a : ℝ≥0), 0 ≤ X → X ≤ 4 ^ n → ∀ q ∈ qSet a (tn X), y q = y' q :=
    fun X a hX hX4 q hq => h q ((coe_le_of_le_tn hX (mem_qSet_le hq)).trans hX4)
  have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
  unfold EsJ EsB EsB' EsC EsD EsG
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · refine forall_congr' fun m => imp_congr_right fun _ => imp_congr_right fun _ =>
      not_congr (exists_qSet_congr fun q hq => ?_)
    rw [key _ _ h4 le_rfl q hq]
  · refine not_congr (exists_qSet_congr fun q hq => ?_)
    rw [key _ _ h4 le_rfl q hq]
  · refine not_congr (exists_qSet_congr fun q hq => ?_)
    rw [key _ _ h4 le_rfl q hq]
  · refine forall_congr' fun m => imp_congr_right fun _ => imp_congr_right fun hm =>
      not_congr (exists_qSet_congr fun t ht => exists_qSet_congr fun s' hs => ?_)
    have hm4 : (4 : ℝ) ^ m ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hm
    rw [key _ _ (by positivity) hm4 t ht, key _ _ (by positivity) hm4 s' hs]
  · refine not_congr (exists_qSet_congr fun q hq => ?_)
    rw [key _ _ (by positivity) hjn q hq]

theorem envWalk_eq_cycWalk {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν)
    (δ : CycData ℕ (k + 2)) (s : ℝ≥0) :
    envWalk ν δ s = ElboimSly.cycWalk (envMeasure ν δ) δ.start (δ.sgn * δ.phase) (s : ℝ) := by
  have hg' : Good (cycSlice δ.copy ν) := hν δ.copy
  have hgm : Good (envMeasure ν δ) := good_envMeasure hg'
  unfold envWalk
  rw [ite_eq_left hν, envFn_eq_fwdTraj hg', cycWalk_of_nonneg hgm _ _ (NNReal.coe_nonneg s)]

theorem avoid_eq_envWalk_of_EsB {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {n m₁ : ℕ}
    (hRC : IsRCPath (fun q : ℝ≥0 => ElboimSly.regenWalk (fun l => cycSlice l ν) (q : ℝ)))
    (hm₁ : 1 ≤ m₁) (hm1n : m₁ ≤ n) (hβ : (4 : ℝ) ^ m₁ ≤ β) (p : Fin (k + 2) → ℤ)
    (hB : EsB n m₁ p (fun q => p + ElboimSly.regenWalk (fun l => cycSlice l ν) (q : ℝ))) :
    ∀ q : ℝ≥0, (q : ℝ) ≤ 4 ^ n →
      ElboimSly.regenWalk (fun l => cycSlice l ν) (q : ℝ) = envWalk ν (0, 0, 0, true) q := by
  have hβ0 : 0 < β := Fact.out
  set ν' : ℕ → Measure (RingSpace (k + 2) β) := fun l => cycSlice l ν with hν'
  have hg : ∀ l, Good (ν' l) := fun l => hν l
  have hT : (0 : ℝ) < 4 ^ n := by positivity
  have htreg : ENNReal.ofReal ((4 : ℝ) ^ n) < ElboimSly.cycTreg (ν' 0) := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨i, hi, hzero⟩ := exists_regenWalk_zero_of_treg_le hg hT hle
    rw [Finset.mem_Icc] at hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
    have hiT : (i : ℝ) * β ≤ 4 ^ n := by
      have := (Nat.le_floor_iff (by positivity)).1 hi.2
      rwa [le_div_iff₀ hβ0] at this
    have hs0 : 0 ≤ (i : ℝ) * β := by positivity
    set s : ℝ≥0 := ((i : ℝ) * β).toNNReal with hs
    have hsr : (s : ℝ) = i * β := Real.coe_toNNReal _ hs0
    have hy : IsRCPath (fun q : ℝ≥0 => p + ElboimSly.regenWalk ν' (q : ℝ)) := by
      intro t
      filter_upwards [hRC t] with u hu
      simp only [hu]
    have hab : tn ((4 : ℝ) ^ m₁) ≤ tn ((4 : ℝ) ^ n) :=
      Real.toNNReal_le_toNNReal (pow_le_pow_right₀ (by norm_num) hm1n)
    have hcon := forall_of_not_exists_qSet hy hab
      (P := fun v => ‖v - p‖ < 2 ^ (m₁ + 3) / m₁) (hB m₁ le_rfl hm1n) s
      (by
        refine Real.toNNReal_le_toNNReal ?_
        nlinarith)
      (Real.toNNReal_le_toNNReal hiT)
    apply hcon
    have h0 : ElboimSly.regenWalk ν' (s : ℝ) = 0 := by rw [hsr]; exact hzero
    simp only [h0, add_zero, sub_self, norm_zero]
    have : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
    positivity
  intro q hq
  have hqlt : (q : ℝ≥0∞) < ElboimSly.cycTreg (ν' 0) :=
    lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hq) htreg
  rw [regenWalk_of_lt_treg ν' hqlt, envWalk_eq_cycWalk hν]
  simp [envMeasure, CycData.sgn, CycData.phase, CycData.start, CycData.copy, CycData.fwd, hν']

theorem measurableSet_cyl2 (a b : ℝ≥0) (c : ℝ≥0 → ℝ≥0 → Prop)
    (R : (Fin (k + 2) → ℤ) → (Fin (k + 2) → ℤ) → Prop) :
    MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ | ∃ t ∈ qSet a b, ∃ s ∈ qSet a b, c t s ∧
      R (x t) (x s)} := by
  have : {x : ℝ≥0 → Fin (k + 2) → ℤ | ∃ t ∈ qSet a b, ∃ s ∈ qSet a b, c t s ∧ R (x t) (x s)} =
      ⋃ t ∈ qSet a b, ⋃ s ∈ qSet a b, ⋃ (_ : c t s), {x | R (x t) (x s)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [this]
  refine MeasurableSet.biUnion (qSet_countable a b) fun t _ =>
    MeasurableSet.biUnion (qSet_countable a b) fun s _ => MeasurableSet.iUnion fun _ => ?_
  have hm : Measurable fun x : ℝ≥0 → Fin (k + 2) → ℤ => (x t, x s) :=
    (measurable_pi_apply t).prodMk (measurable_pi_apply s)
  exact (MeasurableSet.of_discrete (s := {v : (Fin (k + 2) → ℤ) × (Fin (k + 2) → ℤ) |
    R v.1 v.2})).preimage hm

theorem measurableSet_EsRest (n m₁ j I : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ)
    (p₀ : Fin (k + 2) → ℤ) :
    MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ | EsB n m₁ (escPoint n j u i) (fun q => p₀ + x q) ∧
      EsB' n j (escPoint n j u i) (fun q => p₀ + x q) ∧ EsD n m₁ (fun q => p₀ + x q) ∧
      EsG n j I u i (fun q => p₀ + x q)} := by
  have hB : MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ |
      EsB n m₁ (escPoint n j u i) (fun q => p₀ + x q)} := by
    have : {x : ℝ≥0 → Fin (k + 2) → ℤ | EsB n m₁ (escPoint n j u i) (fun q => p₀ + x q)} =
        ⋂ m : ℕ, ⋂ (_ : m₁ ≤ m), ⋂ (_ : m ≤ n), {x : ℝ≥0 → Fin (k + 2) → ℤ |
          ∃ q ∈ qSet (tn ((4 : ℝ) ^ m)) (tn ((4 : ℝ) ^ n)),
            ‖p₀ + x q - escPoint n j u i‖ < 2 ^ (m + 3) / m}ᶜ := by
      ext x; simp [EsB]
    rw [this]
    exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      (measurableSet_cyl _ _ (fun v => ‖p₀ + v - escPoint n j u i‖ < 2 ^ (m + 3) / m)).compl
  have hB' : MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ |
      EsB' n j (escPoint n j u i) (fun q => p₀ + x q)} :=
    (measurableSet_cyl _ _ (fun v => ‖p₀ + v - escPoint n j u i‖ < 2 ^ j)).compl
  have hD : MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ | EsD n m₁ (fun q => p₀ + x q)} := by
    have : {x : ℝ≥0 → Fin (k + 2) → ℤ | EsD n m₁ (fun q => p₀ + x q)} =
        ⋂ m : ℕ, ⋂ (_ : m₁ ≤ m), ⋂ (_ : m ≤ n), {x : ℝ≥0 → Fin (k + 2) → ℤ |
          ∃ t ∈ qSet 0 (tn ((4 : ℝ) ^ m)), ∃ s ∈ qSet 0 (tn ((4 : ℝ) ^ m)),
            (0 < t ∧ s ≤ t ∧ t ≤ s + 1) ∧ (m : ℝ) ^ 2 ≤ ‖p₀ + x t - (p₀ + x s)‖}ᶜ := by
      ext x; simp [EsD, and_assoc]
    rw [this]
    exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      (measurableSet_cyl2 _ _ (fun t s => 0 < t ∧ s ≤ t ∧ t ≤ s + 1)
        (fun a b => (m : ℝ) ^ 2 ≤ ‖p₀ + a - (p₀ + b)‖)).compl
  have hG : MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ | EsG n j I u i (fun q => p₀ + x q)} :=
    (measurableSet_cyl _ _ (fun v => EsGBad n j I u i (p₀ + v))).compl
  exact hB.inter (hB'.inter (hD.inter hG))

theorem measurableSet_EsJ_x (n m₁ j I : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ)
    (A : Set (Fin (k + 2) → ℤ)) (p₀ : Fin (k + 2) → ℤ) :
    MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ | EsJ n m₁ j I u i A (fun q => p₀ + x q)} := by
  have hC : MeasurableSet {x : ℝ≥0 → Fin (k + 2) → ℤ | EsC n A (fun q => p₀ + x q)} :=
    (measurableSet_cyl _ _ (fun v => p₀ + v ∈ A)).compl
  have hR := measurableSet_EsRest n m₁ j I u i p₀
  have e : {x : ℝ≥0 → Fin (k + 2) → ℤ | EsJ n m₁ j I u i A (fun q => p₀ + x q)} =
      {x : ℝ≥0 → Fin (k + 2) → ℤ | EsB n m₁ (escPoint n j u i) (fun q => p₀ + x q) ∧
        EsB' n j (escPoint n j u i) (fun q => p₀ + x q) ∧ EsD n m₁ (fun q => p₀ + x q) ∧
        EsG n j I u i (fun q => p₀ + x q)} ∩
      {x : ℝ≥0 → Fin (k + 2) → ℤ | EsC n A (fun q => p₀ + x q)} := by
    ext x
    simp only [EsJ, mem_ofPred_eq, mem_inter_iff]
    tauto
  rw [e]
  exact hR.inter hC

theorem prob_envWalk_ge (_hk : 3 ≤ k) {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (CycS ℕ (k + 2) β)}
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr) {n m₁ j I : ℕ}
    (u : Fin (k + 2) → ℤ) (i : ℕ) (b : ℝ) (A : Set (Fin (k + 2) → ℤ))
    (hm₁ : 1 ≤ m₁) (hm1n : m₁ ≤ n) (hβ : (4 : ℝ) ^ m₁ ≤ β)
    (hjn : (j : ℝ) * 4 ^ j ≤ 4 ^ n) :
    Pr {ω | EsJ n m₁ j I u i A (absPath (escPoint n j u i) N ω)} ≤
      Pr {ω | EsJ n m₁ j I u i A (fun q => envWalk (N ω) (0, escPoint n j u i, b, true) q)} := by
  have := hN.isProbabilityMeasure
  set p := escPoint n j u i with hp
  set δ0 : CycData ℕ (k + 2) := (0, 0, 0, true) with hδ0
  set δi : CycData ℕ (k + 2) := (0, p, b, true) with hδi
  set S : Set (ℝ≥0 → Fin (k + 2) → ℤ) := {x | EsJ n m₁ j I u i A (fun q => p + x q)} with hS
  have hSm : MeasurableSet S := measurableSet_EsJ_x n m₁ j I u i A p
  have hmap : ∀ δ : CycData ℕ (k + 2), Measurable fun (ω : Ω) (s : ℝ≥0) =>
      envWalk (N ω) δ s - δ.start := by
    intro δ
    refine measurable_pi_iff.2 fun s => ?_
    have := (measurable_pi_apply s).comp
      (measurable_envWalk.comp (hN.measurable.prodMk (measurable_const (a := δ))))
    exact this.sub_const _
  -- the law of the first piece equals the law of the walk started at `p`
  have hM := isPoissonPointProcess_envMeasure hN δ0
  have hlaw : Pr.map (fun ω (s : ℝ≥0) => envWalk (N ω) δ0 s - δ0.start) =
      Pr.map (fun ω (s : ℝ≥0) => envWalk (N ω) δi s - δi.start) :=
    (law_envWalk hN hM δ0).trans (law_envWalk hN hM δi).symm
  have hZ : Pr ((fun (ω : Ω) (s : ℝ≥0) => envWalk (N ω) δ0 s - δ0.start) ⁻¹' S) =
      Pr {ω | EsJ n m₁ j I u i A (fun q => envWalk (N ω) δi q)} := by
    have h1 := Measure.map_apply (μ := Pr) (hmap δ0) hSm
    have h2 := Measure.map_apply (μ := Pr) (hmap δi) hSm
    rw [hlaw] at h1
    rw [← h1, h2]
    congr 1
    ext ω
    have hfun : (fun q : ℝ≥0 => p + (envWalk (N ω) δi q - δi.start)) =
        fun q => envWalk (N ω) δi q := by
      funext q
      show p + (envWalk (N ω) δi q - p) = envWalk (N ω) δi q
      abel
    simp only [mem_preimage, hS, mem_ofPred_eq]
    rw [hfun]
  rw [← hZ]
  refine measure_mono_ae ?_
  filter_upwards [CycSchemeEnv.ae_cycGood' hN, ae_isRCPath_avoidPath hN] with ω hgood hrc hJ
  have hgood' : CycGood (N ω) := hgood
  have e : avoidPath N ω = fun q : ℝ≥0 => ElboimSly.regenWalk (fun l => cycSlice l (N ω)) (q : ℝ) := by
    funext q
    simp only [avoidPath, avoidWalk]
    rw [avoidEnv_eq_cycSlice]
  have e2 : absPath p N ω =
      fun q : ℝ≥0 => p + ElboimSly.regenWalk (fun l => cycSlice l (N ω)) (q : ℝ) := by
    funext q
    simp only [absPath]
    rw [e]
  have hrc' : IsRCPath (fun q : ℝ≥0 => ElboimSly.regenWalk (fun l => cycSlice l (N ω)) (q : ℝ)) := by
    rw [← e]; exact hrc
  have hB : EsB n m₁ p (fun q => p + ElboimSly.regenWalk (fun l => cycSlice l (N ω)) (q : ℝ)) := by
    rw [← e2]; exact hJ.1
  have heq := avoid_eq_envWalk_of_EsB hgood' hrc' hm₁ hm1n hβ p hB
  show EsJ n m₁ j I u i A (fun q => p + (envWalk (N ω) δ0 q - δ0.start))
  refine (EsJ_congr (n := n) (m₁ := m₁) (j := j) (I := I) (u := u) (i := i) (A := A) hjn
    (y := absPath p N ω) (y' := fun q => p + (envWalk (N ω) δ0 q - δ0.start)) ?_).1 hJ
  intro q hq
  rw [e2]
  show p + ElboimSly.regenWalk (fun l => cycSlice l (N ω)) (q : ℝ) = p + (envWalk (N ω) δ0 q - 0)
  rw [sub_zero, heq q hq]

/-- **The bound on `P(𝒥)`** for the regenerated walk: `P(𝒢) - (errors of ℬ, ℬ', 𝒞, 𝒟)`. -/
theorem prob_J_bound (hk : 3 ≤ k) :
    ∃ CB CB' CC CD cD : ℝ, 0 < CB ∧ 0 < CB' ∧ 0 < CC ∧ 0 < CD ∧ 0 < cD ∧
      ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} (_hp : Es4Params (k + 2) β n₀ n t₀) {Ω : Type}
        [MeasurableSpace Ω]
        {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}
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
        (A : Set (Fin (k + 2) → ℤ)) {L : ℝ} (_hL1 : (4 : ℝ) ^ (n₀ + 1) ≤ L) (_hL2 : L ≤ (4 : ℝ) ^ n)
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
          (absPath (escPoint n (escJ n) u i) N ω)} := by
  obtain ⟨CB, hCB, hB⟩ := prob_B_bad hk
  obtain ⟨CB', hCB', hB'⟩ := prob_B'_bad hk
  obtain ⟨CC, hCC, hC⟩ := prob_C_bad hk
  obtain ⟨CD, cD, hCD, hcD, hD⟩ := prob_D_bad hk
  refine ⟨CB, CB', CC, CD, cD, hCB, hCB', hCC, hCD, hcD, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN hn53 u i hi1 hiI hIn hj1 hj2 hT1 hT2 hε1 hε2 m₁ hm₁ hθB hθB'
    A L hL1 hL2 hA1 hA2
  have := hN.isProbabilityMeasure
  set p := escPoint n (escJ n) u i with hpdef
  have h44 : (4 : ℝ) ^ n₀ < 4 ^ (n₀ + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hT1' : (4 : ℝ) ^ n₀ < (escJ n : ℝ) * 4 ^ escJ n := lt_of_lt_of_le h44 hT1
  have hG := prob_G hk hp hN hn53 u hi1 hiI hIn hj1 hj2 hT1' hT2 hε1 hε2
  have hBb := hB β n₀ n t₀ hp Pr N hN p hm₁ hθB
  have hB'b := hB' β n₀ n t₀ hp Pr N hN p (escJ n) hT1 hT2 hθB'
  have hCb := hC β n₀ n t₀ hp Pr N hN p A hL1 hL2 hA1 hA2
  have hDb := hD β n₀ n t₀ hp Pr N hN p (m₁ := m₁) (by omega)
  have hsub : {ω | EsG n (escJ n) (escIstar n (escJ n)) u i (absPath p N ω)} ⊆
      {ω | EsJ n m₁ (escJ n) (escIstar n (escJ n)) u i A (absPath p N ω)} ∪
      ({ω | ¬ EsB n m₁ p (absPath p N ω)} ∪ ({ω | ¬ EsB' n (escJ n) p (absPath p N ω)} ∪
      ({ω | ¬ EsC n A (absPath p N ω)} ∪ {ω | ¬ EsD n m₁ (absPath p N ω)}))) := by
    intro ω hω
    by_cases h1 : EsB n m₁ p (absPath p N ω)
    · by_cases h2 : EsB' n (escJ n) p (absPath p N ω)
      · by_cases h3 : EsC n A (absPath p N ω)
        · by_cases h4 : EsD n m₁ (absPath p N ω)
          · exact Or.inl ⟨h1, h2, h3, h4, hω⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
      · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inl h1)
  have hmain : ENNReal.ofReal (cline (k + 2)) -
      ENNReal.ofReal (Real.exp (-((avoidLevel ((escJ n : ℝ) * 4 ^ escJ n) : ℕ) : ℝ) ^ 2)) ≤
      Pr {ω | EsJ n m₁ (escJ n) (escIstar n (escJ n)) u i A (absPath p N ω)} + errB CB k m₁ n +
        ENNReal.ofReal (CB' * ((2 : ℝ) ^ escJ n) ^ k *
          ((escJ n : ℝ) * 4 ^ escJ n) ^ (-(k : ℝ) / 2)) +
        ENNReal.ofReal (CC * L ^ (-(1 : ℝ) / 30)) + errD CD cD m₁ n := by
    refine hG.trans ((measure_mono hsub).trans ?_)
    refine (measure_union_le _ _).trans ?_
    have := measure_union_le (μ := Pr) {ω | ¬ EsB n m₁ p (absPath p N ω)}
      ({ω | ¬ EsB' n (escJ n) p (absPath p N ω)} ∪
      ({ω | ¬ EsC n A (absPath p N ω)} ∪ {ω | ¬ EsD n m₁ (absPath p N ω)}))
    have h2 := measure_union_le (μ := Pr) {ω | ¬ EsB' n (escJ n) p (absPath p N ω)}
      ({ω | ¬ EsC n A (absPath p N ω)} ∪ {ω | ¬ EsD n m₁ (absPath p N ω)})
    have h3 := measure_union_le (μ := Pr) {ω | ¬ EsC n A (absPath p N ω)}
      {ω | ¬ EsD n m₁ (absPath p N ω)}
    calc _ ≤ Pr {ω | EsJ n m₁ (escJ n) (escIstar n (escJ n)) u i A (absPath p N ω)} +
          (Pr {ω | ¬ EsB n m₁ p (absPath p N ω)} + (Pr {ω | ¬ EsB' n (escJ n) p (absPath p N ω)} +
          (Pr {ω | ¬ EsC n A (absPath p N ω)} + Pr {ω | ¬ EsD n m₁ (absPath p N ω)}))) := by
          gcongr
          exact this.trans (add_le_add le_rfl (h2.trans (add_le_add le_rfl h3)))
      _ ≤ _ := by
          rw [add_assoc, add_assoc, add_assoc]
          gcongr
  rw [tsub_le_iff_right, tsub_le_iff_right, tsub_le_iff_right, tsub_le_iff_right]
  calc _ ≤ _ := hmain
    _ = _ := by ring

end ElboimSly.Paper.Escape
