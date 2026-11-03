/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Law
public import ElboimSly.Paper.Escape.C57Walk
public import ElboimSly.Paper.Escape.C57Core
public import Mathlib

/-!
# The probability of the events `E₅₇`, `E_far`, `E_av` for the regenerated walk

ES22 Claim 5.7, "Events" (ES22 Claim 5.7, eq. (85): staying in a box and visiting B^-, ES22 Claim 4.3, ES22 Claim 4.2,
The induction hypothesis at arbitrary times).  The events are written with countable test times (`qSet`, and the multiples of
`β` for `E_far`), so that they are measurable for the product `σ`-algebra of the path space; they
contain the real-time events.

* `Cyl57`, `CylFar`, `CylAv`: the events, as sets of paths `z = Y' - p_i`;
* `prob_57`, `prob_far`, `prob_av`: lower bounds for `P(regenW N'' ∈ ·)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Brownian ElboimSly.Bridge ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

section events

variable {k : ℕ}

/-- `E₅₇` for the recentred path `z = Y' - p_i`. -/
def Cyl57 (n j : ℕ) (u : EscV k) (i : ℕ) (S : ℝ≥0) : Set (ℝ≥0 → EscV k) :=
  {z | (∀ q ∈ qSet 0 S, escPoint n j u i + z q ∈ escBigBox j u) ∧
    escPoint n j u i + z S ∉ escQ j u}

/-- `E_far` for the recentred path: `‖z(τ)‖ ≥ L` at the test times of `[a, 4^n]`. -/
def CylFar (β : ℝ) (n : ℕ) (a L : ℝ) : Set (ℝ≥0 → EscV k) :=
  {z | ∀ τ : ℝ≥0, a ≤ τ → (τ : ℝ) ≤ 4 ^ n →
    (τ ∈ qSet a.toNNReal ((4 : ℝ≥0) ^ n) ∨ ∃ m : ℕ, τ = m * β.toNNReal) → L ≤ ‖z τ‖}

/-- `E_av` for the recentred path: `p + z(τ) ∉ A` at the test times of `[0, 4^n]`. -/
def CylAv (n : ℕ) (p : EscV k) (A : Set (EscV k)) : Set (ℝ≥0 → EscV k) :=
  {z | ∀ τ ∈ qSet 0 ((4 : ℝ≥0) ^ n), p + z τ ∉ A}

end events

section prob

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N N'' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- **`E₅₇`**: `P(E₅₇) ≥ c₅₇ - e^{-n_T²}` (`T = 4^j`). -/
theorem prob_57 (hp : Es4Params (k + 2) β n₀ n t₀)
    (hN'' : IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr) {m : ℕ} (u : EscV k)
    {i : ℕ} (hi1 : 1 ≤ i) (hiI : i ≤ escIstar m (escJ m)) (hm : 2 ≤ m)
    (hj1 : (m : ℝ) ^ 20 ≤ 2 ^ escJ m) (hj3 : 3 ≤ escJ m)
    (hIlam : 16 * (escIstar m (escJ m) * escLambda m) ≤ 3 * 2 ^ escJ m)
    (hT1 : (4 : ℝ) ^ n₀ < 4 ^ escJ m) (hT2 : (4 : ℝ) ^ escJ m ≤ 4 ^ n)
    (hε : ((4 : ℝ) ^ escJ m) ^ indThetaH < (2 : ℝ) ^ escJ m / 64)
    {S : ℝ≥0} (hS : (S : ℝ) = ((2 : ℝ) ^ escJ m) ^ 2 / 4) :
    ENNReal.ofReal (c57 (k + 2)) -
        ENNReal.ofReal (Real.exp (-((avoidLevel ((4 : ℝ) ^ escJ m) : ℕ) : ℝ) ^ 2)) ≤
      Pr {ω | regenW N'' ω ∈ Cyl57 m (escJ m) u i S} := by
  have := hN''.isProbabilityMeasure
  set T : ℝ := (4 : ℝ) ^ escJ m with hT
  have hT0 : 0 < T := by positivity
  set Tn : ℝ≥0 := T.toNNReal with hTn
  have hTn' : (Tn : ℝ) = ((2 : ℝ) ^ escJ m) ^ 2 := by
    rw [hTn, Real.coe_toNNReal _ hT0.le, hT]
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  obtain ⟨σ, hσ, hc⟩ := es4_hyp_d hp hN'' hT1 hT2
  have hε0 : 0 < T ^ indThetaH := Real.rpow_pos_of_pos hT0 _
  have key := lawW_57_ge (n := m) u hi1 hiI hm hj1 hj3 hIlam hTn' hS hσ.1 hσ.2 hε0 hε hc
  have hSle : S ≤ Tn := by
    rw [← NNReal.coe_le_coe, hS, hTn']
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ escJ m) ^ 2 := by positivity
    linarith
  set Φ : Ω → Set.Icc (0 : ℝ≥0) Tn → EscV k :=
    fun ω t => avoidWalk N'' ω ((t : ℝ≥0) : ℝ) with hΦ
  have hΦm : AEMeasurable Φ Pr := by
    have : Φ = (fun (y : ℝ≥0 → EscV k) (t : Set.Icc (0 : ℝ≥0) Tn) => y t) ∘ avoidPath N'' := rfl
    rw [this]
    exact (Measurable.of_eval fun t => measurable_pi_apply _).comp_aemeasurable
      (aemeasurable_avoidPath hN'')
  have hset : {ω | regenW N'' ω ∈ Cyl57 m (escJ m) u i S} = Φ ⁻¹' G57W m (escJ m) u i S Tn := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, Cyl57, G57W]
    have hr : ∀ t : ℝ≥0, regenW N'' ω t = avoidWalk N'' ω (t : ℝ) := fun t => by
      rw [regenW_eq_avoidPath]; rfl
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun q hq hqT => ?_, fun hS' => ?_⟩
      · have := h1 q hq; rwa [hr] at this
      · have := h2; rwa [hr] at this
    · rintro ⟨h1, h2⟩
      refine ⟨fun q hq => ?_, ?_⟩
      · have hqS : q ≤ S := (mem_qSet_Icc zero_le hq).2
        have := h1 q hq (hqS.trans hSle)
        have e : regenW N'' ω q = Φ ω ⟨q, bot_le, hqS.trans hSle⟩ := hr q
        rw [e]; exact this
      · have := h2 hSle
        have e : regenW N'' ω S = Φ ω ⟨S, bot_le, hSle⟩ := hr S
        rw [e]; exact this
  rw [hset, ← Measure.map_apply_of_aemeasurable hΦm (measurableSet_G57W _ _ _ _ _ _)]
  exact key

end prob

section farav

variable {k : ℕ}

/-- **`E_far`** (ES22 Claim 4.3). -/
theorem prob_far (hd : 5 ≤ k + 2) : ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
    Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
      {N N'' : Ω → Measure (CycS ℕ (k + 2) β)},
      IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
      IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr →
      ∀ {t L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ t → t ≤ (4 : ℝ) ^ n → t ^ indThetaH ≤ L →
        L ≤ t ^ (1 / 2 : ℝ) →
        ENNReal.ofReal (1 - C * L ^ (k + 2 - 2) * t ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2)) ≤
          Pr {ω | regenW N'' ω ∈ CylFar β n t L} := by
  obtain ⟨C, hC, H⟩ := es4_claim3 hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N N'' hN hN'' t L ht1 ht2 htL hLt
  have := hN.isProbabilityMeasure
  have hX := (H β n₀ n t₀ hp Pr N hN ht1 ht2 htL hLt).2 Pr (avoidPath (cycNgood N'')) 0
    (measurable_avoidPath_cycNgood hN''.measurable).aemeasurable
    (fun ω => isRCPath_avoidPath (cycGood_cycNgood N'' ω))
    (map_avoidPath_cycNgood_eq hN hN'')
  refine hX.trans (measure_mono_ae ?_)
  filter_upwards [ae_regenW_eq hN''] with ω h hfull
  intro τ ha hb _
  rw [h]
  simpa using hfull τ ha hb

/-- **`E_av`** (ES22 Claim 4.2). -/
theorem prob_av (hd : 5 ≤ k + 2) : ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
    Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
      {N N'' : Ω → Measure (CycS ℕ (k + 2) β)},
      IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
      IsPoissonPointProcess N'' (cycIntensity ℕ (k + 2) β) Pr →
      ∀ {L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ L → L ≤ (4 : ℝ) ^ n → ∀ (p : EscV k) {A : Set (EscV k)},
        (∀ y ∈ A, L ≤ ‖y - p‖) →
        (∀ r : ℝ, L ≤ r → (({y | y ∈ A ∧ ‖y - p‖ ≤ r} : Set (EscV k)).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)) →
        ENNReal.ofReal (1 - C * L ^ (-(1 : ℝ) / 30)) ≤
          Pr {ω | regenW N'' ω ∈ CylAv n p A} := by
  obtain ⟨C, hC, H⟩ := es4_claim2 hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N N'' hN hN'' L hL1 hL2 p A hA1 hA2
  have := hN.isProbabilityMeasure
  set A' : Set (EscV k) := {v | p + v ∈ A} with hA'
  have h1 : ∀ v ∈ A', L ≤ ‖v‖ := fun v hv => by
    have := hA1 _ hv; simpa using this
  have h2 : ∀ r : ℝ, L ≤ r → ((A' ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
    intro r hr
    have himg : (fun v => p + v) '' (A' ∩ {u | ‖u‖ ≤ r}) = {y | y ∈ A ∧ ‖y - p‖ ≤ r} := by
      ext y
      constructor
      · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
        exact ⟨hv1, by simpa using hv2⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨y - p, ⟨by simpa [hA'] using hy1, by simpa using hy2⟩, by simp⟩
    have := hA2 r hr
    rw [← himg, Set.ncard_image_of_injective _ (add_right_injective p)] at this
    exact this
  have hX := (H β n₀ n t₀ hp Pr N hN hL1 hL2 h1 h2).2 Pr (avoidPath (cycNgood N''))
    (measurable_avoidPath_cycNgood hN''.measurable).aemeasurable
    (fun ω => isRCPath_avoidPath (cycGood_cycNgood N'' ω))
    (map_avoidPath_cycNgood_eq hN hN'')
  refine hX.trans (measure_mono_ae ?_)
  filter_upwards [ae_regenW_eq hN''] with ω h hfull
  intro τ hτ
  rw [h]
  have := hfull τ (by have := (mem_qSet_Icc zero_le hτ).2; exact_mod_cast this)
  exact this

end farav

end ElboimSly.Paper.Escape
