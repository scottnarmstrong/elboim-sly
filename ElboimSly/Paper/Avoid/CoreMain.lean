/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoreProb
public import Mathlib

/-!
# ES22 §4: Lemma 4.1, core form

ES22 Lemma 4.1 (ES22 Lemma 4.1 proof, ES22 §4).

Setting: `ℋ ≤ 𝒜'` a `σ`-algebra; `a ≤ T` real random variables, `ℋ`-measurable; `w` a random path
whose recorded history `h(s) = w((a + s) ∧ T)` is jointly `ℋ ⊗ ℬ`-measurable in `(ω, s)` and right
continuous; `X̃` a measurable process with right-continuous paths, independent of `ℋ`, with the law
of the regenerated walk `W` (`Pr'.map X̃ = Pr₀.map (avoidPath N₀)` for a Poisson environment `N₀`).
Put `W'(r) = w(T) + X̃(r)` and `τ' = hitTime β w a T W'`.

* `Rel = {T relaxed along w|[a,T]} ∈ ℋ`;
* for every `A ∈ ℋ` with `A ⊆ Rel`:
  `(1 - C β^{-δ/30}) P(A) ≤ P(A ∩ {τ' ≥ 4ⁿ})`, i.e. `P(τ' ≥ 4ⁿ | ℋ) ≥ 1 - C β^{-δ/30}` a.s. on `Rel`.

The statement involves `P` only through the outer measure of `{τ' ≥ 4ⁿ}` (which is measurable for
right-continuous paths, but this is not needed for the lower bound).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ}

/-- **ES22 Lemma 4.1**. -/
theorem es4_1_core (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₀ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → Es4Params d β n₀ n t₀ →
      ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] (Pr₀ : Measure Ω₀) (N₀ : Ω₀ → Measure (CycS ℕ d β)),
        IsPoissonPointProcess N₀ (cycIntensity ℕ d β) Pr₀ →
      ∀ {Ω' : Type*} (H : MeasurableSpace Ω') [mΩ : MeasurableSpace Ω'] (_hH : H ≤ mΩ)
        (Pr' : Measure Ω') [IsProbabilityMeasure Pr'] (a T : Ω' → ℝ) (w : Ω' → ℝ → Fin d → ℤ)
        (X : Ω' → ℝ≥0 → Fin d → ℤ),
        (∀ ω, a ω ≤ T ω) → Measurable[H] a → Measurable[H] T →
        Measurable[H.prod inferInstance]
          (fun p : Ω' × ℝ => w p.1 (min (a p.1 + max p.2 0) (T p.1))) →
        (∀ ω, IsRCPath (fun s : ℝ≥0 => w ω (min (a ω + s) (T ω)))) →
        Measurable X → (∀ ω, IsRCPath (X ω)) →
        Indep H (MeasurableSpace.comap X inferInstance) Pr' →
        Pr'.map X = Pr₀.map (avoidPath N₀) →
        MeasurableSet[H] {ω | IsRelaxedTimeWrt β (w ω) (a ω) (T ω)} ∧
        ∀ {A : Set Ω'}, MeasurableSet[H] A → (∀ ω ∈ A, IsRelaxedTimeWrt β (w ω) (a ω) (T ω)) →
          ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) * Pr' A ≤
            Pr' (A ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤
              hitTime β (w ω) (a ω) (T ω) (fun r => w ω (T ω) + X ω r.toNNReal)}) := by
  obtain ⟨C, hC, H0⟩ := gamma_prob hd
  refine ⟨C, hC, fun n₀ => ?_⟩
  obtain ⟨β41a, hH0⟩ := H0 n₀
  obtain ⟨β41b, hb10, hβb⟩ := exists_beta41 hd n₀
  refine ⟨max β41a β41b, ?_⟩
  intro β _ n t₀ hβ hp Ω₀ _ Pr₀ N₀ hN₀ Ω' H mΩ hH Pr' _ a T w X haT ha hT hhist hrc hXm hXrc
    hind hlaw
  have hβa : β41a ≤ β := (le_max_left _ _).trans hβ
  have hβb' : β41b ≤ β := (le_max_right _ _).trans hβ
  have hgamma := hH0 β n t₀ hβa hp Pr₀ N₀ hN₀ Pr' X hXm hlaw
  have hδ := avoid_indDelta_pos (d := d) (by have := hp.five_le; omega)
  obtain ⟨hL4, hL3, hb3⟩ := hβb β hβb'
  have hβ1 : (10 : ℝ) ^ 14 ≤ β := hb10.trans hβb'
  have hβ1' : (1 : ℝ) ≤ β := le_trans (by norm_num) hβ1
  have hβ0 : 0 < β := by linarith
  have hn1 : 1 ≤ n := by have := hp.lt; omega
  have hβn : β < (4 : ℝ) ^ (n + 1) := by
    have h1 := hp.beta_lt
    have h2 : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1) := by
      unfold indScale; rw [pow_succ]; nlinarith [hp.le_four, pow_pos (by norm_num : (0 : ℝ) < 4) n]
    linarith
  have hb1pos : 0 < β ^ indDelta d := Real.rpow_pos_of_pos hβ0 _
  have hb3pos : 0 < β ^ (3 * indDelta d) := Real.rpow_pos_of_pos hβ0 _
  have hb3n : β ^ (3 * indDelta d) ≤ (4 : ℝ) ^ n := beta_pow_le hd hβ1' hn1 hβn
  have hb1big : (2 : ℝ) < β ^ indDelta d := by
    have : (4 : ℝ) ≤ 4 ^ (n₀ + 1) := by
      calc (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (n₀ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hRel : MeasurableSet[H] {ω | IsRelaxedTimeWrt β (w ω) (a ω) (T ω)} :=
    @measurableSet_rel d β _ Ω' H a T w haT ha hT hhist hrc
  refine ⟨hRel, ?_⟩
  intro A hA hArel
  have hAm : MeasurableSet A := hH _ hA
  set c : ℝ := C * β ^ (-indDelta d / 30) with hc
  set Γ0 := cylGamma d (β ^ indDelta d / 2) (β ^ indDelta d) (β ^ (3 * indDelta d)).toNNReal
    ((4 : ℝ) ^ n).toNNReal with hΓ0
  have hΓ0m : MeasurableSet Γ0 := measurableSet_cylGamma _ _ _ _
  -- measurability of the recorded history
  have hU : Measurable[H] (fun ω => histOf (w ω) (a ω) (T ω)) := by
    let : MeasurableSpace Ω' := H
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · refine measurable_pi_iff.2 fun s => ?_
      have : (fun ω => w ω (min (a ω + s) (T ω))) =
          (fun p : Ω' × ℝ => w p.1 (min (a p.1 + max p.2 0) (T p.1))) ∘
            (fun ω => (ω, (s : ℝ))) := by
        funext ω; simp
      rw [this]
      exact hhist.comp (measurable_id.prodMk measurable_const)
    · exact (hT.sub ha).real_toNNReal
    · have : (fun ω => w ω (T ω)) =
          (fun p : Ω' × ℝ => w p.1 (min (a p.1 + max p.2 0) (T p.1))) ∘
            (fun ω => (ω, T ω - a ω)) := by
        funext ω
        simp only [Function.comp]
        rw [max_eq_left (by linarith [haT ω]), show a ω + (T ω - a ω) = T ω by ring,
          min_self]
      show Measurable (fun ω => w ω (T ω))
      rw [this]
      exact hhist.comp (measurable_id.prodMk (hT.sub ha))
  have hIA : Measurable[H] (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hA
  have hV2H : Measurable[H] (fun ω => (histOf (w ω) (a ω) (T ω), A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) :=
    hU.prodMk hIA
  have hV2 : Measurable (fun ω => (histOf (w ω) (a ω) (T ω), A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) :=
    hV2H.mono hH le_rfl
  -- independence
  have hindep : IndepFun (fun ω => (histOf (w ω) (a ω) (T ω), A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) X Pr' := by
    have hle : MeasurableSpace.comap (fun ω => (histOf (w ω) (a ω) (T ω),
        A.indicator (fun _ => (1 : ℝ≥0∞)) ω)) inferInstance ≤ H := hV2H.comap_le
    exact indep_of_indep_of_le_left hind hle
  -- the integrand
  set φ : HistE d × ℝ≥0∞ → (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞ :=
    fun x y => x.2 * Γ0.indicator (fun _ => (1 : ℝ≥0∞)) (x.1, y) with hφ
  have hφm : Measurable (Function.uncurry φ) := by
    refine (measurable_snd.comp measurable_fst).mul ?_
    exact measurable_const.indicator (hΓ0m.preimage (by fun_prop))
  have hfreeze := ElboimSly.Brownian.lintegral_freeze (P := Pr') hV2 hXm hindep hφm
  -- lower bound for the inner integral
  have hlow : ∀ ω, A.indicator (fun _ => ENNReal.ofReal (1 - c)) ω ≤
      ∫⁻ y, φ (histOf (w ω) (a ω) (T ω), A.indicator (fun _ => (1 : ℝ≥0∞)) ω) y ∂(Pr'.map X) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      have hsec : MeasurableSet {y | (histOf (w ω) (a ω) (T ω), y) ∈ Γ0} :=
        measurable_prodMk_left hΓ0m
      have : ∫⁻ y, φ (histOf (w ω) (a ω) (T ω), (1 : ℝ≥0∞)) y ∂(Pr'.map X)
          = (Pr'.map X) {y | (histOf (w ω) (a ω) (T ω), y) ∈ Γ0} := by
        simp only [hφ, one_mul]
        rw [← lintegral_indicator_one hsec]
        rfl
      rw [this, Measure.map_apply hXm hsec]
      exact hgamma (w ω) (a ω) (T ω) (haT ω) (hArel ω hω)
    · simp [Set.indicator_of_notMem hω]
  -- pointwise upper bound
  have hup : ∀ ω, φ (histOf (w ω) (a ω) (T ω), A.indicator (fun _ => (1 : ℝ≥0∞)) ω) (X ω) ≤
      (A ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤
        hitTime β (w ω) (a ω) (T ω) (fun r => w ω (T ω) + X ω r.toNNReal)}).indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ A
    · by_cases hg : (histOf (w ω) (a ω) (T ω), X ω) ∈ Γ0
      · have hgood := good_imp_nohit (β := β) (b1 := β ^ indDelta d) (b3 := β ^ (3 * indDelta d))
          hβ0 hb3pos.le hb3 hb1big (w := w ω) (a := a ω) (T := T ω) (haT ω)
          (hArel ω hω).2 (hrc ω) (hXrc ω) (N4 := (4 : ℝ) ^ n) hb3n hg
        have hmem : ω ∈ A ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤
            hitTime β (w ω) (a ω) (T ω) (fun r => w ω (T ω) + X ω r.toNNReal)} := ⟨hω, hgood⟩
        simp only [hφ, Set.indicator_of_mem hω, Set.indicator_of_mem hg,
          Set.indicator_of_mem hmem, one_mul]
        rfl
      · simp [hφ, Set.indicator_of_mem hω, Set.indicator_of_notMem hg]
    · simp [hφ, Set.indicator_of_notMem hω]
  calc ENNReal.ofReal (1 - c) * Pr' A
      = ∫⁻ ω, A.indicator (fun _ => ENNReal.ofReal (1 - c)) ω ∂Pr' :=
        (lintegral_indicator_const hAm _).symm
    _ ≤ ∫⁻ ω, ∫⁻ y, φ (histOf (w ω) (a ω) (T ω), A.indicator (fun _ => (1 : ℝ≥0∞)) ω) y
          ∂(Pr'.map X) ∂Pr' := lintegral_mono hlow
    _ = ∫⁻ ω, φ (histOf (w ω) (a ω) (T ω), A.indicator (fun _ => (1 : ℝ≥0∞)) ω) (X ω) ∂Pr' :=
        hfreeze.symm
    _ ≤ ∫⁻ ω, (A ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤
        hitTime β (w ω) (a ω) (T ω) (fun r => w ω (T ω) + X ω r.toNNReal)}).indicator 1 ω ∂Pr' :=
        lintegral_mono hup
    _ ≤ _ := lintegral_indicator_one_le _

end ElboimSly.Paper

end
