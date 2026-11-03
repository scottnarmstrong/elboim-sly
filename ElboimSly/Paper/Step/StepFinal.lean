/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StepH1
public import ElboimSly.Paper.Step.StepH5
public import ElboimSly.Paper.Step.Chain
public import ElboimSly.Paper.Step.Es61All
public import Mathlib

/-!
# The induction step (conditional form)

The induction step; Induction step; Bookkeeping of n_0; closing crefprop:ind-step.

`step_es7_of_inputs` is the conditional form of the induction step: for every base level
`n₁ ≥ 8d` there is a threshold `β_step(n₁)` such that, for `β ≥ β_step(n₁)`, `n ≥ 1`, `t₀ ∈ (1, 4]`
and `t_n > β`, the hypotheses `H(β, n', t₀')` for `n₁ ≤ n' < n` give `H(β, n, t₀)`.

The residual hypotheses (all named; none is assumed as a conclusion of the induction step itself):

* `hI`: `HeavyEscInterface d β E n₀ n t₀` for all data, the conclusion of interface with S6
  (§5); it feeds Theorem 6.1 (`es6_one_of_params`) for (H1);
* `H6 : StepEs61 d c6 β6` (Theorem 6.1 for the driven walk), which feeds Lemmas 7.3, 7.4, 7.6, 7.7
  through `step_lemmas_of_es61`;
* `hPp : StepPp d cPp βPp` (Lemma 7.8), which feeds (H5) at level n.

The threshold `β_step(n₁)` is the maximum of `β_{§6}`, `β_tr`, `β_bm`, `β_tp`, `β_pp`, `4^{n₁+2}`,
`10^14`, `β₅` and `4^{N+1}` with `N` covering the large-`n` conditions (bookkeeping of n_0; closing crefprop:ind-step).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

/-- The induction step, conditional on `hI`, `H6`, `hPp`. -/
theorem step_es7_of_inputs {d : ℕ} (hd5 : 5 ≤ d) (E : ℕ → HeavyEscConsts)
    (hI : HeavyEscInterfaceAll d E)
    {cPp : ℝ} {βPp : ℕ → ℝ} (hPp : StepPp d cPp βPp) :
    ∃ βstep : ℕ → ℝ, ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)], βstep n₁ ≤ β →
      ∀ n : ℕ, 1 ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 → β < indScale t₀ n →
        (∀ n' : ℕ, n₁ ≤ n' → n' < n → ∀ t' : ℝ, 1 < t' → t' ≤ 4 → IndHyp d β n' t') →
        IndHyp d β n t₀ := by
  obtain ⟨⟨cTf, hcTf, βTf, hTf⟩, ⟨cTr, hcTr, βTr, hTr⟩, ⟨cBm, hcBm, βBm, hBm⟩, βTp, hTp⟩ :=
    step_lemmas_of_es61 hd5 (heavyC6_pos (by omega) (E 0)) (stepEs61_of_interfaceAll hd5 hI)
  have hcPp : 0 < cPp := hPp.1
  let Nb : ℕ → ℕ := fun n₁ => max (max ⌈1 / cTr⌉₊ ⌈1 / cBm⌉₊)
    (max (max ⌈1 / cPp⌉₊ ⌈1 / heavyC6 d (E n₁)⌉₊) (max 3 (heavyN6 d n₁ (E n₁))))
  refine ⟨fun n₁ => max (βTr n₁) (max (βBm n₁) (max (βTp n₁) (max (βPp n₁)
    (max ((4 : ℝ) ^ (n₁ + 2)) (max ((10 : ℝ) ^ 14) (max (E n₁).beta5 ((4 : ℝ) ^ (Nb n₁ + 1)))))))),
    ?_⟩
  intro n₁ hn₁ β _ hβ n hn t₀ ht1 ht4 hlt hind
  have hβTr : βTr n₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ' := (le_max_right _ _).trans hβ
  have hβBm : βBm n₁ ≤ β := (le_max_left _ _).trans hβ'
  have hβ'' := (le_max_right _ _).trans hβ'
  have hβTp : βTp n₁ ≤ β := (le_max_left _ _).trans hβ''
  have hβ3 := (le_max_right _ _).trans hβ''
  have hβPp : βPp n₁ ≤ β := (le_max_left _ _).trans hβ3
  have hβ4 := (le_max_right _ _).trans hβ3
  have hβ2 : (4 : ℝ) ^ (n₁ + 2) ≤ β := (le_max_left _ _).trans hβ4
  have hβ5' := (le_max_right _ _).trans hβ4
  have hβ14 : (10 : ℝ) ^ 14 ≤ β := (le_max_left _ _).trans hβ5'
  have hβ6 := (le_max_right _ _).trans hβ5'
  have hβE : (E n₁).beta5 ≤ β := (le_max_left _ _).trans hβ6
  have hβN : (4 : ℝ) ^ (Nb n₁ + 1) ≤ β := (le_max_right _ _).trans hβ6
  have hβ1 : 1 < β := lt_of_lt_of_le (by
    have : (1 : ℝ) < 4 ^ (n₁ + 2) := one_lt_pow₀ (by norm_num) (by omega)
    exact this) hβ2
  have hreg : StepRegime d n₁ β n t₀ :=
    ⟨hn₁, hβ1, hn, ⟨ht1, ht4⟩, hlt, fun n' a b t' ht' => hind n' a b t' ht'.1 ht'.2⟩
  have hnN : Nb n₁ < n := step_n_gt hreg hβN
  have hle : ∀ x : ℕ, x ≤ Nb n₁ → x ≤ n := fun x hx => by omega
  have hc : ∀ c : ℝ, ⌈1 / c⌉₊ ≤ Nb n₁ → 1 / c ≤ (n : ℝ) := fun c hc =>
    (Nat.le_ceil _).trans (by exact_mod_cast hle _ hc)
  have hnTr : 1 / cTr ≤ (n : ℝ) :=
    hc _ ((le_max_left _ _).trans (le_max_left _ _))
  have hnBm : 1 / cBm ≤ (n : ℝ) :=
    hc _ ((le_max_right _ _).trans (le_max_left _ _))
  have hnPp : 1 / cPp ≤ (n : ℝ) :=
    hc _ (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _))
  have hnC6 : 1 / heavyC6 d (E n₁) ≤ (n : ℝ) :=
    hc _ (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _))
  have hn3 : 3 ≤ n :=
    hle _ (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have hN6 : heavyN6 d n₁ (E n₁) ≤ n :=
    hle _ (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  refine ⟨fun Ω _ P N hN => ⟨?_, ?_, ?_, ?_⟩, fun Ω _ P N hN => ?_⟩
  · exact step_H1_of_interface hd5 hn₁ hreg hβ2 hβ14 hβE (hI.2 n₁ β n t₀) hN6 hn3 hnC6 P N hN
  · exact step_H2_of_tp hTp hn₁ hβTp hβ2 hreg P N hN
  · exact step_H3_of_tr hcTr hTr hn₁ hβTr hreg hnTr P N hN
  · exact step_H4_of_bm hcBm hBm hn₁ hβBm hreg hnBm P N hN
  · exact step_H5_of_pp hPp hn₁ hβPp hreg hnPp P N hN

end ElboimSly.Paper.Step

end
