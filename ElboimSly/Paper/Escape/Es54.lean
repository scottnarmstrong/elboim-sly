/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Main
public import ElboimSly.Paper.Escape.Es54Meas
public import Mathlib

/-!
# ES22 Corollary 5.4

ES22 Corollary 5.4.  Under the hypotheses of ES22 Lemma 5.3,
`P(𝒜(β')) ≥ 1 - (1 - c_{53})^{I}` for every admissible `B` and every `β'`, where
`𝒜(β') = ⋃_{ℓ < I} 𝒜_ℓ`.  The proof is the induction of the written proof: `𝒜_ℓ ∈ 𝒢_ℓ ⊆ 𝒢_{i-1}` for
`ℓ < i`, so `P(⋂_{ℓ ≤ i} 𝒜_ℓ^c) = E[1_{⋂_{ℓ<i} 𝒜_ℓ^c} P(𝒜_i^c | 𝒢_{i-1})] ≤ (1 - c_{53}) P(⋂_{ℓ<i} 𝒜_ℓ^c)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

theorem es5_4 (hk : 3 ≤ k) :
    ∃ β53 : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
      {𝒢₀ : MeasurableSpace Ω} [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
      {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
      (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N'), β53 n₀ ≤ β →
      ∀ (u : Fin (k + 2) → ℤ), EscAdmissible (escJ n) u → ∀ (b : ℕ),
        1 - (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n) ≤
          Pr {ω | ∃ ℓ, ℓ < escIstar n (escJ n) ∧
            (escEntry n u b (hlog_of_params hS.params) (cycNgood N ω) ℓ).len =
              (4 : ℝ≥0∞) ^ n} := by
  obtain ⟨β53, h53⟩ := es5_3 hk
  refine ⟨β53, ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS hβ u hadm b
  have := hS.space.ppp.isProbabilityMeasure
  set hlog := hlog_of_params hS.params with hhlog
  set I := escIstar n (escJ n) with hI
  set c : ℝ≥0∞ := ENNReal.ofReal (cline (k + 2) / 2) with hc
  have hN := hS.space.ppp
  have h𝒢 := hS.space.le
  set A : ℕ → Set Ω := fun ℓ => EscAEv n u b hlog N ℓ with hA
  have hAm : ∀ ℓ, ℓ < I → MeasurableSet (A ℓ) := fun ℓ hℓ => measurableSet_A hN.measurable hℓ
  -- the event that none of the first `i` walks succeeds
  set E : ℕ → Set Ω := fun i => {ω | ∀ ℓ, ℓ < i → ω ∉ A ℓ} with hE
  have hEm : ∀ i, i ≤ I → MeasurableSet (E i) := by
    intro i hi
    have : E i = ⋂ ℓ ∈ Finset.range i, (A ℓ)ᶜ := by
      ext ω; simp [hE]
    rw [this]
    exact MeasurableSet.biInter (Finset.range i).countable_toSet fun ℓ hℓ =>
      (hAm ℓ (lt_of_lt_of_le (Finset.mem_range.1 hℓ) hi)).compl
  have hstep : ∀ i, i < I → Pr (E (i + 1)) ≤ (1 - c) * Pr (E i) := by
    intro i hi
    obtain ⟨hT, hG⟩ := h53 hS hβ u hadm b (m := i) hi
    have hTi := isStoppingTime_escLam (u := u) (b := b) (hlog := hlog) 𝒢₀ hN h𝒢 hi
    -- `E i ∈ 𝒢_i`
    have hEi : MeasurableSet[hT.measurableSpace] (E i) := by
      have : E i = ⋂ ℓ ∈ Finset.range i, (A ℓ)ᶜ := by
        ext ω; simp [hE]
      rw [this]
      refine @MeasurableSet.biInter Ω ℕ hT.measurableSpace _ _ (Finset.range i).countable_toSet
        fun ℓ hℓ => ?_
      have hℓi : ℓ < i := Finset.mem_range.1 hℓ
      have hTl := isStoppingTime_escLam (u := u) (b := b) (hlog := hlog) 𝒢₀ hN h𝒢
        (show ℓ + 1 < I by omega)
      have hle : escLam n u b hlog N (ℓ + 1) ≤ escLam n u b hlog N i := by
        intro ω
        unfold escLam
        refine WithTop.coe_le_coe.2 ?_
        have hf1 := cum_envFinal_ne_top (u := u) (b := b) (hlog := hlog)
          (cycNgood N ω) (show ℓ + 1 ≤ I by omega)
        have hf2 := cum_envFinal_ne_top (u := u) (b := b) (hlog := hlog) (cycNgood N ω)
          hi.le
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hf1, ENNReal.coe_toNNReal hf2]
        exact CycRec.cum_mono _ hℓi
      exact (IsStoppingTime.measurableSpace_mono hTl hTi hle) _
        (measurableSet_A_stopped (u := u) (b := b) (hlog := hlog) 𝒢₀ hN h𝒢
          (show ℓ + 1 < I by omega)).compl
    have h1 := hG (E i) hEi
    have hAi := hAm i hi
    have hEmi := hEm i hi.le
    have hsplit : E (i + 1) = E i \ (E i ∩ A i) := by
      ext ω
      simp only [hE, mem_ofPred_eq, mem_sdiff, mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun ℓ hℓ => h ℓ (by omega), fun hh => h i (by omega) hh.2⟩
      · rintro ⟨h1, h2⟩ ℓ hℓ
        rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ with hl | rfl
        · exact h1 ℓ hl
        · exact fun hh => h2 ⟨fun ℓ' hℓ' => h1 ℓ' hℓ', hh⟩
    rw [hsplit, measure_sdiff inter_subset_left (hEmi.inter hAi).nullMeasurableSet
      (measure_ne_top Pr _)]
    rw [ENNReal.sub_mul (fun _ _ => measure_ne_top Pr _), one_mul]
    exact tsub_le_tsub_left h1 _
  have hmain : ∀ i, i ≤ I → Pr (E i) ≤ (1 - c) ^ i := by
    intro i
    induction i with
    | zero => intro _; simp [hE]
    | succ i ih =>
      intro hi
      calc Pr (E (i + 1)) ≤ (1 - c) * Pr (E i) := hstep i (by omega)
        _ ≤ (1 - c) * (1 - c) ^ i := by gcongr; exact ih (by omega)
        _ = (1 - c) ^ (i + 1) := by ring
  have hset : {ω | ∃ ℓ, ℓ < I ∧ (escEntry n u b hlog (cycNgood N ω) ℓ).len =
      (4 : ℝ≥0∞) ^ n} = (E I)ᶜ := by
    ext ω
    constructor
    · rintro ⟨ℓ, hℓ, h⟩ hh
      exact hh ℓ hℓ h
    · intro h
      by_contra hne
      apply h
      intro ℓ hℓ hAℓ
      exact hne ⟨ℓ, hℓ, hAℓ⟩
  have hcompl : Pr {ω | ∃ ℓ, ℓ < I ∧ (escEntry n u b hlog (cycNgood N ω) ℓ).len =
      (4 : ℝ≥0∞) ^ n} = 1 - Pr (E I) := by
    rw [hset]
    exact prob_compl_eq_one_sub (hEm I le_rfl)
  rw [hcompl]
  exact tsub_le_tsub_left (hmain I le_rfl) _

end ElboimSly.Paper.Escape
