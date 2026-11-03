/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycClosingPlan
public import ElboimSly.Foundations.Cyclic.DrivenDef
public import Mathlib

/-!
# The stopping length of the closing rule

The driven walk is a driven world-line, first paragraph ("Stopping length"): with the closing rule the
stopping length of every path `p` is `treg(p) = inf {kβ : k ≥ 1, p(kβ) = 0}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem ofReal_nat_mul (j : ℕ) :
    ENNReal.ofReal (j * β) = (((j : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.ofReal, Real.toNNReal_mul (Nat.cast_nonneg j)]
  simp

section
variable {I : Type*} [MeasurableSpace I] {K : ℕ∞} {start : ∀ k : ℕ, CycRecN I d k → CycData I d}
  {hs : ∀ k, Measurable (start k)}

omit [Fact (0 < β)] in
theorem closing_hat_path (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d) (a : ℕ) :
    ((closingPlan β K start hs).hatRec k ρ p a (Fin.last k)).2 = p.cut (p.1.jt a) := by
  simp [CycPlan.hatRec, CycRec.snoc]

end

/-- The path is constant between consecutive jump times. -/
theorem fn_eq_of_jt (f : CPath (Fin d → ℤ)) {a : ℕ} {s : ℝ≥0} (h1 : f.jt a ≤ s)
    (h2 : (s : ℝ≥0∞) < f.jt (a + 1)) : f.fn s = f.fn (f.jt a).toNNReal := by
  have hc1 : a ≤ f.cnt s := (f.jt_le_iff a s).1 h1
  have hc2 : f.cnt s < a + 1 := f.cnt_lt_of_lt_jt h2
  rw [f.fn_eq_jv s, show f.cnt s = a by omega]
  rfl

omit [Fact (0 < β)] in
theorem closeSt_cut_iff (p : CycPath d) {ℓ : ℝ≥0∞} (_hℓ : ℓ < ⊤) :
    closeSt β (p.cut ℓ) = true ↔
      ∃ j : ℕ, 1 ≤ j ∧ ℓ = ENNReal.ofReal (j * β) ∧ p.1.fn ℓ.toNNReal = 0 := by
  classical
  unfold closeSt
  simp only [decide_eq_true_eq, CycPath.cut, CPath.cut_len, CPath.cut_fn]
  have : (min (ℓ.toNNReal : ℝ≥0∞) ℓ).toNNReal = ℓ.toNNReal := by
    rw [min_eq_left ENNReal.coe_toNNReal_le_self, ENNReal.toNNReal_coe]
  rw [this]

omit [Fact (0 < β)] in
theorem closeDl_cut (p : CycPath d) {ℓ : ℝ≥0∞} (hℓ : ℓ < ⊤) :
    closeDl β (p.cut ℓ) =
      if p.1.fn ℓ.toNNReal = 0 then
        ENNReal.ofReal (β * (⌈max ℓ.toReal β / β⌉₊ : ℕ)) - ℓ else ⊤ := by
  classical
  unfold closeDl
  simp only [CycPath.cut, CPath.cut_len, CPath.cut_fn]
  have : (min (ℓ.toNNReal : ℝ≥0∞) ℓ).toNNReal = ℓ.toNNReal := by
    rw [min_eq_left ENNReal.coe_toNNReal_le_self, ENNReal.toNNReal_coe]
  rw [this]
  simp [hℓ.ne]


theorem dl_facts (x : ℝ) (_hx : 0 ≤ x) :
    1 ≤ ⌈max x β / β⌉₊ ∧ x ≤ ⌈max x β / β⌉₊ * β ∧
      ∀ j : ℕ, 1 ≤ j → x ≤ j * β → ⌈max x β / β⌉₊ ≤ j := by
  have hβ : 0 < β := Fact.out
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.one_le_iff_ne_zero.2 ?_
    refine (Nat.ceil_pos.2 ?_).ne'
    exact div_pos (lt_max_of_lt_right hβ) hβ
  · have h := Nat.le_ceil (max x β / β)
    rw [div_le_iff₀ hβ] at h
    exact (le_max_left _ _).trans h
  · intro j hj hxj
    refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ hβ]
    refine max_le hxj ?_
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith

theorem jt_zero' (f : CPath (Fin d → ℤ)) : f.jt 0 = 0 := by
  have := (f.jt_le_iff 0 0).2 (Nat.zero_le _)
  simpa using this

theorem closingPlan_stopLen {I : Type*} [MeasurableSpace I] {K : ℕ∞}
    {start : ∀ k : ℕ, CycRecN I d k → CycData I d} {hs : ∀ k, Measurable (start k)}
    (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d) :
    (closingPlan β K start hs).stopLen k ρ p = pathTreg β.toNNReal p.1.fn := by
  classical
  have hβ : 0 < β := Fact.out
  have hβ' : (0 : ℝ≥0) < β.toNNReal := Real.toNNReal_pos.2 hβ
  have hcoe : ((β.toNNReal : ℝ≥0) : ℝ) = β := Real.coe_toNNReal β hβ.le
  have hT : pathTreg β.toNNReal p.1.fn = sInf {t : ℝ≥0∞ | ∃ j : ℕ, 1 ≤ j ∧
      p.1.fn ((j : ℝ≥0) * β.toNNReal) = 0 ∧ t = (((j : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞)} := by
    unfold pathTreg
    rw [← sInf_range]
    congr 1
    ext t
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj.1, hj.2, rfl⟩
    · rintro ⟨j, h1, h2, rfl⟩
      exact ⟨⟨j, h1, h2⟩, rfl⟩
  rw [hT]
  unfold CycPlan.stopLen
  have hdl : ∀ a : ℕ, (closingPlan β K start hs).dl k
      ((closingPlan β K start hs).hatRec k ρ p a) = closeDl β (p.cut (p.1.jt a)) := fun a => by
    show closeDl β _ = _
    rw [closing_hat_path]
  have hst : ∀ a : ℕ, (closingPlan β K start hs).st k
      ((closingPlan β K start hs).hatRec k ρ p a) = closeSt β (p.cut (p.1.jt a)) := fun a => by
    show closeSt β _ = _
    rw [closing_hat_path]
  apply le_antisymm
  · refine le_sInf ?_
    rintro t ⟨j, hj, h0, rfl⟩
    set s : ℝ≥0 := (j : ℝ≥0) * β.toNNReal with hs_def
    have hspos : 0 < s := by
      rw [hs_def]; exact mul_pos (by exact_mod_cast hj) hβ'
    set a := p.1.cnt s with ha
    have hja : p.1.jt a ≤ s := (p.1.jt_le_iff a s).2 le_rfl
    have hjb : (s : ℝ≥0∞) < p.1.jt (a + 1) := by
      by_contra h
      rw [not_lt] at h
      have := (p.1.jt_le_iff (a + 1) s).1 h
      omega
    have hfa : p.1.fn (p.1.jt a).toNNReal = 0 := by
      rw [← fn_eq_of_jt p.1 hja hjb]; exact h0
    have hlt : p.1.jt a < ⊤ := lt_of_le_of_lt hja ENNReal.coe_lt_top
    rcases hja.eq_or_lt with heq | hlt'
    · have ha1 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · rw [h, jt_zero'] at heq
          exact absurd (by exact_mod_cast heq.symm : (s : ℝ≥0) = 0) hspos.ne'
        · exact h
      refine (sInf_le ?_).trans heq.le
      refine Or.inl ⟨a, ha1, hlt, ?_, rfl⟩
      rw [hst, closeSt_cut_iff p hlt]
      refine ⟨j, hj, ?_, hfa⟩
      rw [heq, hs_def, ofReal_nat_mul]
    · set σ := p.1.jt a with hσ
      have hσr : σ.toReal < (s : ℝ) := by
        have : σ.toNNReal < s := by
          rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hlt.ne]; exact hlt'
        exact_mod_cast this
      have hsr : (s : ℝ) = j * β := by rw [hs_def]; push_cast; rw [hcoe]
      obtain ⟨hn1, hn2, hn3⟩ := dl_facts (β := β) σ.toReal ENNReal.toReal_nonneg
      have hnj := hn3 j hj (by rw [← hsr]; exact hσr.le)
      have hX : σ ≤ ENNReal.ofReal (β * (⌈max σ.toReal β / β⌉₊ : ℕ)) := by
        rw [← ENNReal.ofReal_toReal hlt.ne, mul_comm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; exact hn2
      have hXs : ENNReal.ofReal (β * (⌈max σ.toReal β / β⌉₊ : ℕ)) ≤ (s : ℝ≥0∞) := by
        rw [hs_def, ← ofReal_nat_mul, mul_comm]
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnj) hβ.le
      have hc : σ + closeDl β (p.cut σ) = ENNReal.ofReal (β * (⌈max σ.toReal β / β⌉₊ : ℕ)) := by
        rw [closeDl_cut p hlt, ite_eq_left hfa]
        exact add_tsub_cancel_of_le hX
      refine (sInf_le (a := p.1.jt a + (closingPlan β K start hs).dl k
        ((closingPlan β K start hs).hatRec k ρ p a)) ?_).trans ?_
      · refine Or.inr ⟨a, hlt, rfl, ?_⟩
        rw [hdl, hc]; exact lt_of_le_of_lt hXs hjb
      · rw [hdl, hc]; exact hXs
  · refine le_sInf ?_
    rintro t (⟨a, ha, hlt, hst', rfl⟩ | ⟨a, hlt, rfl, hlt2⟩)
    · rw [hst, closeSt_cut_iff p hlt] at hst'
      obtain ⟨j, hj, h1, h2⟩ := hst'
      have h3 : (p.1.jt a).toNNReal = (j : ℝ≥0) * β.toNNReal := by
        rw [h1, ofReal_nat_mul, ENNReal.toNNReal_coe]
      refine sInf_le ⟨j, hj, ?_, ?_⟩
      · rw [← h3]; exact h2
      · rw [h1, ofReal_nat_mul]
    · rw [hdl] at hlt2 ⊢
      by_cases hf : p.1.fn (p.1.jt a).toNNReal = 0
      · set σ := p.1.jt a with hσ
        obtain ⟨hn1, hn2, -⟩ := dl_facts (β := β) σ.toReal ENNReal.toReal_nonneg
        have hX : σ ≤ ENNReal.ofReal (β * (⌈max σ.toReal β / β⌉₊ : ℕ)) := by
          rw [← ENNReal.ofReal_toReal hlt.ne, mul_comm]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; exact hn2
        have hc : σ + closeDl β (p.cut σ) =
            (((⌈max σ.toReal β / β⌉₊ : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
          rw [closeDl_cut p hlt, ite_eq_left hf, add_tsub_cancel_of_le hX, mul_comm, ofReal_nat_mul]
        rw [hc] at hlt2 ⊢
        refine sInf_le ⟨⌈max σ.toReal β / β⌉₊, hn1, ?_, rfl⟩
        have hle : σ ≤ (((⌈max σ.toReal β / β⌉₊ : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
          rw [← hc]; exact le_self_add
        rw [fn_eq_of_jt p.1 hle hlt2, hf]
      · rw [closeDl_cut p hlt, ite_eq_right hf] at hlt2
        simp at hlt2

end ElboimSly.Cyclic

end
