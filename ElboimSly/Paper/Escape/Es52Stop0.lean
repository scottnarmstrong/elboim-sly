/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Incl
public import ElboimSly.Foundations.Cyclic.CycClosingStopLen
public import ElboimSly.Paper.Escape.Plan5Entries
public import ElboimSly.Paper.Escape.Plan5Fin
public import Mathlib

/-!
# The stopping length of walk `1` of `𝒫₅`

For a path `p`, the stopping length of walk `1` of `𝒫₅(B, β', i)` is
`min(ξ_B(p), treg(p), t_n)`: the first entrance into `B`, the closing time, or the length cap.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The first entrance time of a path into a set. -/
noncomputable def pathXi (f : ℝ≥0 → Fin (k + 2) → ℤ) (B : Set (Fin (k + 2) → ℤ)) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : f t ∈ B), (t : ℝ≥0∞)

theorem pathXi_le {f : ℝ≥0 → Fin (k + 2) → ℤ} {B : Set (Fin (k + 2) → ℤ)} {s : ℝ≥0}
    (h : f s ∈ B) : pathXi f B ≤ s :=
  iInf₂_le s h

theorem le_pathXi {f : ℝ≥0 → Fin (k + 2) → ℤ} {B : Set (Fin (k + 2) → ℤ)} {m : ℝ≥0∞}
    (h : ∀ s : ℝ≥0, f s ∈ B → m ≤ s) : m ≤ pathXi f B :=
  le_iInf₂ fun s hs => h s hs

theorem escXi_eq_pathXi (W : ℝ → Fin (k + 2) → ℤ) (B : Set (Fin (k + 2) → ℤ)) :
    escXi W B = pathXi (fun t : ℝ≥0 => W (t : ℝ)) B := rfl

section walk0

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)

theorem hat0_last (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (a : ℕ) :
    (plan5 n β tn u β' i hlog).hatRec 0 ρ p a (Fin.last 0) =
      ((plan5 n β tn u β' i hlog).start 0 ρ, p.cut (p.1.jt a)) := by
  unfold CycPlan.hatRec
  exact snoc_last' _ _

theorem plan5_st0_eq (ρ' : CycRecN ℕ (k + 2) 1) :
    (plan5 n β tn u β' i hlog).st 0 ρ' = plan5St0 β (escJ n) u ρ' := rfl

theorem plan5_dl0_eq (ρ' : CycRecN ℕ (k + 2) 1) :
    (plan5 n β tn u β' i hlog).dl 0 ρ' = plan5Dl0 β tn (escJ n) u ρ' := rfl

open Classical in
theorem plan5_st0 (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (a : ℕ) :
    (plan5 n β tn u β' i hlog).st 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) =
      (closeSt β (p.cut (p.1.jt a)) ||
        decide (entEnd (((plan5 n β tn u β' i hlog).start 0 ρ, p.cut (p.1.jt a)) :
          CycEntry ℕ (k + 2)) ∈ escBlock (escJ n) u)) := by
  rw [plan5_st0_eq]
  unfold plan5St0
  rw [hat0_last n tn u β' i hlog]

open Classical in
theorem plan5_dl0 (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (a : ℕ) :
    (plan5 n β tn u β' i hlog).dl 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) =
      (if entEnd (((plan5 n β tn u β' i hlog).start 0 ρ, p.cut (p.1.jt a)) :
          CycEntry ℕ (k + 2)) ∈ escBlock (escJ n) u then 0
      else min (closeDl β (p.cut (p.1.jt a)))
        (ENNReal.ofReal tn - (p.cut (p.1.jt a)).1.len)) := by
  rw [plan5_dl0_eq]
  unfold plan5Dl0
  rw [hat0_last n tn u β' i hlog]
  rfl

/-- Lower bound for the stopping length of walk `1`. -/
theorem plan5_stopLen0_ge (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (_hp : p.1.len = ⊤)
    {m : ℝ≥0∞} (hξ : ∀ s : ℝ≥0, p.1.fn s ∈ escBlock (escJ n) u → m ≤ s)
    (hr : ∀ j : ℕ, 1 ≤ j → p.1.fn ((j : ℝ≥0) * β.toNNReal) = 0 → m ≤ ENNReal.ofReal (j * β))
    (hn : m ≤ ENNReal.ofReal tn) : m ≤ (plan5 n β tn u β' i hlog).stopLen 0 ρ p := by
  classical
  unfold CycPlan.stopLen
  refine le_sInf ?_
  rintro t (⟨a, ha, hlt, hst, rfl⟩ | ⟨a, hlt, rfl, hlt2⟩)
  · rw [plan5_st0] at hst
    obtain ⟨r, hr'⟩ : ∃ r : ℝ≥0, p.1.jt a = r := ⟨_, (ENNReal.coe_toNNReal hlt.ne).symm⟩
    rw [hr'] at hst ⊢
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hst
    rcases hst with hc | hb
    · rw [closeSt_cut_iff p ENNReal.coe_lt_top] at hc
      obtain ⟨j, hj, h1, h2⟩ := hc
      have h3 : r = (j : ℝ≥0) * β.toNNReal := by
        have := h1; rw [ofReal_nat_mul] at this; exact_mod_cast this
      rw [h1]
      refine hr j hj ?_
      rw [← h3]; simpa using h2
    · rw [entEnd_cut] at hb
      exact hξ r hb
  · obtain ⟨r, hr'⟩ : ∃ r : ℝ≥0, p.1.jt a = r := ⟨_, (ENNReal.coe_toNNReal hlt.ne).symm⟩
    rw [plan5_dl0] at hlt2 ⊢
    rw [hr'] at hlt2 ⊢
    by_cases hb : entEnd (((plan5 n β tn u β' i hlog).start 0 ρ, p.cut (r : ℝ≥0∞)) :
        CycEntry ℕ (k + 2)) ∈ escBlock (escJ n) u
    · rw [ite_eq_left hb, add_zero]
      rw [entEnd_cut] at hb
      exact hξ r hb
    · rw [ite_eq_right hb]
      have hlen : (p.cut (r : ℝ≥0∞)).1.len = r := by
        simp [CycPath.cut, CPath.cut_len]
      rw [hlen]
      rw [ite_eq_right hb] at hlt2
      rw [hlen] at hlt2
      by_cases hc : closeDl β (p.cut (r : ℝ≥0∞)) ≤ ENNReal.ofReal tn - r
      · rw [min_eq_left hc] at hlt2 ⊢
        have hctop : closeDl β (p.cut (r : ℝ≥0∞)) ≠ ⊤ :=
          ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self) hc
        rw [closeDl_cut p ENNReal.coe_lt_top] at hctop hlt2 ⊢
        rw [ENNReal.toNNReal_coe, ENNReal.coe_toReal] at hctop hlt2 ⊢
        by_cases hf : p.1.fn r = 0
        · rw [ite_eq_left hf] at hctop hlt2 ⊢
          obtain ⟨hn1, hn2, -⟩ := dl_facts (β := β) (r : ℝ) r.2
          have hX : (r : ℝ≥0∞) ≤ ENNReal.ofReal (β * (⌈max (r : ℝ) β / β⌉₊ : ℕ)) := by
            rw [← ENNReal.ofReal_coe_nnreal, mul_comm]
            exact ENNReal.ofReal_le_ofReal hn2
          rw [add_tsub_cancel_of_le hX] at hlt2 ⊢
          have hc2 : ENNReal.ofReal (β * (⌈max (r : ℝ) β / β⌉₊ : ℕ)) =
              (((⌈max (r : ℝ) β / β⌉₊ : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [mul_comm, ofReal_nat_mul]
          rw [hc2] at hlt2 ⊢
          have hle : (r : ℝ≥0∞) ≤ (((⌈max (r : ℝ) β / β⌉₊ : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
            rw [← hc2]; exact hX
          have hf0 : p.1.fn ((⌈max (r : ℝ) β / β⌉₊ : ℝ≥0) * β.toNNReal) = 0 := by
            have := fn_eq_of_jt p.1 (a := a) (s := (⌈max (r : ℝ) β / β⌉₊ : ℝ≥0) * β.toNNReal)
              (by rw [hr']; exact hle) hlt2
            rw [this, hr', ENNReal.toNNReal_coe]; exact hf
          rw [← ofReal_nat_mul]
          exact hr _ hn1 hf0
        · rw [ite_eq_right hf] at hctop
          exact absurd rfl hctop
      · rw [min_eq_right (le_of_not_ge hc)]
        exact hn.trans le_add_tsub

open Classical in
theorem plan5_dl0_le_closeDl (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (a : ℕ) :
    (plan5 n β tn u β' i hlog).dl 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) ≤
      closeDl β (p.cut (p.1.jt a)) := by
  rw [plan5_dl0]
  split_ifs
  · exact zero_le
  · exact min_le_left _ _

/-- Walk `1` stops by the closing time. -/
theorem plan5_stopLen0_le_treg (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) :
    (plan5 n β tn u β' i hlog).stopLen 0 ρ p ≤ pathTreg β.toNNReal p.1.fn := by
  classical
  have hβ : 0 < β := Fact.out
  have hβ' : (0 : ℝ≥0) < β.toNNReal := Real.toNNReal_pos.2 hβ
  have hcoe : ((β.toNNReal : ℝ≥0) : ℝ) = β := Real.coe_toNNReal β hβ.le
  unfold pathTreg
  refine le_iInf fun jj => ?_
  obtain ⟨j, hj, h0⟩ := jj
  set s : ℝ≥0 := (j : ℝ≥0) * β.toNNReal with hs_def
  have hspos : 0 < s := mul_pos (by exact_mod_cast hj) hβ'
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
  unfold CycPlan.stopLen
  rcases hja.eq_or_lt with heq | hlt'
  · have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, jt_zero'] at heq
        exact absurd (by exact_mod_cast heq.symm : (s : ℝ≥0) = 0) hspos.ne'
      · exact h
    refine (sInf_le ?_).trans heq.le
    refine Or.inl ⟨a, ha1, hlt, ?_, rfl⟩
    rw [plan5_st0]
    have : closeSt β (p.cut (p.1.jt a)) = true := by
      rw [closeSt_cut_iff p hlt]
      refine ⟨j, hj, ?_, hfa⟩
      rw [heq, hs_def, ofReal_nat_mul]
    simp [this]
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
    have hd := plan5_dl0_le_closeDl n tn u β' i hlog ρ p a
    refine (sInf_le (a := p.1.jt a + (plan5 n β tn u β' i hlog).dl 0
      ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a)) ?_).trans ?_
    · refine Or.inr ⟨a, hlt, rfl, ?_⟩
      refine lt_of_le_of_lt ?_ hjb
      calc σ + _ ≤ σ + closeDl β (p.cut σ) := add_le_add le_rfl hd
        _ ≤ s := by rw [hc]; exact hXs
    · calc σ + _ ≤ σ + closeDl β (p.cut σ) := add_le_add le_rfl hd
        _ ≤ s := by rw [hc]; exact hXs

/-- Walk `1` stops when the path is in `B`. -/
theorem plan5_stopLen0_le_xi (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) :
    (plan5 n β tn u β' i hlog).stopLen 0 ρ p ≤ pathXi p.1.fn (escBlock (escJ n) u) :=
  le_iInf₂ fun s hs => stopLen_plan5_zero_le n tn u β' i hlog ρ p s hs

/-- Walk `1` stops by time `t_n`. -/
theorem plan5_stopLen0_le_tn (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) :
    (plan5 n β tn u β' i hlog).stopLen 0 ρ p ≤ ENNReal.ofReal tn := by
  classical
  refine stopLen_le_of_dl_le _ 0 ρ p ENNReal.ofReal_ne_top fun ρ' => ?_
  show plan5Dl0 β tn (escJ n) u ρ' ≤ _
  unfold plan5Dl0
  split_ifs
  · exact zero_le
  · exact min_le_right _ _

/-- **The stopping length of walk `1` of `𝒫₅`**: `min(ξ_B, treg, t_n)`. -/
theorem plan5_stopLen0_eq (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2)) (hp : p.1.len = ⊤) :
    (plan5 n β tn u β' i hlog).stopLen 0 ρ p =
      min (min (pathXi p.1.fn (escBlock (escJ n) u)) (pathTreg β.toNNReal p.1.fn))
        (ENNReal.ofReal tn) := by
  refine le_antisymm (le_min (le_min (plan5_stopLen0_le_xi n tn u β' i hlog ρ p)
    (plan5_stopLen0_le_treg n tn u β' i hlog ρ p)) (plan5_stopLen0_le_tn n tn u β' i hlog ρ p)) ?_
  refine plan5_stopLen0_ge n tn u β' i hlog ρ p hp ?_ ?_ (min_le_right _ _)
  · intro s hs
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (pathXi_le hs))
  · intro j hj h0
    refine (min_le_left _ _).trans ((min_le_right _ _).trans ?_)
    unfold pathTreg
    rw [ofReal_nat_mul]
    exact iInf_le (fun kk : {kk : ℕ // 1 ≤ kk ∧ p.1.fn ((kk : ℝ≥0) * β.toNNReal) = 0} =>
      (((kk.1 : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞)) ⟨j, hj, h0⟩

end walk0

end ElboimSly.Paper.Escape
