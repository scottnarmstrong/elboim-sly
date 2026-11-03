/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5
public import ElboimSly.Paper.Escape.Plan5Stop
public import ElboimSly.Paper.Escape.VisitsG
public import ElboimSly.Paper.Heavy.Agree
public import Mathlib

/-!
# The pathwise conditions (1)-(7) imply the plan's conditions

The walks W_i and the stopping times tau_i.  `EscStopCond` (real-time, for the full walk `W_i`) at a time `t > 0`
implies `Cany` (for the record `ρ` of the earlier walks followed by the walk `W_i` cut at `t`), if the
earlier entries of `ρ` agree with the earlier walks (`EscAgree`).  Together with `stopLen_le_of_cond`
this gives `EscBefore` for the stopping lengths of the plan.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ}

/-- The earlier entries `ρ` of a record are the earlier walks `W ℓ` cut at their stopping times
`τ ℓ`. -/
structure EscAgree {m : ℕ} (W : ℕ → ℝ → Fin (k + 2) → ℤ) (τ : ℕ → ℝ)
    (ρ : CycRecN ℕ (k + 2) m) : Prop where
  len : ∀ ℓ : Fin m, (ρ ℓ).len = ENNReal.ofReal (τ (ℓ + 1))
  fn : ∀ (ℓ : Fin m) (s : ℝ≥0), (ρ ℓ).path.fn s = W (ℓ + 1) (min (s : ℝ) (τ (ℓ + 1)))
  nonneg : ∀ ℓ : Fin m, 0 ≤ τ (ℓ + 1)

theorem pathTfast_eq_of_nonneg {d : ℕ} {w w' : ℝ → Fin d → ℤ} (h : ∀ s, 0 ≤ s → w s = w' s)
    (L : ℝ) : pathTfast w L = pathTfast w' L := by
  have hset : {t : ℝ | 0 < t ∧ ∃ s : ℝ, t - 1 ≤ s ∧ s ≤ t ∧ L ≤ ‖w t - w (max s 0)‖} =
      {t : ℝ | 0 < t ∧ ∃ s : ℝ, t - 1 ≤ s ∧ s ≤ t ∧ L ≤ ‖w' t - w' (max s 0)‖} := by
    ext t
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨ht, s, h1, h2, h3⟩
      exact ⟨ht, s, h1, h2, by rwa [← h t ht.le, ← h _ (le_max_right _ _)]⟩
    · rintro ⟨ht, s, h1, h2, h3⟩
      exact ⟨ht, s, h1, h2, by rwa [h t ht.le, h _ (le_max_right _ _)]⟩
  unfold pathTfast
  rw [hset]

theorem pathTfast_sub_const {d : ℕ} (w : ℝ → Fin d → ℤ) (c : Fin d → ℤ) (L : ℝ) :
    pathTfast (fun s => w s - c) L = pathTfast w L := by
  unfold pathTfast
  simp only [sub_sub_sub_cancel_right]

theorem EscStopCond_imp_Cany {m : ℕ} (n : ℕ) (β : ℝ) (u : Fin (k + 2) → ℤ)
    (W : ℕ → ℝ → Fin (k + 2) → ℤ) (τ : ℕ → ℝ) (ρ : CycRecN ℕ (k + 2) m)
    (hag : EscAgree W τ ρ) (δ : CycData ℕ (k + 2)) (p : CycPath (k + 2))
    (hWi : ∀ s : ℝ, 0 ≤ s → W (m + 1) s = p.1.fn s.toNNReal)
    (hlog : 1 < Real.log β)
    {t : ℝ≥0} (_ht : 0 < t)
    (hc : EscStopCond n (escJ n) β (escIstar n (escJ n)) (escPoint n (escJ n) u) W
      (escBlockMinus (escJ n) u) (fun ℓ => if ℓ < m + 1 then τ ℓ else 0) (m + 1) (t : ℝ)) :
    (escRP n β u 0).Cany (m + 1) (CycRec.snoc ρ (δ, p.cut (t : ℝ≥0∞))) := by
  have hWt : W (m + 1) (t : ℝ) = p.1.fn t := by
    have := hWi (t : ℝ) t.2
    rwa [Real.toNNReal_coe] at this
  unfold EscStopCond at hc
  unfold EscRP.Cany EscRP.Cpos
  simp only [snoc_last']
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · refine Or.inl (Or.inl ?_)
    unfold escC1; rw [entEnd_cut, ← hWt]; exact h1
  · refine Or.inr (Or.inl ?_)
    unfold EscRP.C2
    rw [tm_cut, entEnd_cut, ← hWt]
    exact h2
  · refine Or.inr (Or.inr (Or.inl ?_))
    unfold EscRP.C3
    rw [tm_cut]
    have hL := escL_pos hlog (t : ℝ)
    have hwc := isCyclicPath_shift (p.cut (t : ℝ≥0∞))
    have hwp := isCyclicPath_shift p
    have hagree : ∀ s ∈ Icc (0 : ℝ) t, (fun s : ℝ => p.1.fn s.toNNReal - p.1.fn 0) s =
        (fun s : ℝ => (p.cut (t : ℝ≥0∞)).1.fn s.toNNReal - (p.cut (t : ℝ≥0∞)).1.fn 0) s := by
      intro s hs
      have e1 := cut_fn_apply δ p t s.toNNReal
      have e2 := cut_fn_apply δ p t 0
      unfold CycEntry.path at e1 e2
      simp only at e1 e2
      have hs' : s.toNNReal ≤ t := by
        rw [← Real.toNNReal_coe (r := t)]; exact Real.toNNReal_le_toNNReal hs.2
      show _ = (p.cut (t : ℝ≥0∞)).1.fn s.toNNReal - (p.cut (t : ℝ≥0∞)).1.fn 0
      rw [e1, e2, min_eq_left hs', min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)]
    show pathTfast (fun s : ℝ => (p.cut (t : ℝ≥0∞)).1.fn s.toNNReal - (p.cut (t : ℝ≥0∞)).1.fn 0)
      (escL β (t : ℝ)) ≤ ENNReal.ofReal t
    rw [← pathTfast_le_iff_of_agree hwp hwc hL (T := (t : ℝ)) t.2 hagree]
    rw [pathTfast_eq_of_nonneg (w' := fun s : ℝ => p.1.fn s.toNNReal)
      (fun s hs => by rw [hWi s hs]) _] at h3
    rw [pathTfast_sub_const (fun s : ℝ => p.1.fn s.toNNReal)]
    exact h3
  · refine Or.inl (Or.inr (Or.inl ?_))
    unfold EscRP.C4
    rw [entEnd_cut, ← hWt]
    exact h4
  · refine Or.inl (Or.inr (Or.inr (Or.inl ?_)))
    obtain ⟨ℓ', hℓ1, hℓ2, s, hs0, hsτ, hs⟩ := h5
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ : Fin m, ℓ' = (ℓ : ℕ) + 1 :=
      ⟨⟨ℓ' - 1, by omega⟩, by simp; omega⟩
    have hℓτ : ((fun ℓ => if ℓ < m + 1 then τ ℓ else 0) ((ℓ : ℕ) + 1)) = τ ((ℓ : ℕ) + 1) := by
      simp only [ite_eq_left hℓ2]
    rw [hℓτ] at hsτ
    refine ⟨(ℓ : ℕ) + 1, hℓ1, hℓ2, ?_, ?_⟩
    · have := ℓ.2
      simp [EscRP.idx, escRP]
    · have hidx : (escRP n β u 0).idx ((ℓ : ℕ) + 1) = ℓ := by simp [EscRP.idx, escRP]
      have hlt : ((escRP n β u 0).idx ((ℓ : ℕ) + 1)) < m := by rw [hidx]; exact ℓ.2
      have hh : (escRP n β u 0).idx ((ℓ : ℕ) + 1) < m + 1 := by omega
      rw [snoc_castSucc' ρ _ hlt hh]
      have e : (⟨(escRP n β u 0).idx ((ℓ : ℕ) + 1), hlt⟩ : Fin m) = ℓ := Fin.ext hidx
      rw [e]
      simp only [snoc_last']
      have hτ0 := hag.nonneg ℓ
      refine ⟨s.toNNReal, ?_, ?_⟩
      · rw [hag.len ℓ]
        exact ENNReal.ofReal_le_ofReal hsτ
      · rw [hag.fn ℓ, Real.coe_toNNReal _ hs0, min_eq_left hsτ, entEnd_cut, ← hWt]
        exact hs
  · refine Or.inl (Or.inr (Or.inr (Or.inr ?_)))
    unfold EscRP.C6
    rw [entEnd_cut, ← hWt]
    exact h6
  · refine Or.inr (Or.inr (Or.inr ?_))
    unfold EscRP.C7
    rw [tm_cut]
    exact h7

end ElboimSly.Paper.Escape
