/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasPath

/-!
# The remaining statements

* `heavyEntSeq_eq_entrance`: on `{s_i(B) < ∞}`, `s_i(B) = ξ_{B''}` for some sub-block `B''`.
* `isStoppingTime_min_treg_tauV`: `t_n ∧ T_reg ∧ τ_V` is a stopping time.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {w : ℝ → Fin d → ℤ} {j m : ℕ} {D : ℝ≥0∞} {ι : Fin d → ℤ}

/-- Measurability (a), last claim. -/
theorem heavyEntSeq_eq_entrance (hw : IsCyclicPath w) (hjm : j ≤ m) :
    ∀ i : ℕ, heavyEntSeq w j m D ι i < ⊤ →
      ∃ ι' ∈ heavySubIdx d j m ι, heavyEntSeq w j m D ι i = entranceTime w (heavyBlock j ι')
  | 0, h => by
    have h0 : entranceTime w (heavyBlock m ι) < ⊤ := h
    obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ entranceTime w (heavyBlock m ι) ≤ ENNReal.ofReal T :=
      ⟨(entranceTime w (heavyBlock m ι)).toReal, ENNReal.toReal_nonneg, by
        rw [ENNReal.ofReal_toReal h0.ne]⟩
    have hne : ∃ s : ℝ, 0 ≤ s ∧ w s ∈ heavyBlock m ι := by
      by_contra hno
      push Not at hno
      rw [entranceTime_eq_top_of_empty hno] at h0
      exact absurd h0 (by simp)
    obtain ⟨s, hs0, hsB⟩ := hne
    obtain ⟨s'', h0', -, hmem, heq⟩ := exists_entrance_real hw hs0 hsB
    have hsub : heavyBlock j (heavyBlockIdx j (w s'')) ⊆ heavyBlock m ι :=
      heavyBlock_refine hjm (mem_heavyBlock_idx j (w s'')) hmem
    refine ⟨heavyBlockIdx j (w s''), hsub, ?_⟩
    show entranceTime w (heavyBlock m ι) = _
    exact le_antisymm (entranceTime_mono hsub w)
      ((entranceTime_le_of_mem h0' (mem_heavyBlock_idx j (w s''))).trans heq.ge)
  | i + 1, h => by
    have hS : {x ∈ heavyEntrances w j m ι | heavyEntSeq w j m D ι i + D ≤ x}.Finite :=
      (heavyEntrances_finite w j m ι).subset fun x hx => hx.1
    have hne : {x ∈ heavyEntrances w j m ι | heavyEntSeq w j m D ι i + D ≤ x}.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      have : heavyEntSeq w j m D ι (i + 1) = ⊤ := by
        show sInf _ = _
        rw [hemp]; exact sInf_empty
      exact absurd h (by simp [this])
    obtain ⟨⟨ι', hι', hx⟩, -⟩ := hne.csInf_mem hS
    exact ⟨ι', hι', hx.symm⟩

end ElboimSly.Paper
