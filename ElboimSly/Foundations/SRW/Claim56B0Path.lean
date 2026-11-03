/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Claim56PartT
public import ElboimSly.Foundations.SRW.KernelChain
public import Mathlib

/-!
# Claim 5.6, event `𝓑_0`: the windows and the pathwise argument
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {j m : ℕ} {t s₀ P N : ℝ}

/-- Window lengths. -/
noncomputable def rww (s₀ : ℝ) : ℕ → ℝ≥0
  | 0 => rhoA s₀
  | _ + 1 => dlt s₀

/-- Window boxes. -/
noncomputable def Qww (j : ℕ) (u : Fin d → ℤ) (t s₀ : ℝ) (v : Fin d → ℤ) : ℕ → Set (Fin d → ℤ)
  | 0 => QA j u s₀ v
  | k + 1 => QT j u t s₀ v k

/-- Window starting points. -/
noncomputable def xww (j : ℕ) (u : Fin d → ℤ) (t s₀ : ℝ) (v : Fin d → ℤ) : ℕ → Fin d → ℤ
  | 0 => v
  | k + 1 => pt j u t s₀ v k

/-- Window end points. -/
noncomputable def zww (j : ℕ) (u : Fin d → ℤ) (t s₀ : ℝ) (v : Fin d → ℤ) (k : ℕ) : Fin d → ℤ :=
  pt j u t s₀ v k

theorem sum_rww (s₀ : ℝ) (i : ℕ) : ∑ k ∈ Finset.range (i + 1), rww s₀ (0 + k) = sT s₀ i := by
  induction i with
  | zero => simp [rww, sT_zero]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, sT_succ]
    simp [rww]

theorem Ctx.path_B0 (c : Ctx j m t s₀ P N) (u v : Fin d → ℤ) (hv : v ∈ claimBox u j) (hj : 1 ≤ j)
    {γ : PathSpace d} (hγ : IsRegularPath γ)
    (hG : γ ∈ Gfrom (rww s₀) (kerV (Qww j u t s₀ v) (rww s₀) (xww j u t s₀ v)
      (zww j u t s₀ v)) 0 201) :
    (∀ s : ℝ≥0, s ≤ sT s₀ 200 → v + γ s ∈ claimBox u j) ∧
    (∀ s : ℝ≥0, rhoA s₀ ≤ s → s ≤ sT s₀ 200 →
      ∀ i, |((v + γ s) i : ℝ) - claimFv j u t v s i| ≤ s₀ / 32) := by
  have hSΓ : ∀ k (β : PathSpace d), IsRegularPath β →
      (stopPath (rww s₀ k) β ∈ kerV (Qww j u t s₀ v) (rww s₀) (xww j u t s₀ v)
        (zww j u t s₀ v) k ↔
        β ∈ kerSet (Qww j u t s₀ v k) (rww s₀ k) (xww j u t s₀ v k) (zww j u t s₀ v k)) :=
    fun k β hβ => kerV_stop _ _ _ _ k hβ
  obtain ⟨h0, hW⟩ := mem_Gfrom_regular_gen hSΓ 200 0 hγ hG
  have h0' : v + γ (rhoA s₀) = pt j u t s₀ v 0 ∧ ∀ s : ℝ≥0, s ≤ rhoA s₀ → v + γ s ∈ QA j u s₀ v := h0
  have hW' : ∀ i < 200, pt j u t s₀ v i + (γ (sT s₀ i + dlt s₀) - γ (sT s₀ i)) =
      pt j u t s₀ v (i + 1) ∧ ∀ w : ℝ≥0, w ≤ dlt s₀ →
        pt j u t s₀ v i + (γ (sT s₀ i + w) - γ (sT s₀ i)) ∈ QT j u t s₀ v i := by
    intro i hi
    have := hW i hi
    rw [sum_rww] at this
    simp only [zero_add] at this
    exact this
  -- positions at the grid times
  have hpos : ∀ k ≤ 200, v + γ (sT s₀ k) = pt j u t s₀ v k := by
    intro k
    induction k with
    | zero => intro _; rw [sT_zero]; exact h0'.1
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := (hW' k (by omega)).1
      rw [sT_succ]
      have : v + γ (sT s₀ k + dlt s₀) = pt j u t s₀ v k + (γ (sT s₀ k + dlt s₀) - γ (sT s₀ k)) := by
        rw [← h1]; abel
      rw [this, h2]
  -- containment and closeness by induction
  have hmain : ∀ n ≤ 200, (∀ s : ℝ≥0, s ≤ sT s₀ n → v + γ s ∈ claimBox u j) ∧
      (∀ s : ℝ≥0, rhoA s₀ ≤ s → s ≤ sT s₀ n →
        ∀ i, |((v + γ s) i : ℝ) - claimFv j u t v s i| ≤ s₀ / 32) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨fun s hs => ?_, fun s hs1 hs2 i => ?_⟩
      · rw [sT_zero] at hs
        exact c.QA_sub u v hv hj (h0'.2 s hs)
      · rw [sT_zero] at hs2
        have hse : s = rhoA s₀ := le_antisymm hs2 hs1
        rw [hse]
        have h3 : (v + γ (rhoA s₀)) = pt j u t s₀ v 0 := h0'.1
        have hcl := pt_close j u t s₀ v 0 i
        rw [sT_zero] at hcl
        rw [h3]
        refine hcl.trans ?_
        linarith [c.s288]
    | succ n ih =>
      intro hn
      obtain ⟨ihA, ihB⟩ := ih (by omega)
      have hw := hW' n (by omega)
      refine ⟨fun s hs => ?_, fun s hs1 hs2 i => ?_⟩
      · rcases le_or_gt s (sT s₀ n) with h | h
        · exact ihA s h
        · have hu : s - sT s₀ n ≤ dlt s₀ := by
            rw [tsub_le_iff_left, ← sT_succ]; exact hs
          have hmem := hw.2 _ hu
          rw [add_tsub_cancel_of_le h.le] at hmem
          have e : v + γ s = pt j u t s₀ v n + (γ s - γ (sT s₀ n)) := by
            rw [← hpos n (by omega)]; abel
          rw [e]
          exact c.QT_sub u v hv hj (by omega) hmem
      · rcases le_or_gt s (sT s₀ n) with h | h
        · exact ihB s hs1 h i
        · have hu : s - sT s₀ n ≤ dlt s₀ := by
            rw [tsub_le_iff_left, ← sT_succ]; exact hs2
          have hmem := hw.2 _ hu
          rw [add_tsub_cancel_of_le h.le] at hmem
          have e : v + γ s = pt j u t s₀ v n + (γ s - γ (sT s₀ n)) := by
            rw [← hpos n (by omega)]; abel
          rw [e]
          exact c.close_T u v hv hj (k := n) (by omega) hmem h.le hs2 i
  exact hmain 200 le_rfl

end SRW
end ElboimSly
