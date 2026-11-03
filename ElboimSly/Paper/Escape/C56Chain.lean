/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Phases
public import Mathlib

/-!
# ES22 Claim 5.6: chaining the phases

ES22 Claim 5.6, "Conclusion".  `G_i = G_{i-1} ∩ ℬ_i`, so if
`c P(G_{i-1}) ≤ P(G_{i-1} ∩ ℬ_i)` for `1 ≤ i ≤ I`, then `c^I P(G_0) ≤ P(G_I)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Paper

variable {k : ℕ}

theorem EscG_succ_iff (β : ℝ) (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ)
    (y : ℝ → Fin (k + 2) → ℤ) (i : ℕ) :
    EscG β j u v z t y (i + 1) ↔ EscG β j u v z t y i ∧ EscBi β j u v z t y (i + 1) := by
  unfold EscG
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, fun i' h1 h2 => h i' h1 (by omega)⟩, h (i + 1) (by omega) le_rfl⟩
  · rintro ⟨⟨h0, h⟩, hb⟩
    refine ⟨h0, fun i' h1 h2 => ?_⟩
    rcases Nat.lt_or_ge i' (i + 1) with hlt | hge
    · exact h i' h1 (by omega)
    · have : i' = i + 1 := by omega
      subst this; exact hb

theorem chain_bound {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {c : ℝ≥0∞}
    (G : ℕ → Set Ω) (B : ℕ → Set Ω) (hG : ∀ i, G (i + 1) = G i ∩ B (i + 1)) {I : ℕ}
    (hstep : ∀ i, i < I → c * Pr (G i) ≤ Pr (G i ∩ B (i + 1))) :
    c ^ I * Pr (G 0) ≤ Pr (G I) := by
  induction I with
  | zero => simp
  | succ I ih =>
    have h1 := ih (fun i hi => hstep i (by omega))
    have h2 := hstep I (by omega)
    rw [hG I]
    calc c ^ (I + 1) * Pr (G 0) = c * (c ^ I * Pr (G 0)) := by ring
      _ ≤ c * Pr (G I) := by gcongr
      _ ≤ _ := h2

end ElboimSly.Paper.Escape

end
