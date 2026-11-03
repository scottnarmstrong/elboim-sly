/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.TwoParticleProps
public import Mathlib

/-!
# Two particles: the counting bound

Two particles: deterministic properties (c), the final bound: for every `s ≥ 0`,
`‖E(s)‖ ≤ ‖E(s)‖₁ ≤ #{r ∈ (0, s] : ‖D(r-)‖₁ = 1 and `x₁` or `x₂` jumps at `r`}`.
-/

@[expose] public section

open Set Filter Topology Function
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base

variable {d : ℕ}

theorem l1_add_le (u v : Fin d → ℤ) : l1 (u + v) ≤ l1 u + l1 v := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le _ _

/-- The contact times in `(0, s]`: where `‖D(r-)‖₁ = 1` and `x₁` or `x₂` jumps. -/
def contactSet (a : Fin d → ℤ) (x₁ x₂ y : ℝ≥0 → Fin d → ℤ) (s : ℝ≥0) : Set ℝ≥0 :=
  {r | 0 < r ∧ r ≤ s ∧ l1 (leftLim y r - (a + leftLim x₁ r)) = 1 ∧
    (r ∈ CDisc x₁ ∨ r ∈ CDisc x₂)}

variable {a b : Fin d → ℤ} {x₁ x₂ y : ℝ≥0 → Fin d → ℤ}

theorem contactSet_finite (h : TwoParticleData a b x₁ x₂ y) (s : ℝ≥0) :
    (contactSet a x₁ x₂ y s).Finite :=
  ((h.hx₁.step.fin s).union (h.hx₂.step.fin s)).subset fun r hr => by
    rcases hr.2.2.2 with m | m
    · exact Or.inl ⟨m, hr.2.1⟩
    · exact Or.inr ⟨m, hr.2.1⟩

theorem contactSet_mono (s s' : ℝ≥0) (hss : s ≤ s') :
    contactSet a x₁ x₂ y s ⊆ contactSet a x₁ x₂ y s' :=
  fun _r hr => ⟨hr.1, hr.2.1.trans hss, hr.2.2⟩

/-- (c), the counting bound: `‖E(s)‖₁` is at most the number of contacts in `(0, s]`. -/
theorem TwoParticleData.l1_E_le (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b) (s : ℝ≥0) :
    l1 (y s - b - x₂ s) ≤ ((contactSet a x₁ x₂ y s).ncard : ℤ) := by
  have hz := isStepPath_pair h.hx₁.step h.hx₂.step
  refine real_induction (Q := fun s => l1 (y s - b - x₂ s) ≤
    ((contactSet a x₁ x₂ y s).ncard : ℤ)) ?_ ?_ ?_ s
  · simp only [h.hy.zero, h.hx₂.zero, sub_self]
    have : l1 (0 : Fin d → ℤ) = 0 := (l1_eq_zero_iff _).2 rfl
    rw [this]; exact Int.natCast_nonneg _
  · intro r hr hev
    have := neBot_nhdsLT_of_pos hr
    obtain ⟨t, htr, ht⟩ := hz.exists_left_gap hr
    have hsub : ∀ u, t < u → u < r →
        contactSet a x₁ x₂ y u = contactSet a x₁ x₂ y r \ {r} := by
      intro u htu hur
      ext x
      simp only [contactSet, mem_ofPred_eq, Set.mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨h0, hxu, h1, h2⟩
        exact ⟨⟨h0, hxu.trans hur.le, h1, h2⟩, (hxu.trans_lt hur).ne⟩
      · rintro ⟨⟨h0, hxr, h1, h2⟩, hne⟩
        refine ⟨h0, ?_, h1, h2⟩
        by_contra hxu
        have hd : x ∈ CDisc (fun s => (x₁ s, x₂ s)) := by
          rcases h2 with m | m
          · by_contra hn
            exact (notMem_pair hn).1 m
          · by_contra hn
            exact (notMem_pair hn).2 m
        exact ht x hd (htu.trans (not_le.mp hxu)) (lt_of_le_of_ne hxr hne)
    obtain ⟨u, ⟨hu1, hu2⟩, hu3, hu4, hu5⟩ := ((show ∀ᶠ u in 𝓝[<] r, u ∈ Ioo t r from
      Ioo_mem_nhdsLT htr).and (hev.and ((h.hy.step.eventually_left_leftLim hr).and
        (h.hx₂.step.eventually_left_leftLim hr)))).exists
    have hfin := contactSet_finite h r
    have hle : l1 (leftLim y r - b - leftLim x₂ r) ≤
        ((contactSet a x₁ x₂ y r \ {r}).ncard : ℤ) := by
      rw [← hsub u hu1 hu2, ← hu4, ← hu5]
      have : y u - b - x₂ u = y u - b - x₂ u := rfl
      exact hu3
    have hdiff : (contactSet a x₁ x₂ y r \ {r}).ncard ≤ (contactSet a x₁ x₂ y r).ncard :=
      Set.ncard_le_ncard sdiff_subset hfin
    by_cases hE : y r - b - x₂ r = leftLim y r - b - leftLim x₂ r
    · rw [hE]; exact hle.trans (by exact_mod_cast hdiff)
    · obtain ⟨c1, c2, c3⟩ := h.E_jump hab hr hE
      have hmem : r ∈ contactSet a x₁ x₂ y r := ⟨hr, le_rfl, c1, c2⟩
      have hcard := Set.ncard_sdiff_singleton_of_mem hmem
      have hpos : 0 < (contactSet a x₁ x₂ y r).ncard := (Set.ncard_pos hfin).2 ⟨r, hmem⟩
      have htri : l1 (y r - b - x₂ r) ≤ l1 (leftLim y r - b - leftLim x₂ r) + 1 := by
        have := l1_add_le (leftLim y r - b - leftLim x₂ r)
          ((y r - b - x₂ r) - (leftLim y r - b - leftLim x₂ r))
        rw [c3] at this
        simpa using this
      have : ((contactSet a x₁ x₂ y r \ {r}).ncard : ℤ) + 1 =
          ((contactSet a x₁ x₂ y r).ncard : ℤ) := by
        rw [hcard]; omega
      omega
  · intro r hrQ
    filter_upwards [h.hy.step.rc r, h.hx₂.step.rc r, self_mem_nhdsWithin] with u h1 h2 h3
    rw [h1, h2]
    exact hrQ.trans (Int.ofNat_le.2
      (Set.ncard_le_ncard (contactSet_mono r u h3) (contactSet_finite h u)))

/-- (c), the counting bound in the sup norm: `‖E(s)‖ ≤ ‖E(s)‖₁ ≤ #contacts in (0, s]`. -/
theorem TwoParticleData.norm_E_le (h : TwoParticleData a b x₁ x₂ y) (hab : a ≠ b) (s : ℝ≥0) :
    ‖y s - b - x₂ s‖ ≤ ((contactSet a x₁ x₂ y s).ncard : ℝ) :=
  (norm_le_l1 _).trans (by exact_mod_cast h.l1_E_le hab s)

end ElboimSly.Paper
