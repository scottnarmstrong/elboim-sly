/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ThitPieces
public import Mathlib

/-!
# A deterministic characterisation of `thit(R) ≤ t`

Structure of relaxed times; stopping times (d), the part for `thit(R)`.

For a fixed path `W` (with the sets `{s : ‖W s - W (s - jβ)‖ ≤ 1}` locally of type `[l, r)`), a
fixed `r ≥ 0` and `A r` (the value of the regeneration function at `r`), we have
`thit(r) ≤ t` iff for some `j ≥ 1` there is a `u ≤ t` with `‖W u - W (u - jβ)‖ ≤ 1`,
`max (A r + jβ) r ≤ u < r + jβ`.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

theorem mem_hit_iff {β : ℝ} (hβ : 0 < β) {W : ℝ → Fin d → ℤ} {A : ℝ → ℝ} {r : ℝ} (s : ℝ) :
    (r < s ∧ ∃ s' : ℝ, (∃ k : ℤ, s' = s + k * β) ∧ A r < s' ∧ s' < r ∧ ‖W s - W s'‖ ≤ 1) ↔
      ∃ j : ℕ, 1 ≤ j ∧ s ∈ stepVj β W j ∧ max (A r + j * β) r < s ∧ s < r + j * β := by
  constructor
  · rintro ⟨hrs, s', ⟨k, hk⟩, hAs, hsr, hn⟩
    have hk0 : k < 0 := by
      by_contra hk0
      push Not at hk0
      have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
      nlinarith
    refine ⟨(-k).toNat, by omega, ?_⟩
    have hj : (((-k).toNat : ℕ) : ℝ) = -(k : ℝ) := by
      have h1 : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have h2 : (((-k).toNat : ℕ) : ℝ) = ((((-k).toNat : ℕ) : ℤ) : ℝ) := by norm_cast
      rw [h2, h1]; push_cast; ring
    rw [hj]
    have hs' : s' = s - (-(k : ℝ)) * β := by rw [hk]; ring
    refine ⟨?_, max_lt (by nlinarith) hrs, by nlinarith⟩
    simp only [stepVj, mem_ofPred_eq, hj]
    rw [← hs']
    exact hn
  · rintro ⟨j, hj, hV, hl, hr⟩
    refine ⟨(max_lt_iff.1 hl).2, s - j * β, ⟨-(j : ℤ), by push_cast; ring⟩, by
      linarith [(max_lt_iff.1 hl).1], by linarith, hV⟩

/-- The deterministic characterisation of `thit(r) ≤ t`. -/
theorem stepThit_le_iff {β : ℝ} (hβ : 0 < β) {W : ℝ → Fin d → ℤ} {A : ℝ → ℝ}
    (hV : ∀ j : ℕ, IsLocIco (stepVj β W j)) {r : ℝ} (hr : 0 ≤ r) (t : ℝ≥0) :
    stepThit β W A r ≤ ENNReal.ofReal t ↔
      ∃ j : ℕ, 1 ≤ j ∧ ∃ u : ℝ, u ∈ stepVj β W j ∧ max (A r + j * β) r ≤ u ∧ u < r + j * β ∧
        u ≤ t := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    -- a lower bound for each `H j`
    have L1 : ∀ j : ℕ, ∃ m : ℝ, (t : ℝ) < m ∧ ∀ s : ℝ, s ∈ stepVj β W j →
        max (A r + j * β) r < s → s < r + j * β → m ≤ s := by
      intro j
      by_cases hne : ∃ s : ℝ, s ∈ stepVj β W j ∧ max (A r + j * β) r < s ∧ s < r + j * β
      · have hj1 : 1 ≤ j := by
          obtain ⟨s, -, h1, h2⟩ := hne
          by_contra hj0
          have : j = 0 := by omega
          subst this
          simp only [Nat.cast_zero, zero_mul, add_zero] at h1 h2
          exact absurd (lt_of_le_of_lt (le_max_right _ _) h1) (not_lt.2 h2.le)
        set U := stepVj β W j ∩ Ico (max (A r + j * β) r) (r + j * β) with hU
        have hUloc : IsLocIco U := (hV j).inter (isLocIco_Ico _ _)
        obtain ⟨s, hsV, hs1, hs2⟩ := hne
        obtain ⟨m, hmU, hcm, hlow, -⟩ := hUloc.sInf_eq_min (c := max (A r + j * β) r)
          (hr.trans (le_max_right _ _)) ⟨s, ⟨hsV, hs1.le, hs2⟩, hs1⟩
        exact ⟨m, hno j hj1 m hmU.1 hmU.2.1 hmU.2.2,
          fun s' hs'V hs'1 hs'2 => hlow s' ⟨hs'V, hs'1.le, hs'2⟩ hs'1.le⟩
      · refine ⟨t + 1, by linarith, fun s hsV hs1 hs2 => absurd ⟨s, hsV, hs1, hs2⟩ hne⟩
    choose m hmt hmH using L1
    set J : ℕ := ⌈((t : ℝ) - A r) / β⌉₊ with hJ
    have hJ' : ((t : ℝ) - A r) / β ≤ J := Nat.le_ceil _
    have hJ'' : (t : ℝ) < A r + (J + 1 : ℕ) * β := by
      have := (div_le_iff₀ hβ).1 hJ'
      push_cast
      nlinarith
    have hne : (Finset.range (J + 1)).Nonempty := ⟨0, by simp⟩
    set mm : ℝ := min (A r + (J + 1 : ℕ) * β)
      ((Finset.range (J + 1)).inf' hne m) with hmm
    have hmmt : (t : ℝ) < mm := by
      refine lt_min hJ'' ?_
      obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_inf' hne m
      rw [hb]
      exact hmt b
    have hlow : ENNReal.ofReal mm ≤ stepThit β W A r := by
      refine le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal ?_
      obtain ⟨j, -, hsV, hs1, hs2⟩ := (mem_hit_iff hβ s).1 hs
      by_cases hjJ : j ≤ J
      · exact (min_le_right _ _).trans
          (((Finset.inf'_le m (Finset.mem_range.2 (Nat.lt_succ_of_le hjJ)))).trans
            (hmH j s hsV hs1 hs2))
      · push Not at hjJ
        refine (min_le_left _ _).trans ?_
        have hjβ : ((J + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hjJ
        have := (max_lt_iff.1 hs1).1
        nlinarith
    have hmm0 : 0 < mm := lt_of_le_of_lt t.2 hmmt
    exact absurd (h.trans' hlow) (not_le.2 ((ENNReal.ofReal_lt_ofReal_iff hmm0).2 hmmt))
  · rintro ⟨j, hj, u, huV, hl, hu, hut⟩
    have hu0 : 0 ≤ u := hr.trans ((le_max_right _ _).trans hl)
    obtain ⟨ε', hε', hsub⟩ := (hV j).exists_Ico hu0 huV
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set δ : ℝ := min (ε' / 2) (min ((r + j * β - u) / 2) (ε / 2)) with hδ
    have hε0 : (0 : ℝ) < ε := by exact_mod_cast hε
    have hδ0 : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hδ1 : δ ≤ ε' / 2 := min_le_left _ _
    have hδ2 : δ ≤ (r + j * β - u) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ3 : δ ≤ ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hmem : u + δ ∈ stepVj β W j := hsub ⟨by linarith, by linarith⟩
    have hhit : r < u + δ ∧ ∃ s' : ℝ, (∃ k : ℤ, s' = u + δ + k * β) ∧ A r < s' ∧ s' < r ∧
        ‖W (u + δ) - W s'‖ ≤ 1 :=
      (mem_hit_iff hβ (u + δ)).2 ⟨j, hj, hmem, max_lt_iff.2 ⟨by linarith [(max_le_iff.1 hl).1],
        by linarith [(max_le_iff.1 hl).2]⟩, by linarith⟩
    calc stepThit β W A r ≤ ENNReal.ofReal (u + δ) := iInf₂_le (u + δ) hhit
      _ ≤ ENNReal.ofReal ((t : ℝ) + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal t + ε := by
        rw [ENNReal.ofReal_add (NNReal.coe_nonneg t) hε0.le, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

/-- Rational reduction: the witness `u` in `stepThit_le_iff` can be taken to be `t` or a rational
`q ∈ [0, t)`. -/
theorem stepThit_le_iff_rat {β : ℝ} (hβ : 0 < β) {W : ℝ → Fin d → ℤ} {A : ℝ → ℝ}
    (hV : ∀ j : ℕ, IsLocIco (stepVj β W j)) {r : ℝ} (hr : 0 ≤ r) (t : ℝ≥0) :
    stepThit β W A r ≤ ENNReal.ofReal t ↔
      ∃ j : ℕ, 1 ≤ j ∧
        ((t : ℝ) ∈ stepVj β W j ∧ max (A r + j * β) r ≤ t ∧ (t : ℝ) < r + j * β ∨
        ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) < t ∧ (q : ℝ) ∈ stepVj β W j ∧
          max (A r + j * β) r ≤ q ∧ (q : ℝ) < r + j * β) := by
  rw [stepThit_le_iff hβ hV hr]
  constructor
  · rintro ⟨j, hj, u, huV, hl, hu, hut⟩
    refine ⟨j, hj, ?_⟩
    rcases hut.lt_or_eq with hlt | heq
    · right
      have hu0 : 0 ≤ u := hr.trans ((le_max_right _ _).trans hl)
      have hUloc : IsLocIco (stepVj β W j ∩ Ico (max (A r + j * β) r) (r + j * β)) :=
        (hV j).inter (isLocIco_Ico _ _)
      obtain ⟨ε, hε, hsub⟩ := hUloc.exists_Ico hu0 ⟨huV, hl, hu⟩
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show u < min (u + ε) t from
        lt_min (by linarith) hlt)
      have hq := hsub ⟨hq1.le, lt_of_lt_of_le hq2 (min_le_left _ _)⟩
      exact ⟨q, by exact_mod_cast hu0.trans hq1.le, lt_of_lt_of_le hq2 (min_le_right _ _),
        hq.1, hq.2.1, hq.2.2⟩
    · left
      subst heq
      exact ⟨huV, hl, hu⟩
  · rintro ⟨j, hj, h | ⟨q, hq0, hqt, hqV, hql, hqu⟩⟩
    · exact ⟨j, hj, t, h.1, h.2.1, h.2.2, le_rfl⟩
    · exact ⟨j, hj, q, hqV, hql, hqu, hqt.le⟩

end ElboimSly.Paper
