/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsRelaxedPath
public import ElboimSly.Paper.Induction.RelaxedMeasWrt
public import ElboimSly.Foundations.Cyclic.CycJoint
public import ElboimSly.Foundations.Cyclic.CycEvents
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Foundations.Cyclic.FwdBridge
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import Mathlib

/-!
# Measurability of relaxed times: the regenerated walk

Measurability of relaxed times (Steps 2 and 5).

Let `ν : Ω → ℕ → Measure (RingSpace d β)` be a family of environment sequences, each `ν · k`
measurable and each `ν ω k` good (the environments are almost surely good; this is the standing
typing assumption under which `cycWalk` is the trajectory and not a junk value).

* `regenWalk_rlc`: the regenerated walk is right-locally constant at every `s ≥ 0`.
* `measurableSet_relaxedTimes`: `{(ω, t) | 0 ≤ t ∧ IsRelaxedTime (ν ω) t}` is measurable.
* `measurable_volume_relaxedTimes`: `ω ↦ |𝒯(ω) ∩ I|` is measurable for measurable `I`.
* `measurableSet_isRelaxedPath`: `{ω | IsRelaxedPath (ν ω) t}` is measurable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-! ### Regeneration times -/

theorem le_cycTreg (ν : Measure (RingSpace d β)) : ENNReal.ofReal β ≤ cycTreg ν := by
  refine le_iInf fun k => ENNReal.ofReal_le_ofReal ?_
  have hk : (1 : ℝ) ≤ k.1 := by exact_mod_cast k.2.1
  have hβ : 0 < β := Fact.out
  nlinarith

omit [Fact (0 < β)] in
theorem ind_regenSigma_succ (ν : ℕ → Measure (RingSpace d β)) (i : ℕ) :
    regenSigma ν (i + 1) = regenSigma ν i + cycTreg (ν i) := by
  simp [regenSigma, Finset.sum_range_succ]

omit [Fact (0 < β)] in
theorem regenSigma_mono' (ν : ℕ → Measure (RingSpace d β)) : Monotone (regenSigma ν) :=
  fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem le_regenSigma (ν : ℕ → Measure (RingSpace d β)) (i : ℕ) :
    ENNReal.ofReal (β * i) ≤ regenSigma ν i := by
  induction i with
  | zero => simp [regenSigma]
  | succ i ih =>
    rw [ind_regenSigma_succ]
    have : ENNReal.ofReal (β * ((i + 1 : ℕ) : ℝ)) =
        ENNReal.ofReal (β * i) + ENNReal.ofReal β := by
      rw [← ENNReal.ofReal_add (mul_nonneg (Fact.out : 0 < β).le (Nat.cast_nonneg _)) (Fact.out : 0 < β).le]
      congr 1; push_cast; ring
    rw [this]
    exact add_le_add ih (le_cycTreg _)

theorem regenCount_spec (ν : ℕ → Measure (RingSpace d β)) {t : ℝ} (ht : 0 ≤ t) :
    regenSigma ν (regenCount ν t) ≤ ENNReal.ofReal t ∧
      ENNReal.ofReal t < regenSigma ν (regenCount ν t + 1) := by
  have hβ : 0 < β := Fact.out
  set S : Set ℕ := {i | regenSigma ν i ≤ ENNReal.ofReal t} with hS
  have hne : S.Nonempty := ⟨0, by simp [hS, regenSigma]⟩
  have hbdd : BddAbove S := by
    refine ⟨⌈t / β⌉₊, fun j hj => ?_⟩
    by_contra hlt
    push Not at hlt
    have h1 : ENNReal.ofReal (β * j) ≤ ENNReal.ofReal t := (le_regenSigma ν j).trans hj
    rw [ENNReal.ofReal_le_ofReal_iff ht] at h1
    have h2 : t / β < j := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hlt)
    rw [div_lt_iff₀ hβ] at h2
    linarith
  have hmem : regenCount ν t ∈ S := Nat.sSup_mem hne hbdd
  refine ⟨hmem, ?_⟩
  by_contra hc
  push Not at hc
  have : regenCount ν t + 1 ≤ regenCount ν t := le_csSup hbdd hc
  omega

theorem regenCount_eq_iff (ν : ℕ → Measure (RingSpace d β)) {t : ℝ} (ht : 0 ≤ t) (i : ℕ) :
    regenCount ν t = i ↔
      regenSigma ν i ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < regenSigma ν (i + 1) := by
  constructor
  · rintro rfl
    exact regenCount_spec ν ht
  · rintro ⟨h1, h2⟩
    have : {j : ℕ | regenSigma ν j ≤ ENNReal.ofReal t} = Set.Iic i := by
      ext j
      simp only [mem_ofPred_eq, mem_Iic]
      constructor
      · intro hj
        by_contra hji
        push Not at hji
        exact absurd (lt_of_lt_of_le h2 (regenSigma_mono' ν hji)) (not_lt.2 hj)
      · intro hj
        exact (regenSigma_mono' ν hj).trans h1
    unfold regenCount
    rw [this, csSup_Iic]

/-! ### Right-local constancy -/

theorem cycWalk_rlc {ν : Measure (RingSpace d β)} (hν : Good ν) (u : Fin d → ℤ) {r : ℝ}
    (hr : 0 ≤ r) : ∃ ε > 0, ∀ s ∈ Ico r (r + ε), cycWalk ν u 0 s = cycWalk ν u 0 r := by
  obtain ⟨k, hk1, hk2⟩ := Cyclic.exists_block hν u 0 r
  refine ⟨(Cyclic.fseq ν u 0 (k + 1)).1 - max r 0, by linarith, fun s hs => ?_⟩
  have hs0 : 0 ≤ s := hr.trans hs.1
  have hmr : max r 0 = r := max_eq_left hr
  rw [hmr] at hk1 hk2
  rw [Cyclic.cycWalk_of_nonneg hν u 0 hs0, Cyclic.cycWalk_of_nonneg hν u 0 hr,
    Cyclic.fwdTraj_eq_fseq hν u 0 (0 + s) (k := k) (by rw [zero_add, max_eq_left hs0]; linarith [hs.1])
      (by rw [zero_add, max_eq_left hs0]; linarith [hs.2]),
    Cyclic.fwdTraj_eq_fseq hν u 0 (0 + r) (k := k) (by rw [zero_add, max_eq_left hr]; exact hk1)
      (by rw [zero_add, max_eq_left hr]; exact hk2)]

/-- The regenerated walk is right-locally constant at every `s ≥ 0`. -/
theorem regenWalk_rlc {ν : ℕ → Measure (RingSpace d β)} (hg : ∀ k, Good (ν k)) {s : ℝ}
    (hs : 0 ≤ s) : ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), regenWalk ν s' = regenWalk ν s := by
  obtain ⟨h1, h2⟩ := regenCount_spec ν hs
  set i := regenCount ν s with hi
  have hσs : (regenSigma ν i).toReal ≤ s := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal hs] at this
  obtain ⟨ε₂, hε₂, hc⟩ := cycWalk_rlc (hg i) 0 (r := s - (regenSigma ν i).toReal)
    (by linarith)
  -- the distance to the next regeneration time
  have hε₁ : ∃ ε₁ > 0, ENNReal.ofReal (s + ε₁) ≤ regenSigma ν (i + 1) := by
    by_cases htop : regenSigma ν (i + 1) = ⊤
    · exact ⟨1, one_pos, by simp [htop]⟩
    · refine ⟨(regenSigma ν (i + 1)).toReal - s, ?_, ?_⟩
      · have := ENNReal.toReal_strict_mono htop h2
        rw [ENNReal.toReal_ofReal hs] at this
        linarith
      · rw [add_sub_cancel]; exact (ENNReal.ofReal_toReal htop).le
  obtain ⟨ε₁, hε₁, hle⟩ := hε₁
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun s' hs' => ?_⟩
  have hs'0 : 0 ≤ s' := hs.trans hs'.1
  have hcnt : regenCount ν s' = i := by
    rw [regenCount_eq_iff ν hs'0]
    refine ⟨?_, ?_⟩
    · exact h1.trans (ENNReal.ofReal_le_ofReal hs'.1)
    · have hlt : s' < s + ε₁ := by linarith [hs'.2, min_le_left ε₁ ε₂]
      exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hlt) hle
  simp only [regenWalk, regenStart, hcnt, ← hi]
  have := hc (s' - (regenSigma ν i).toReal) ⟨by linarith [hs'.1], by linarith [hs'.2, min_le_right ε₁ ε₂]⟩
  simpa using this

end ElboimSly.Paper

end
