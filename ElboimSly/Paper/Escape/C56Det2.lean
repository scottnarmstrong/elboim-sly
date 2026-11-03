/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Det
public import Mathlib

/-!
# ES22 Claim 5.6, phase `i`: `thit(T) ≥ b_i` and `ℬ_i`

ES22 Claim 5.6, "On `G_{i-1} ∩ E^a ∩ E^b ∩ E^d`, `thit(T) ≥ b_i`" and "`ℬ_i` holds".
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- **`thit(T) ≥ b_i`.**  The coupled path `W̃` does not come back to the history `W|[0, T]`
before time `b_i`. -/
theorem phase_thit_ge {j : ℕ} {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {β t : ℝ}
    (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    {n : ℕ} (hn : (4 : ℝ) ^ j ≤ 4 ^ n) (W : ℝ → Fin (k + 2) → ℤ) {i : ℕ} (hi1 : 1 ≤ i)
    (him : i ≤ 2 * escPhaseM β t) (hG : EscG β j u v z t W (i - 1))
    (Wt : ℝ≥0 → Fin (k + 2) → ℤ) {thit : ℝ≥0∞}
    (hthit : thit = ⨅ s ∈ {s : ℝ | escZeta β W t (escPhaseM β t) (i - 1) < s ∧ ∃ s' : ℝ,
        (∃ kk : ℤ, s' = s + kk * β) ∧ 0 < s' ∧ s' < escZeta β W t (escPhaseM β t) (i - 1) ∧
        ‖W (escZeta β W t (escPhaseM β t) (i - 1)) +
          Wt (s - escZeta β W t (escPhaseM β t) (i - 1)).toNNReal - W s'‖ ≤ 1},
      ENNReal.ofReal s)
    (hEa1 : ∀ r : ℝ, 0 ≤ r → r ≤ es56B t (escPhaseM β t) i -
        escZeta β W t (escPhaseM β t) (i - 1) →
      ‖escCast (W (escZeta β W t (escPhaseM β t) (i - 1)) + Wt r.toNNReal) -
        escCurve j u v z t (escZeta β W t (escPhaseM β t) (i - 1) + r)‖ ≤
        escR t (escPhaseM β t) i)
    (hEb : ENNReal.ofReal ((4 : ℝ) ^ n) ≤
      hitTime β W (escZetaPrev β W t (escPhaseM β t) (i - 1))
        (escZeta β W t (escPhaseM β t) (i - 1))
        (fun r => W (escZeta β W t (escPhaseM β t) (i - 1)) + Wt r.toNNReal)) :
    ENNReal.ofReal (es56B t (escPhaseM β t) i) ≤ thit := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  set m := escPhaseM β t with hm
  set T := escZeta β W t m (i - 1) with hT
  have hTmem := escZeta_mem β W ht0.le m (i - 1)
  have hT0 : 0 ≤ T := (escPhaseA_nonneg ht0.le m (i - 1)).trans hTmem.1
  rw [hthit]
  refine le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨hTs, s', ⟨kk, hk⟩, hs'0, hs'T, hle⟩ := hs
  by_contra hlt
  push Not at hlt
  have hr0 : 0 < s - T := sub_pos.2 hTs
  have hbt : es56B t m i ≤ t := es56B_le_t ht0.le m i
  by_cases hsa : escZetaPrev β W t m (i - 1) < s'
  · have hmem : s - T ∈ {r : ℝ | 0 < r ∧ ∃ s'' : ℝ, (∃ k : ℤ, s'' = T + r + k * β) ∧
        escZetaPrev β W t m (i - 1) < s'' ∧ s'' < T ∧
        ‖(fun r => W T + Wt r.toNNReal) r - W s''‖ ≤ 1} :=
      ⟨hr0, s', ⟨kk, by rw [hk]; ring⟩, hsa, hs'T, hle⟩
    have h1 := hEb.trans (iInf₂_le (s - T) hmem)
    have h2 : (4 : ℝ) ^ n ≤ s - T := (ENNReal.ofReal_le_ofReal_iff hr0.le).1 h1
    linarith
  · push Not at hsa
    have hi2 : 2 ≤ i := by
      by_contra hc
      have hi' : i = 1 := by omega
      subst hi'
      simp [escZetaPrev] at hsa
      linarith
    have hprev : escZetaPrev β W t m (i - 1) = escZeta β W t m (i - 2) := by
      unfold escZetaPrev
      rw [ite_eq_right (by omega)]
      congr 1
    rw [hprev] at hsa
    have hkk : kk < 0 := by
      by_contra hc
      push Not at hc
      have : (0 : ℝ) ≤ kk := by exact_mod_cast hc
      nlinarith
    have hkR : (kk : ℝ) ≤ -1 := by exact_mod_cast (by omega : kk ≤ -1)
    have hss : β ≤ s - s' := by nlinarith
    have hsb : s ≤ es56B t m i := hlt.le
    have hY := hEa1 (s - T) hr0.le (by linarith)
    rw [show T + (s - T) = s by ring] at hY
    have hsep := es5_sep hgeom hβ hβj ht1 ht2 W hi2 him hG
      (fun x => W T + Wt (x - T).toNNReal) (s := s) (s' := s') hTs.le hsb hs'0.le hsa hss
      (by simpa using hY)
    rw [c56_norm_escCast_sub] at hsep
    linarith

end ElboimSly.Paper.Escape

end
