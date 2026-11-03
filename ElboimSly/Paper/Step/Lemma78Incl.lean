/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StopHit2
public import Mathlib

/-!
# The inclusion step of one excursion succeeds with probability at least frac12 for the second walk

One excursion succeeds with probability at least frac12, "Reduction", first item (the inclusion step of
ES22 Lemma 4.1, for a path `w` coupled with `w t + y` on `[t, thit(t)]`): if the walk
`w(t + ·) - w(t)` agrees with a right-continuous path `y` up to `thit(t)` and `t` is relaxed, then
`τ' ≥ n4` implies `thit(t) ≥ t + n4`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- **Inclusion step** (abstract form). -/
theorem step78_ofReal_add_le_stepThit {β : ℝ} (hd : 1 ≤ d) (hβ1 : 1 < β)
    {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ}
    (hrc : ∀ s : ℝ, ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), w s' = w s) {t : ℝ} (ht0 : 0 ≤ t)
    (hrel : IsRelaxedTimeWrt β w (α t) t) {y : ℝ≥0 → Fin d → ℤ}
    (hy : ∀ s, ∀ᶠ u in 𝓝[≥] s, y u = y s)
    (hcpl : ∀ s : ℝ, 0 ≤ s → ENNReal.ofReal (t + s) ≤ stepThit β w α t →
      w (t + s) = w t + y s.toNNReal) {n4 : ℝ}
    (hit : ENNReal.ofReal n4 ≤ hitTime β w (α t) t (fun r => w t + y r.toNNReal)) :
    ENNReal.ofReal (t + n4) ≤ stepThit β w α t := by
  have hβ0 : 0 < β := by linarith
  have hgt := stepThit_gt_of_relaxed hd hβ1 (α := α) hrc ht0 hrel
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨h, hh⟩ : ∃ h, stepThit β w α t = h := ⟨_, rfl⟩
  have hgt : ENNReal.ofReal t < h := by rw [← hh]; exact hgt
  have hlt : h < ENNReal.ofReal (t + n4) := by rw [← hh]; exact hlt
  have hhtop : h ≠ ⊤ := ne_top_of_lt (hlt.trans ENNReal.ofReal_lt_top)
  set hr := h.toReal with hhr
  have hhe : h = ENNReal.ofReal hr := (ENNReal.ofReal_toReal hhtop).symm
  rw [hhe] at hgt hlt
  have h1 : t < hr := ((ENNReal.ofReal_lt_ofReal_iff').1 hgt).1
  have h2 : hr < t + n4 := ((ENNReal.ofReal_lt_ofReal_iff').1 hlt).1
  obtain ⟨ε1, hε1, hc1⟩ := hrc hr
  obtain ⟨ε2, hε2, hc2⟩ := exists_Ico_const_stepExt hy (hr - t)
  set η := min (min ε1 ε2) ((t + n4 - hr) / 2) with hη
  have hη0 : 0 < η := lt_min (lt_min hε1 hε2) (by linarith)
  have hηε1 : η ≤ ε1 := (min_le_left _ _).trans (min_le_left _ _)
  have hηε2 : η ≤ ε2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηn : η ≤ (t + n4 - hr) / 2 := min_le_right _ _
  have hlt2 : h < ENNReal.ofReal (hr + η) := by
    rw [hhe]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  -- a witness `s` of the infimum below `hr + η`
  have hlt3 := hlt2
  rw [← hh] at hlt3
  unfold stepThit at hlt3
  rw [iInf_lt_iff] at hlt3
  obtain ⟨s, hlt3⟩ := hlt3
  rw [iInf_lt_iff] at hlt3
  obtain ⟨hs, hslt⟩ := hlt3
  obtain ⟨hts, s', ⟨k, hk⟩, hαs, hs't, hnorm⟩ := hs
  have hs0 : 0 ≤ s := le_trans ht0 hts.le
  have hhs : h ≤ ENNReal.ofReal s := by
    rw [← hh]; exact iInf₂_le s ⟨hts, s', ⟨k, hk⟩, hαs, hs't, hnorm⟩
  have hrs : hr ≤ s := by
    rw [hhe] at hhs; exact (ENNReal.ofReal_le_ofReal_iff hs0).1 hhs
  have hsη : s < hr + η := (ENNReal.ofReal_lt_ofReal_iff' |>.1 hslt).1
  -- the coupling at `hr`
  have hcpl' : w hr = w t + y (hr - t).toNNReal := by
    have := hcpl (hr - t) (by linarith) (by
      rw [show t + (hr - t) = hr by ring, ← hhe, ← hh])
    rwa [show t + (hr - t) = hr by ring] at this
  -- the walk at `s`
  have hws : w s = w t + y (s - t).toNNReal := by
    have e1 : w s = w hr := hc1 s ⟨hrs, by linarith⟩
    have e2 : y (s - t).toNNReal = y (hr - t).toNNReal :=
      hc2 (s - t) ⟨by linarith, by linarith⟩
    rw [e1, hcpl', e2]
  -- hence `τ' < n4`
  have hmem : s - t ∈ {r : ℝ | 0 < r ∧ ∃ s'' : ℝ, (∃ k : ℤ, s'' = t + r + k * β) ∧
      α t < s'' ∧ s'' < t ∧ ‖(fun r => w t + y r.toNNReal) r - w s''‖ ≤ 1} := by
    refine ⟨by linarith, s', ⟨k, by rw [hk]; ring⟩, hαs, hs't, ?_⟩
    simp only
    rw [← hws]; exact hnorm
  have h3 := hit.trans (iInf₂_le (s - t) hmem)
  have h4 : n4 ≤ s - t := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h3
  linarith

end ElboimSly.Paper.Step

end
