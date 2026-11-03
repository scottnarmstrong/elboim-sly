/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenAgree
public import ElboimSly.Foundations.Cyclic.CycRegenRc
public import Mathlib

/-!
# ES22 Lemma 2.1 (e): the hitting time through `W'`

ES22 Lemma 2.1 (e), deterministic form. With `x = W(t)` and `W'` the
restarted regenerated walk (`seqCons`), `t_hit(t)` equals
`inf {s > t : ∃ s' ∈ s + βℤ, α(t) < s' < t, ‖x + W'(s - t) - W(s')‖ ≤ 1}`
(`regen_thit_eq`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : ℕ → Measure (RingSpace d β)}

/-- Two infima over sets whose memberships agree up to and slightly after the infimum. -/
theorem iInf_set_eq_of_agree (P1 P2 : ℝ → Prop) (h : ℝ≥0∞)
    (hh : h = ⨅ s ∈ {s | P1 s}, ENNReal.ofReal s) (hnn : ∀ s, P1 s → 0 ≤ s)
    (h1 : ∀ s, ENNReal.ofReal s ≤ h → (P1 s ↔ P2 s))
    (h2 : h = ⊤ ∨ ∃ ε : ℝ, 0 < ε ∧ ∀ s, h.toReal ≤ s → s < h.toReal + ε → (P1 s ↔ P2 s)) :
    h = ⨅ s ∈ {s | P2 s}, ENNReal.ofReal s := by
  refine le_antisymm (le_iInf₂ fun s hs2 => ?_) ?_
  · by_contra hlt
    rw [not_le] at hlt
    have : P1 s := (h1 s hlt.le).2 hs2
    exact absurd (hh ▸ iInf₂_le s this) (not_le.2 hlt)
  · rcases h2 with htop | ⟨ε, hε, hagree⟩
    · rw [htop]; exact le_top
    by_cases htop : h = ⊤
    · rw [htop]; exact le_top
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc1, hc2⟩ := exists_between hcon
    have hhR : ENNReal.ofReal h.toReal = h := ENNReal.ofReal_toReal htop
    have hhR0 : 0 ≤ h.toReal := ENNReal.toReal_nonneg
    have hlt2 : h < ENNReal.ofReal (h.toReal + ε) := by
      calc h = ENNReal.ofReal h.toReal := hhR.symm
        _ < ENNReal.ofReal (h.toReal + ε) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have hlt3 : ⨅ s ∈ {s | P1 s}, ENNReal.ofReal s < min c (ENNReal.ofReal (h.toReal + ε)) := by
      rw [← hh]; exact lt_min hc1 hlt2
    rw [iInf_lt_iff] at hlt3
    obtain ⟨s, hs⟩ := hlt3
    rw [iInf_lt_iff] at hs
    obtain ⟨hP, hlts⟩ := hs
    have hhs : h ≤ ENNReal.ofReal s := hh ▸ iInf₂_le s hP
    have hRs : h.toReal ≤ s := ENNReal.toReal_le_of_le_ofReal (hnn s hP) hhs
    have hsε : s < h.toReal + ε := by
      have := (lt_min_iff.1 hlts).2
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 this
    have hP2 : P2 s := (hagree s hRs hsε).1 hP
    have : ⨅ s ∈ {s | P2 s}, ENNReal.ofReal s ≤ ENNReal.ofReal s := iInf₂_le s hP2
    exact absurd (this.trans_lt (lt_of_lt_of_le hlts (min_le_left _ _))) (not_lt.2 hc2.le)

/-- **ES22 Lemma 2.1 (e)**, deterministic form. -/
theorem regen_thit_eq (hg : ∀ j, Good (ν j)) {t L : ℝ≥0}
    (hLd : (L : ℝ) = (t : ℝ) - ElboimSly.regenStart ν t)
    {ν' : Measure (RingSpace d β)} (hν' : Good ν')
    (hag : ν'.restrict (cycRegion β (fun r => ElboimSly.cycWalk
        (ν (ElboimSly.regenCount ν t)) 0 0 r) 0 (L : ℝ))ᶜ =
      (ν (ElboimSly.regenCount ν t)).restrict (cycRegion β (fun r => ElboimSly.cycWalk
        (ν (ElboimSly.regenCount ν t)) 0 0 r) 0 (L : ℝ))ᶜ) :
    ElboimSly.cycThit ν t =
      ⨅ s ∈ {s : ℝ | (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
        ElboimSly.regenStart ν t < s' ∧ s' < t ∧
        ‖ElboimSly.regenWalk ν t +
          ElboimSly.regenWalk (seqCons (ν'.map (hitPhi (ElboimSly.regenWalk ν t) (L : ℝ))) ν
            (ElboimSly.regenCount ν t)) (s - t) - ElboimSly.regenWalk ν s'‖ ≤ 1},
        ENNReal.ofReal s := by
  set Wp : ℝ → Fin d → ℤ := fun r => ElboimSly.regenWalk
    (seqCons (ν'.map (hitPhi (ElboimSly.regenWalk ν t) (L : ℝ))) ν
      (ElboimSly.regenCount ν t)) r with hWp
  have hgM : ∀ j, Good (seqCons (ν'.map (hitPhi (ElboimSly.regenWalk ν t) (L : ℝ))) ν
      (ElboimSly.regenCount ν t) j) :=
    good_seqCons hg (good_map_hitPhi hν' _ _) _
  rcases (show (0 : ℝ≥0) ≤ L from zero_le).lt_or_eq with hL | hL
  · -- `L > 0`
    have ht : (0 : ℝ) ≤ t := t.2
    -- agreement on the part below the hitting time
    have hW : ∀ s : ℝ, (t : ℝ) ≤ s → ENNReal.ofReal s ≤ ElboimSly.cycThit ν t →
        ElboimSly.regenWalk ν t + Wp (s - t) = ElboimSly.regenWalk ν s := by
      intro s hts hs
      have hr : ((s - t).toNNReal : ℝ) = s - t := Real.coe_toNNReal _ (by linarith)
      have hs' : ENNReal.ofReal ((t : ℝ) + ((s - t).toNNReal : ℝ)) ≤ ElboimSly.cycThit ν t := by
        rw [hr]; simpa using hs
      have := (regen_agree_pos hg hLd hL hν' hag hs').2
      rw [hr] at this
      simp only [hWp]
      rw [this, show (t : ℝ) + (s - t) = s by ring]
      abel
    set x := ElboimSly.regenWalk ν t with hx
    let P1 : ℝ → Prop := fun s => (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
      ElboimSly.regenStart ν t < s' ∧ s' < t ∧
        ‖ElboimSly.regenWalk ν s - ElboimSly.regenWalk ν s'‖ ≤ 1
    let P2 : ℝ → Prop := fun s => (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
      ElboimSly.regenStart ν t < s' ∧ s' < t ∧ ‖x + Wp (s - t) - ElboimSly.regenWalk ν s'‖ ≤ 1
    -- memberships agree whenever `x + W'(s - t) = W(s)`
    have hiff : ∀ s : ℝ, x + Wp (s - t) = ElboimSly.regenWalk ν s → (P1 s ↔ P2 s) := by
      intro s hsame
      simp only [P1, P2, hsame]
    refine iInf_set_eq_of_agree P1 P2 (ElboimSly.cycThit ν t) rfl
      (fun s hs => (t.2).trans hs.1.le) (fun s hs => ?_) ?_
    · by_cases hts : (t : ℝ) < s
      · exact hiff s (hW s hts.le hs)
      · constructor <;> rintro ⟨h1, -⟩ <;> exact absurd h1 hts
    · by_cases htop : ElboimSly.cycThit ν t = ⊤
      · exact Or.inl htop
      right
      set hR := (ElboimSly.cycThit ν t).toReal with hhR
      have hRe : ENNReal.ofReal hR = ElboimSly.cycThit ν t := ENNReal.ofReal_toReal htop
      have htle : ENNReal.ofReal (t : ℝ) ≤ ElboimSly.cycThit ν t := by
        unfold ElboimSly.cycThit
        exact le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal hs.1.le
      have hRt : (t : ℝ) ≤ hR := (ENNReal.ofReal_le_iff_le_toReal htop).1 htle
      have hR0 : 0 ≤ hR := ENNReal.toReal_nonneg
      have hWR := hW hR hRt hRe.le
      obtain ⟨ε1, hε1, hc1⟩ := regenWalk_const_near hg hR0
      obtain ⟨ε2, hε2, hc2⟩ := regenWalk_const_near hgM (sub_nonneg.2 hRt)
      refine ⟨min ε1 ε2, lt_min hε1 hε2, fun s hs1 hs2 => ?_⟩
      have e1 : ElboimSly.regenWalk ν s = ElboimSly.regenWalk ν hR :=
        hc1 s hs1 (by have := min_le_left ε1 ε2; linarith)
      have e2 : Wp (s - t) = Wp (hR - t) :=
        hc2 (s - t) (by linarith) (by have := min_le_right ε1 ε2; linarith)
      exact hiff s (by rw [e1, e2]; exact hWR)
  · -- `L = 0`
    have hα : ElboimSly.regenStart ν t = t := by
      have : (L : ℝ) = 0 := by rw [← hL]; simp
      linarith
    rw [cycThit_eq_top hα]
    symm
    refine iInf₂_eq_top.2 fun s hs => ?_
    obtain ⟨-, s', -, h1, h2, -⟩ := hs
    rw [hα] at h1
    exact absurd (h1.trans h2) (lt_irrefl _)

end ElboimSly.Cyclic

end
