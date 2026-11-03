/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenThitLe
public import ElboimSly.Foundations.Cyclic.CycRegenShiftSeq
public import ElboimSly.Foundations.Cyclic.CycHitAgree
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegen
public import Mathlib

/-!
# ES22 Lemma 2.1 (c): agreement, deterministic part

ES22 Lemma 2.1 (c), proof ("Case `L > 0`"). Let `ν : ℕ → Measure S_β` be the
good environments of the pieces of the regenerated walk `W = regenWalk ν`, `t` a time with
`k = regenCount ν t`, `α = regenStart ν t`, `L = t - α > 0` and `x = W(t)`. Let `ν'` be a good
environment which agrees with `ν k` off the region `ℛ_{(0,L]}(w)` of the current piece `w`. Let
`W' = regenWalk (seqCons ((φ_{(x,L)})_* ν') ν k)`, the regenerated walk with first piece the
recentred `ν'` and later pieces `ν (k+1), …`. Then `W(t + s) - W(t) = W'(s)` for `s` with
`t + s ≤ t_hit(t)` (`regen_agree_pos`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The environments of the restarted regenerated walk: first `μ0`, then `ν (k+1), ν (k+2), …`. -/
def seqCons (μ0 : Measure (RingSpace d β)) (ν : ℕ → Measure (RingSpace d β)) (k : ℕ) :
    ℕ → Measure (RingSpace d β)
  | 0 => μ0
  | j + 1 => ν (k + 1 + j)

theorem walkMap_zero (ν : Measure (RingSpace d β)) : walkMap ν 0 = 0 := by
  classical
  unfold walkMap
  exact cycWalk_zero (by split_ifs with h; exacts [h, good_zero]) _ _

variable {ν : ℕ → Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem good_seqCons (hg : ∀ j, Good (ν j)) {μ0 : Measure (RingSpace d β)} (h0 : Good μ0)
    (k : ℕ) : ∀ j, Good (seqCons μ0 ν k j) := fun j => by
  cases j with
  | zero => exact h0
  | succ j => exact hg _

/-- The regenerated walk of `seqCons` agrees with its first piece up to the first closing time. -/
theorem regenWalk_seqCons_of_le {μ0 : Measure (RingSpace d β)} (hg : ∀ j, Good (ν j))
    (h0 : Good μ0) (k : ℕ) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) ≤ pathTreg β.toNNReal (walkMap μ0)) :
    ElboimSly.regenWalk (seqCons μ0 ν k) (s : ℝ) = ElboimSly.cycWalk μ0 0 0 (s : ℝ) := by
  rw [regenWalk_eq_contGlue (good_seqCons hg h0 k) s]
  have : contPieces (walkMap (seqCons μ0 ν k 0)) (fun j => walkMap (seqCons μ0 ν k (j + 1))) =
      contPieces (walkMap μ0) (fun j => walkMap (ν (k + 1 + j))) := rfl
  show contGlue _ (walkMap μ0) (fun j => walkMap (ν (k + 1 + j))) s = _
  rw [contGlue_agree (Real.toNNReal_pos.2 Fact.out) _ _ (fun j => walkMap_zero _) hs]
  exact walkMap_eq_cycWalk h0 s

/-- **ES22 Lemma 2.1 (c)**, deterministic form for `L = t - α(t) > 0`. -/
theorem regen_agree_pos (hg : ∀ j, Good (ν j)) {t L : ℝ≥0}
    (hLd : (L : ℝ) = (t : ℝ) - ElboimSly.regenStart ν t) (hL : 0 < L)
    {ν' : Measure (RingSpace d β)} (hν' : Good ν')
    (hag : ν'.restrict (cycRegion β (fun r => ElboimSly.cycWalk
        (ν (ElboimSly.regenCount ν t)) 0 0 r) 0 (L : ℝ))ᶜ =
      (ν (ElboimSly.regenCount ν t)).restrict (cycRegion β (fun r => ElboimSly.cycWalk
        (ν (ElboimSly.regenCount ν t)) 0 0 r) 0 (L : ℝ))ᶜ)
    {s : ℝ≥0} (hs : ENNReal.ofReal ((t : ℝ) + s) ≤ ElboimSly.cycThit ν t) :
    (s : ℝ≥0∞) < pathTreg β.toNNReal (walkMap (ν'.map (hitPhi (ElboimSly.regenWalk ν t) (L : ℝ)))) ∧
    ElboimSly.regenWalk (seqCons (ν'.map (hitPhi (ElboimSly.regenWalk ν t) (L : ℝ))) ν
        (ElboimSly.regenCount ν t)) (s : ℝ) =
      ElboimSly.regenWalk ν ((t : ℝ) + s) - ElboimSly.regenWalk ν t := by
  have hβ : 0 < β := Fact.out
  have ht : (0 : ℝ) ≤ t := t.2
  set k := ElboimSly.regenCount ν t with hk
  have hkfin : ElboimSly.regenSigma ν k < ⊤ := regenSigma_count_lt_top ν ht
  have ha' : ElboimSly.regenStart ν t = (ElboimSly.regenSigma ν k).toReal := rfl
  have hLpos : 0 < (t : ℝ) - ElboimSly.regenStart ν t := by rw [← hLd]; exact_mod_cast hL
  have hLw : ElboimSly.regenWalk ν t = ElboimSly.cycWalk (ν k) 0 0 (L : ℝ) := by
    unfold ElboimSly.regenWalk; rw [← hk, hLd]
  -- the agreement for a general time `r ≤ s`
  have hagree : ∀ r : ℝ≥0, r ≤ s →
      ElboimSly.cycWalk (ν'.map (hitPhi (ElboimSly.regenWalk ν t) (L : ℝ))) 0 0 (r : ℝ) =
        ElboimSly.cycWalk (ν k) 0 0 ((L : ℝ) + r) - ElboimSly.regenWalk ν t := by
    intro r hr
    have hr' : ENNReal.ofReal ((t : ℝ) + r) ≤ ElboimSly.cycThit ν t :=
      (ENNReal.ofReal_le_ofReal (by have : (r : ℝ) ≤ (s : ℝ) := hr; linarith)).trans hs
    have h1 := le_cycHatThit_of_le_cycThit hg ht hLpos (s := (r : ℝ)) r.2 hr'
    have h2 : (((L + r : ℝ≥0)) : ℝ≥0∞) ≤ cycHatThit β
        (fun r => ElboimSly.cycWalk (ν k) 0 0 r) (L : ℝ) := by
      rw [← hLd] at h1
      rwa [← ENNReal.ofReal_coe_nnreal, NNReal.coe_add]
    have := hit_agree (hg k) hν' L hag r h2
    rwa [hLw]
  have hLs := ofReal_add_le_treg hg ht hLpos (s := (s : ℝ)) s.2 hs
  rw [← hLd] at hLs
  have hμ0 : Good (ν'.map (hitPhi (ElboimSly.regenWalk ν t) (L : ℝ))) := good_map_hitPhi hν' _ _
  -- the first piece of `W'` does not close before `s`
  have hnc : (s : ℝ≥0∞) < pathTreg β.toNNReal (walkMap (ν'.map (hitPhi
      (ElboimSly.regenWalk ν t) (L : ℝ)))) := by
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨j, hj1, hj, hz⟩ := pathTreg_exists (b := β.toNNReal) (hcon.trans_lt ENNReal.coe_lt_top)
    have hjs : ((j : ℝ≥0) * β.toNNReal) ≤ s := by
      rw [hj] at hcon; exact_mod_cast hcon
    set r : ℝ≥0 := (j : ℝ≥0) * β.toNNReal with hr
    have hrR : (r : ℝ) = (j : ℝ) * β := by
      rw [hr]; push_cast; rw [Real.coe_toNNReal β hβ.le]
    have hr0 : 0 < (r : ℝ) := by
      rw [hrR]; have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      positivity
    have h1 := hagree r hjs
    rw [walkMap_eq_cycWalk hμ0] at hz
    rw [hz] at h1
    have h2 : ElboimSly.cycWalk (ν k) 0 0 ((L : ℝ) + r) = ElboimSly.cycWalk (ν k) 0 0 (L : ℝ) := by
      rw [← hLw]; exact (sub_eq_zero.1 h1.symm)
    have h3 := cycTreg_le_of_eq (hg k) (s := (L : ℝ) + r) (s' := (L : ℝ)) (by linarith)
      (k := (j : ℤ)) (by rw [hrR]; push_cast; ring) h2
    have hr' : ENNReal.ofReal ((t : ℝ) + r) ≤ ElboimSly.cycThit ν t :=
      (ENNReal.ofReal_le_ofReal (by have : (r : ℝ) ≤ (s : ℝ) := hjs; linarith)).trans hs
    have h4 := ofReal_add_le_treg hg ht hLpos (s := (r : ℝ)) r.2 hr'
    rw [← hLd] at h4
    have h5 : ENNReal.ofReal (r : ℝ) < ENNReal.ofReal ((L : ℝ) + r) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by
        have : (0 : ℝ) < L := by exact_mod_cast hL
        linarith)
    rw [show (L : ℝ) + r - L = r by ring] at h3
    exact absurd (h3.trans_lt (h5.trans_le h4)) (lt_irrefl _)
  refine ⟨hnc, ?_⟩
  rw [regenWalk_seqCons_of_le hg hμ0 k hnc.le, hagree s le_rfl]
  have h6 := regenWalk_piece hg k hkfin (u := (L : ℝ) + s) (by positivity) hLs
  rw [← ha'] at h6
  have h7 : ElboimSly.regenStart ν t + ((L : ℝ) + s) = (t : ℝ) + s := by rw [hLd]; ring
  rw [h7] at h6
  rw [h6]

/-- Regenerated walks whose pieces have the same paths coincide. -/
theorem regenWalk_congr {ν₁ ν₂ : ℕ → Measure (RingSpace d β)} (h1 : ∀ j, Good (ν₁ j))
    (h2 : ∀ j, Good (ν₂ j)) (h : ∀ (j : ℕ) (u : ℝ≥0), ElboimSly.cycWalk (ν₁ j) 0 0 (u : ℝ) =
      ElboimSly.cycWalk (ν₂ j) 0 0 (u : ℝ)) (s : ℝ≥0) :
    ElboimSly.regenWalk ν₁ (s : ℝ) = ElboimSly.regenWalk ν₂ (s : ℝ) := by
  rw [regenWalk_eq_contGlue h1, regenWalk_eq_contGlue h2]
  have hw : ∀ j, walkMap (ν₁ j) = walkMap (ν₂ j) := fun j => by
    funext u; rw [walkMap_eq_cycWalk (h1 j), walkMap_eq_cycWalk (h2 j), h]
  rw [hw 0]
  simp only [hw]

/-- **ES22 Lemma 2.1 (c)**, deterministic form for `L = t - α(t) = 0`: the restarted
regenerated walk is the shifted one. -/
theorem regen_agree_zero (hg : ∀ j, Good (ν j)) {t : ℝ≥0}
    (hL : (t : ℝ) = ElboimSly.regenStart ν t) {μ0 : Measure (RingSpace d β)} (h0 : Good μ0)
    (hpath : ∀ u : ℝ≥0, ElboimSly.cycWalk μ0 0 0 (u : ℝ) =
      ElboimSly.cycWalk (ν (ElboimSly.regenCount ν t)) 0 0 (u : ℝ)) (s : ℝ≥0) :
    ElboimSly.regenWalk (seqCons μ0 ν (ElboimSly.regenCount ν t)) (s : ℝ) =
      ElboimSly.regenWalk ν ((t : ℝ) + s) - ElboimSly.regenWalk ν t := by
  have ht : (0 : ℝ) ≤ t := t.2
  set k := ElboimSly.regenCount ν t with hk
  have hkfin : ElboimSly.regenSigma ν k < ⊤ := regenSigma_count_lt_top ν ht
  have hz : ElboimSly.regenWalk ν t = 0 := by
    unfold ElboimSly.regenWalk
    rw [← hk, ← hL, sub_self]
    exact cycWalk_zero (hg k) 0 0
  have hgS := good_seqCons hg h0 k
  have hgk : ∀ j, Good (ν (k + j)) := fun j => hg _
  have hc : ElboimSly.regenWalk (seqCons μ0 ν k) (s : ℝ) =
      ElboimSly.regenWalk (fun j => ν (k + j)) (s : ℝ) := by
    refine regenWalk_congr hgS hgk ?_ s
    intro j u
    cases j with
    | zero => exact hpath u
    | succ j =>
      show ElboimSly.cycWalk (ν (k + 1 + j)) 0 0 (u : ℝ) = ElboimSly.cycWalk (ν (k + (j + 1))) 0 0 (u : ℝ)
      rw [show k + (j + 1) = k + 1 + j by omega]
  have hσ : (ElboimSly.regenSigma ν k).toReal = (t : ℝ) := hL.symm
  rw [hc, regenWalk_shift ν k hkfin (s := (s : ℝ)) s.2, hσ, hz, sub_zero]

end ElboimSly.Cyclic

end
