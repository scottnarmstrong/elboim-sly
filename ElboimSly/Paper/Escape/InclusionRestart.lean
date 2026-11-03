/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.InclusionArith
public import ElboimSly.Paper.Escape.EscapeTime
public import ElboimSly.Paper.Heavy.PiecesClosing
public import Mathlib

/-!
# The inclusion at ES22 §5: restart, closing, and the full lemma

t' and escK(β'); The inclusion at ES22 §5.

* `EscK`: the event `𝒦(β')` of t' and escK(β'), with `t' = cycFloor β (ξ + 4^j)` the largest cyclic
  integer `≤ ξ + 4^j`.
* `cycIntPhase_cycFloor`: the phase of `t'` is `⌊q(ξ + 4^j)⌋`.
* `es5_inclusion_restart`: the first two claims of the lemma, for the first piece `W = W^μ_{0,0}`
  and the restarted walk `W_i = W^μ_{p_i, β'}` (the walk of copy `0` at `p_i`).
* `es5_inclusion`: all three claims.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The phase of `t' = cycFloor β x` is `⌊q(x)⌋`. -/
theorem cycIntPhase_cycFloor {x : ℝ} :
    cycIntPhase β (cycFloor β x) = ((⌊cycIntPhase β x⌋ : ℤ) : ℝ) := by
  have hβ : 0 < β := Fact.out
  have h0 : 0 ≤ x - β * ⌊x / β⌋ := by
    have := Int.floor_le (x / β)
    have h2 : β * (x / β) = x := by field_simp
    nlinarith
  have h1 : x - β * ⌊x / β⌋ < β := by
    have := Int.lt_floor_add_one (x / β)
    have h2 : β * (x / β) = x := by field_simp
    nlinarith
  have hf0 : (0 : ℝ) ≤ ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 h0
  have hf1 : ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) < β := lt_of_le_of_lt (Int.floor_le _) h1
  have hfl : ⌊cycFloor β x / β⌋ = ⌊x / β⌋ := by
    unfold cycFloor
    rw [Int.floor_eq_iff]
    have e : (β * ⌊x / β⌋ + ⌊x - β * ⌊x / β⌋⌋) / β =
        ⌊x / β⌋ + ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) / β := by field_simp
    rw [e]
    constructor
    · have : 0 ≤ ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) / β := div_nonneg hf0 hβ.le
      linarith
    · have : ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) / β < 1 := (div_lt_one hβ).2 hf1
      linarith
  unfold cycIntPhase
  rw [hfl]
  unfold cycFloor
  ring

/-- t' and escK(β'): the event `𝒦(β')`, for a path `W`, first entrance time `ξ`, closing time
`treg`, half block `B⁻`: `ξ ≤ t_n`, `ξ < t_reg`, `W(ξ) ∈ B⁻` and the largest cyclic integer
`t' ≤ ξ + 4^j` has phase `β'`. -/
def EscK (β tn : ℝ) (j : ℕ) {k : ℕ} (Bm : Set (Fin (k + 2) → ℤ)) (W : ℝ → Fin (k + 2) → ℤ)
    (ξ treg : ℝ≥0∞) (β' : ℕ) : Prop :=
  ξ ≤ ENNReal.ofReal tn ∧ ξ < treg ∧ W ξ.toReal ∈ Bm ∧
    cycIntPhase β (cycFloor β (ξ.toReal + 4 ^ j)) = (β' : ℝ)

/-- On `𝒦(β')` the phase of `t'` is the integer `β'` and `β' < ⌈β⌉`. -/
theorem EscK.phase_lt {k : ℕ} {tn : ℝ} {j : ℕ} {Bm : Set (Fin (k + 2) → ℤ)}
    {W : ℝ → Fin (k + 2) → ℤ} {ξ treg : ℝ≥0∞} {β' : ℕ}
    (h : EscK β tn j Bm W ξ treg β') : β' < ⌈β⌉₊ := by
  have hβ : 0 < β := Fact.out
  have hx : 0 ≤ ξ.toReal + 4 ^ j := by positivity
  have h1 := cycIntPhase_cycFloor (β := β) (x := ξ.toReal + 4 ^ j)
  rw [h.2.2.2] at h1
  have h2 : (β' : ℤ) = ⌊cycIntPhase β (ξ.toReal + 4 ^ j)⌋ := by exact_mod_cast h1
  have h3 : cycIntPhase β (ξ.toReal + 4 ^ j) < β := by
    unfold cycIntPhase
    have := Int.lt_floor_add_one ((ξ.toReal + 4 ^ j) / β)
    have h4 : β * ((ξ.toReal + 4 ^ j) / β) = ξ.toReal + 4 ^ j := by field_simp
    nlinarith
  have h5 : ((β' : ℤ) : ℝ) < β := by
    rw [h2]; exact lt_of_le_of_lt (Int.floor_le _) h3
  have h6 : (β' : ℝ) < β := by exact_mod_cast h5
  exact Nat.lt_ceil.2 h6

/-- **the inclusion at ES22 §5**, first two claims.  For a good environment `μ`, `W = W^μ_{0,0}` the
first piece, a cyclic integer time `t' ≥ 0` with `W(t') = p` and `t' < t_reg`, and
`W_i = W^μ_{p, q(t')}`: if `W_i ≠ 0` on `(0, 4^n)` (condition (1) on `𝒜_i`) then
`t_reg ≥ t' + 4^n` and `W(t' + s') = W_i(s')` for `s' ≥ 0`. -/
theorem es5_inclusion_restart {μ : Measure (RingSpace d β)} (hμ : Good μ) {t' : ℝ} (ht' : 0 ≤ t')
    {p : Fin d → ℤ} (hp : cycWalk μ 0 0 t' = p) {n : ℕ}
    (hlt : ENNReal.ofReal t' < cycTreg μ)
    (h1 : ∀ t : ℝ, 0 < t → t < 4 ^ n → cycWalk μ p (cycIntPhase β t') t ≠ 0) :
    ENNReal.ofReal (t' + 4 ^ n) ≤ cycTreg μ ∧
      ∀ s' : ℝ, 0 ≤ s' → cycWalk μ 0 0 (t' + s') = cycWalk μ p (cycIntPhase β t') s' := by
  have hβ : 0 < β := Fact.out
  have hrestart : ∀ s' : ℝ, 0 ≤ s' →
      cycWalk μ 0 0 (t' + s') = cycWalk μ p (cycIntPhase β t') s' := by
    intro s' hs'
    rw [cycWalk_restart_cycIntTimes hμ ht' hs', hp]
  refine ⟨?_, hrestart⟩
  by_contra hcon
  push Not at hcon
  have hfin : cycTreg μ < ⊤ := lt_of_le_of_lt hcon.le ENNReal.ofReal_lt_top
  obtain ⟨m, hm1, hm0, hme⟩ := ElboimSly.Cyclic.exists_cycTreg_eq hfin
  rw [hme] at hlt hcon
  have hmβ : 0 ≤ (m : ℝ) * β := by positivity
  have e1 : t' < (m : ℝ) * β := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht').1 hlt
  have e2 : (m : ℝ) * β < t' + 4 ^ n := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hmβ).1 hcon
  apply h1 ((m : ℝ) * β - t') (by linarith) (by linarith)
  rw [← hrestart _ (by linarith)]
  have : t' + ((m : ℝ) * β - t') = (m : ℝ) * β := by ring
  rw [this]; exact hm0

/-- **the inclusion at ES22 §5.**  Together with conditions (2), (6) of `W_i` and the position of
`W(ξ)`, the three claims: `t_reg ≥ t' + 4^n`, `W(t' + s') = W_i(s')`, and `ℰ(ξ)`. -/
theorem es5_inclusion {μ : Measure (RingSpace d β)} (hμ : Good μ) {n j : ℕ}
    (hn : 2000 ≤ n) (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ j) (hj2 : (2 : ℝ) ^ j < 2 * n ^ 20)
    (hlb : Real.log β ≤ (n : ℝ) ^ 40) {ξ : ℝ} (hξ : 0 ≤ ξ) {p : Fin d → ℤ}
    {Bm : Set (Fin d → ℤ)}
    (hcon : cycWalk μ 0 0 (cycFloor β (ξ + 4 ^ j)) = p)
    (hlt : ENNReal.ofReal (cycFloor β (ξ + 4 ^ j)) < cycTreg μ)
    (h1 : ∀ t : ℝ, 0 < t → t < 4 ^ n →
      cycWalk μ p (cycIntPhase β (cycFloor β (ξ + 4 ^ j))) t ≠ 0)
    (h2 : ∀ t : ℝ, 0 < t → t < 4 ^ n → Real.log β ≤ t →
      2 * Real.sqrt t / Real.log t <
        ‖cycWalk μ p (cycIntPhase β (cycFloor β (ξ + 4 ^ j))) t - p‖)
    (h6 : ∀ t : ℝ, 0 ≤ t → t < 4 ^ n →
      (2 : ℝ) ^ j / 8 < Metric.infDist
        (fun c => (cycWalk μ p (cycIntPhase β (cycFloor β (ξ + 4 ^ j))) t c : ℝ))
        ((fun x c => (x c : ℝ)) '' Bm))
    (hWξ : cycWalk μ 0 0 ξ ∈ Bm) (hpB : ‖cycWalk μ 0 0 ξ - p‖ ≤ 2 ^ j) :
    ENNReal.ofReal (cycFloor β (ξ + 4 ^ j) + 4 ^ n) ≤ cycTreg μ ∧
      (∀ s' : ℝ, 0 ≤ s' →
        cycWalk μ 0 0 (cycFloor β (ξ + 4 ^ j) + s') =
          cycWalk μ p (cycIntPhase β (cycFloor β (ξ + 4 ^ j))) s') ∧
      EscEvent n j (fun t => cycWalk μ 0 0 t) ξ := by
  have hβ : 0 < β := Fact.out
  have hx : 0 ≤ ξ + 4 ^ j := by positivity
  have ht'0 : 0 ≤ cycFloor β (ξ + 4 ^ j) := (cycFloor_mem hβ hx).1
  obtain ⟨hA, hB⟩ := es5_inclusion_restart hμ ht'0 hcon hlt h1
  have e1 := cycFloor_le (β := β) (x := ξ + 4 ^ j) hβ
  have e2 := lt_cycFloor_add_one (β := β) (x := ξ + 4 ^ j) hβ
  refine ⟨hA, hB, ?_⟩
  exact es5_inclusion_escape_event hn hj1 hj2 hlb (by linarith) e1
    (fun s' hs' _ => hB s' hs') h2 h6 hWξ hpB

end ElboimSly.Paper.Escape
