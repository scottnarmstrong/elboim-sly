/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenWalk
import Mathlib

/-!
# Well-definedness of the driven construction

Well-definedness and measurability of the driven construction (a): `E(x)` is locally finite; the driven walk is a right-continuous
path with `w(0) = 0`, jumps of `ℓ¹`-size `1` lying in `E(x)`, satisfying (D1)--(D3) at every
`t ∈ (0, treg]`; and any right-continuous path with finitely many jumps on `[0, T]`, `T ≤ treg`,
satisfying (D1)--(D3) agrees with it.  We also prove causality: `w^x` on `[0, T]` only depends on
`x` on `[0, T]`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {x y : ℝ≥0 → Fin d → ℤ} {β : ℝ≥0}

/-- The jumps of the driven walk have `ℓ¹`-size `1`. -/
theorem drivenWalk_unit (hx : IsDrivingPath x) (hβ : 0 < β) :
    ∀ s ∈ CDisc (drivenWalk β x), IsUnitStep (drivenWalk β x s - leftVal (drivenWalk β x) s) := by
  have hreg := drivenWalk_isRegPath hx.toIsRegPath hβ
  have hQ : ∀ n : ℕ, ∀ s ∈ CDisc (drivenWalk β x), (s : ℝ≥0∞) ≤ drivenTimes β x n →
      IsUnitStep (drivenWalk β x s - leftVal (drivenWalk β x) s) := by
    intro n
    induction n with
    | zero =>
      intro s hs hle
      rw [drivenTimes_zero] at hle
      have : s = 0 := by exact_mod_cast le_antisymm hle bot_le
      exact absurd this hs.1.ne'
    | succ n ih =>
      intro s hs hle
      by_cases hsn : (s : ℝ≥0∞) ≤ drivenTimes β x n
      · exact ih s hs hsn
      rw [not_le] at hsn
      have hsE := mem_events_of_mem_CDisc hx.toIsRegPath hβ hs
      have hge : drivenTimes β x (n + 1) ≤ s := not_event_between hx.toIsRegPath hβ hsE hsn
      have hseq : drivenTimes β x (n + 1) = s := le_antisymm hge hle
      have hjump : leftVal (drivenWalk β x) s ≠ drivenWalk β x s :=
        (hreg.mem_CDisc_iff.1 hs).2
      have hw := drivenWalk_rule hx.toIsRegPath hβ hs.1
      unfold drivenRuleVal at hw
      by_cases hF : ∃ k, ForcedAt β (drivenWalk β x) s k
      · rw [ite_eq_left hF] at hw
        have hk0 := Nat.sInf_mem hF
        obtain ⟨hid, hJ, heq⟩ := hk0
        set s' := s - (sInf {k | ForcedAt β (drivenWalk β x) s k} : ℕ) * β with hs'
        have hs'lt : s' < s := delayIdx_lt β hβ hid
        have hs'le : (s' : ℝ≥0∞) ≤ drivenTimes β x n := by
          by_contra hcon
          rw [not_le] at hcon
          have := not_event_between hx.toIsRegPath hβ
            (mem_events_of_mem_CDisc hx.toIsRegPath hβ hJ) hcon
          rw [hseq] at this
          exact absurd hs'lt (not_lt.2 (by exact_mod_cast this))
        have hu := ih s' hJ hs'le
        have : drivenWalk β x s - leftVal (drivenWalk β x) s =
            -(drivenWalk β x s' - leftVal (drivenWalk β x) s') := by
          have heq' : drivenWalk β x s' = leftVal (drivenWalk β x) s := heq
          rw [hw, ← heq']; abel
        rw [this]; exact isUnitStep_neg.2 hu
      · rw [ite_eq_right hF] at hw
        by_cases hxs : s ∈ CDisc x
        · rw [ite_eq_left hxs] at hw
          by_cases hT : TakenAt β x (drivenWalk β x) s
          · rw [ite_eq_left hT] at hw
            have : drivenWalk β x s - leftVal (drivenWalk β x) s = x s - leftVal x s := by
              rw [hw]; abel
            rw [this]; exact hx.unit s hxs
          · rw [ite_eq_right hT] at hw; exact absurd hw.symm hjump
        · rw [ite_eq_right hxs] at hw; exact absurd hw.symm hjump
  intro s hs
  obtain ⟨n, hn1, hn2⟩ := exists_interval hx.toIsRegPath hβ s
  exact hQ (n + 1) s hs hn2.le

/-- Causality: `w^x` on `[0, T]` only depends on `x` on `[0, T]`. -/
theorem drivenWalk_congr (hx : IsRegPath x) (hy : IsRegPath y) (hβ : 0 < β) {T : ℝ≥0}
    (hxy : ∀ s ≤ T, x s = y s) : ∀ s ≤ T, drivenWalk β x s = drivenWalk β y s :=
  eq_on_of_rules hβ hxy (fun s _ => (drivenWalk_isRegPath hx hβ).rc s)
    (fun s _ => (drivenWalk_isRegPath hy hβ).rc s)
    (by rw [drivenWalk_zero hx hβ, drivenWalk_zero hy hβ])
    (fun _ ht _ => drivenWalk_rule hx hβ ht) (fun _ ht _ => drivenWalk_rule hy hβ ht)

/-- Well-definedness and measurability of the driven construction (a), uniqueness: a right-continuous path on `[0, T]` that starts at `0`
and satisfies (D1)--(D3) at every `t ∈ (0, T]` agrees with `w^x` on `[0, T]` (for any `T`; in
particular for `T ≤ treg^x`).  Finiteness of the jumps of `p` is not needed. -/
theorem drivenWalk_unique (hx : IsRegPath x) (hβ : 0 < β) {T : ℝ≥0} {p : ℝ≥0 → Fin d → ℤ}
    (hrc : ∀ s < T, ∀ᶠ u in 𝓝[≥] s, p u = p s) (h0 : p 0 = 0)
    (hD : ∀ t, 0 < t → t ≤ T → DrivenD1 β p t ∧ DrivenD2 β x p t ∧ DrivenD3 β x p t) :
    ∀ s ≤ T, p s = drivenWalk β x s :=
  eq_on_of_rules hβ (fun _ _ => rfl) hrc (fun s _ => (drivenWalk_isRegPath hx hβ).rc s)
    (by rw [h0, drivenWalk_zero hx hβ])
    (fun t ht hT => (drivenD123_iff β x p t).1 (hD t ht hT))
    (fun _ ht _ => drivenWalk_rule hx hβ ht)

/-- Well-definedness and measurability of the driven construction (a), the rules: `w^x` satisfies (D1)--(D3) at every `t > 0`. -/
theorem drivenWalk_D123 (hx : IsRegPath x) (hβ : 0 < β) {t : ℝ≥0} (ht : 0 < t) :
    DrivenD1 β (drivenWalk β x) t ∧ DrivenD2 β x (drivenWalk β x) t ∧
      DrivenD3 β x (drivenWalk β x) t :=
  (drivenD123_iff β x _ t).2 (drivenWalk_rule hx hβ ht)

/-- **Well-definedness and measurability of the driven construction (a)**, for a driving path `x` and `β > 0`:
`E(x)` is locally finite; `w^x` is right-continuous with `w^x(0) = 0`, finitely many jumps on
bounded intervals, all of `ℓ¹`-size `1` and lying in `E(x)`; it satisfies (D1)--(D3) at every
`t ∈ (0, treg^x]` with `t < ∞`; and every right-continuous `p : [0, T] → ℤ^d`, `T ≤ treg^x`,
with `p(0) = 0` and finitely many jumps that satisfies (D1)--(D3) at every `t ∈ (0, T]` agrees with
`w^x` on `[0, T]`.

Difference from the written proof: `drivenWalk β x` is defined on all of `[0, ∞)` by the same
recursion (the written proof stops at `treg^x`); only its restriction to `[0, treg^x]` is the written proof's
`w^x`. -/
theorem drivenWalk_wd_a (hx : IsDrivingPath x) (hβ : 0 < β) :
    (∀ T : ℝ≥0, (drivenEvents β x ∩ Iic T).Finite) ∧
    (∀ s, ∀ᶠ u in 𝓝[≥] s, drivenWalk β x u = drivenWalk β x s) ∧
    drivenWalk β x 0 = 0 ∧
    (∀ T : ℝ≥0, (CDisc (drivenWalk β x) ∩ Iic T).Finite) ∧
    (∀ s ∈ CDisc (drivenWalk β x), IsUnitStep (drivenWalk β x s - leftVal (drivenWalk β x) s)) ∧
    (∀ s ∈ CDisc (drivenWalk β x), s ∈ drivenEvents β x) ∧
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ drivenTreg β x →
      DrivenD1 β (drivenWalk β x) t ∧ DrivenD2 β x (drivenWalk β x) t ∧
        DrivenD3 β x (drivenWalk β x) t) ∧
    (∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ drivenTreg β x → ∀ p : ℝ≥0 → Fin d → ℤ,
      (∀ s < T, ∀ᶠ u in 𝓝[≥] s, p u = p s) → (CDisc p ∩ Iic T).Finite → p 0 = 0 →
      (∀ t, 0 < t → t ≤ T → DrivenD1 β p t ∧ DrivenD2 β x p t ∧ DrivenD3 β x p t) →
      ∀ s ≤ T, p s = drivenWalk β x s) :=
  ⟨drivenEvents_finite hx.toIsRegPath hβ, (drivenWalk_isRegPath hx.toIsRegPath hβ).rc,
    drivenWalk_zero hx.toIsRegPath hβ, (drivenWalk_isRegPath hx.toIsRegPath hβ).fin,
    drivenWalk_unit hx hβ, fun _ hs => mem_events_of_mem_CDisc hx.toIsRegPath hβ hs,
    fun _ ht _ => drivenWalk_D123 hx.toIsRegPath hβ ht,
    fun _ _ _ hrc _ h0 hD => drivenWalk_unique hx.toIsRegPath hβ hrc h0 hD⟩

end ElboimSly.Cyclic

end
