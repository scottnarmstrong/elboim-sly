/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadClosed

/-!
# Properties of discovered bad blocks: attainment

Properties of discovered bad blocks (a).

* `upward_dichotomy`: an upward-closed, right-stable predicate on `[0, ∞)` is either never true
  or true exactly on `[m, ∞)`.
* `badByTime_dichotomy`: for each block there is `t_B ∈ [0, ∞]` with
  `{t : B bad by time t} = [t_B, ∞)`.
* `badSet_eventually_eq`, `badCount_eventually_eq`: `b_t` is right-continuous (locally constant
  from the right).
* `badCount_dichotomy`: for each threshold `ℓ`, `inf {t : b_t ≥ ℓ}` is attained when finite.
-/

@[expose] public section

open Set Filter Topology

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {β t₀ : ℝ} {n : ℕ} {w : ℝ → Fin d → ℤ} {ι : Fin d → ℤ}

theorem upward_dichotomy {P : ℝ → Prop} (hmono : ∀ t t', t ≤ t' → P t → P t')
    (hstable : ∀ s, 0 ≤ s → ¬ P s → ∀ᶠ η in 𝓝[>] (0 : ℝ), ¬ P (s + η)) :
    (∀ t, 0 ≤ t → ¬ P t) ∨ ∃ m, 0 ≤ m ∧ ∀ t, 0 ≤ t → (P t ↔ m ≤ t) := by
  by_cases hex : ∃ t, 0 ≤ t ∧ P t
  · right
    set S : Set ℝ := {t | 0 ≤ t ∧ P t} with hS
    have hne : S.Nonempty := hex
    have hb : BddBelow S := ⟨0, fun t ht => ht.1⟩
    have hm0 : 0 ≤ sInf S := le_csInf hne fun t ht => ht.1
    have hPm : P (sInf S) := by
      by_contra hn
      obtain ⟨η, hη, hηpos⟩ := ((hstable _ hm0 hn).and self_mem_nhdsWithin).exists
      obtain ⟨t, ht, ht2⟩ := exists_lt_of_csInf_lt hne
        (show sInf S < sInf S + η from by linarith [show (0 : ℝ) < η from hηpos])
      exact hη (hmono t _ ht2.le ht.2)
    refine ⟨sInf S, hm0, fun t ht0 => ⟨fun hP => csInf_le hb ⟨ht0, hP⟩, fun hle =>
      hmono _ _ hle hPm⟩⟩
  · left
    exact fun t ht hP => hex ⟨t, ht, hP⟩

theorem BadByTime.nonneg (htk : 0 ≤ heavyTkPrime d t₀ n) {t : ℝ}
    (h : BadByTime d β t₀ n w ι t) : 0 ≤ t := by
  rw [badByTime_iff] at h
  rcases h with ⟨x, hx, -, h, -⟩ | ⟨x, hx, h, -⟩ | ⟨x, hx, x₂, hx₂, -, -, h, -⟩
  · linarith [hx.1]
  · linarith [hx.1]
  · linarith [hx.1]

variable (hw : IsCyclicPath w) (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n)

include hw hβ htk in
/-- Properties of discovered bad blocks (a): the set of times at which `B_ι` is bad is empty or a
closed half-line `[t_B, ∞)`. -/
theorem badByTime_dichotomy :
    (∀ t, 0 ≤ t → ¬ BadByTime d β t₀ n w ι t) ∨
      ∃ m, 0 ≤ m ∧ ∀ t, 0 ≤ t → (BadByTime d β t₀ n w ι t ↔ m ≤ t) :=
  upward_dichotomy (fun _ _ h hb => BadByTime.mono hb h)
    (fun _ hs hn => badByTime_eventually_not hw hβ htk hs hn)

include hw hβ htk in
theorem badSet_eventually_eq {s : ℝ} (hs : 0 ≤ s) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ),
      {ι | BadByTime d β t₀ n w ι (s + η)} = {ι | BadByTime d β t₀ n w ι s} := by
  have hF : {ι | BadByTime d β t₀ n w ι (s + 1)}.Finite := badSet_finite hβ htk _
  have hall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ ι ∈ {ι | BadByTime d β t₀ n w ι (s + 1)},
      BadByTime d β t₀ n w ι s ∨ ¬ BadByTime d β t₀ n w ι (s + η) := by
    refine (Filter.eventually_all_finite hF).2 fun ι _ => ?_
    by_cases hb : BadByTime d β t₀ n w ι s
    · exact Eventually.of_forall fun _ => Or.inl hb
    · filter_upwards [badByTime_eventually_not hw hβ htk hs hb] with η h using Or.inr h
  filter_upwards [hall, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with η h1 h2
  ext ι
  constructor
  · intro hι
    have : ι ∈ {ι | BadByTime d β t₀ n w ι (s + 1)} := BadByTime.mono hι (by linarith [h2.2])
    rcases h1 ι this with h | h
    · exact h
    · exact absurd hι h
  · intro hι
    exact BadByTime.mono hι (by linarith [h2.1])

include hw hβ htk in
theorem badCount_eventually_eq {s : ℝ} (hs : 0 ≤ s) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), badCount d β t₀ n w (s + η) = badCount d β t₀ n w s := by
  filter_upwards [badSet_eventually_eq hw hβ htk hs] with η h
  unfold badCount
  rw [h]

include hw hβ htk in
/-- Properties of discovered bad blocks (a): for every threshold `ℓ` the infimum of
`{t : b_t ≥ ℓ}` is attained when finite. -/
theorem badCount_dichotomy (ℓ : ℕ) :
    (∀ t, 0 ≤ t → ¬ ℓ ≤ badCount d β t₀ n w t) ∨
      ∃ m, 0 ≤ m ∧ ∀ t, 0 ≤ t → (ℓ ≤ badCount d β t₀ n w t ↔ m ≤ t) := by
  refine upward_dichotomy (fun t t' h hb => hb.trans (badCount_mono hβ htk h)) ?_
  intro s hs hn
  filter_upwards [badCount_eventually_eq hw hβ htk hs] with η h
  rwa [h]

end ElboimSly.Paper
