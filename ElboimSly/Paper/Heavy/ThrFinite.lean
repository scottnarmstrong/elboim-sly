/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ThrE

/-!
# The thresholds are finite

The thresholds are finite.

* `heavyT_eventually`: (T1)-(T11) hold for all large `n`.
* `thresholds_finite`: there is `M` with `HeavyT d n₀ E n` for all `n ≥ M`.
* `heavyN6_set_nonempty`, `heavyN6_le`: the threshold `N₆` is attained and is at most
  `max (M, N₅, n₀+1, 4)`.
* `HeavyT.of_ge_N6`, `heavyN6_ge_aux`: for `n ≥ N₆`, `HeavyT` holds (no hypothesis on the set).
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem heavyT_eventually (hd : 1 ≤ d) (n₀ : ℕ) (E : HeavyEscConsts) :
    ∀ᶠ n : ℕ in atTop, HeavyT d n₀ E n := by
  filter_upwards [ev_T1 hd n₀, ev_T2 hd, ev_T3, ev_T4, ev_T5 hd, ev_T6 hd, ev_T7 hd, ev_T8 hd,
    ev_T9 hd, ev_T10 hd, ev_T11 (E := E) hd] with n h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The thresholds are finite. -/
theorem thresholds_finite (hd : 1 ≤ d) (n₀ : ℕ) (E : HeavyEscConsts) :
    ∃ M : ℕ, ∀ n, M ≤ n → HeavyT d n₀ E n :=
  eventually_atTop.1 (heavyT_eventually hd n₀ E)

theorem heavyN6_set_nonempty (hd : 1 ≤ d) (n₀ : ℕ) (E : HeavyEscConsts) :
    {N : ℕ | max (max E.N5 (n₀ + 1)) 4 ≤ N ∧ ∀ n, N ≤ n → HeavyT d n₀ E n}.Nonempty := by
  obtain ⟨M, hM⟩ := thresholds_finite hd n₀ E
  exact ⟨max M (max (max E.N5 (n₀ + 1)) 4), le_max_right _ _,
    fun n hn => hM n ((le_max_left _ _).trans hn)⟩

/-- The thresholds are finite: `N₆ ≤ max (M, N₅, n₀ + 1, 4)`. -/
theorem heavyN6_le (hd : 1 ≤ d) (n₀ : ℕ) (E : HeavyEscConsts) :
    ∃ M : ℕ, heavyN6 d n₀ E ≤ max M (max (max E.N5 (n₀ + 1)) 4) := by
  obtain ⟨M, hM⟩ := thresholds_finite hd n₀ E
  exact ⟨M, Nat.sInf_le ⟨le_max_right _ _, fun n hn => hM n ((le_max_left _ _).trans hn)⟩⟩

/-- For `n ≥ N₆`, the conditions (T1)-(T11) hold (the replacement of the `HeavyT n` hypotheses). -/
theorem HeavyT.of_ge_N6 (hd : 1 ≤ d) {n₀ : ℕ} {E : HeavyEscConsts} {n : ℕ}
    (hn : heavyN6 d n₀ E ≤ n) : HeavyT d n₀ E n :=
  HeavyT.of_ge_heavyN6 (heavyN6_set_nonempty hd n₀ E) hn

/-- For `n ≥ N₆`, `n ≥ max (N₅, n₀ + 1, 4)`. -/
theorem heavyN6_ge_aux (hd : 1 ≤ d) {n₀ : ℕ} {E : HeavyEscConsts} {n : ℕ}
    (hn : heavyN6 d n₀ E ≤ n) : max (max E.N5 (n₀ + 1)) 4 ≤ n :=
  le_of_ge_heavyN6 (heavyN6_set_nonempty hd n₀ E) hn

end ElboimSly.Paper.Heavy
