/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.EscInterface
public import Mathlib

/-!
# The interface with §5 with the written proof's constant dependence

Interface with S6; ES22 Theorem 5.1; ES22 Theorem 6.1: `c₅` depends only on `d`, and
`β₅ = β₅(d, n₀)` depends on the base level `n₀`.
-/

@[expose] public section

namespace ElboimSly.Paper.Heavy

/-- §5's interface with the written proof's constant dependence: `c₅` depends only on `d`
(the same for every base level `n₀`), `β₅ = β₅(d, n₀)`. -/
def HeavyEscInterfaceAll (d : ℕ) (E : ℕ → HeavyEscConsts) : Prop :=
  (∀ n₀, (E n₀).c5 = (E 0).c5) ∧
    ∀ (n₀ : ℕ) (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), HeavyEscInterface d β (E n₀) n₀ n t₀

end ElboimSly.Paper.Heavy

end
