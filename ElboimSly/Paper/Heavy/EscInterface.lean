/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasStop5
public import ElboimSly.Paper.Heavy.Thresholds
public import ElboimSly.Paper.Heavy.Scales
public import ElboimSly.Paper.Avoid.Setting
public import ElboimSly.Paper.Escape.Blocks
public import ElboimSly.Paper.Escape.Gamma
public import ElboimSly.Paper.Heavy.RegenAdapted

/-!
# The interface with §5 used by Lemma 6.2

Interface with S6 (statement only), standing assumptions.

* `heavyEscSet W n j ξ`: the escape event `ℰ(ξ) = {ξ < ∞} ∩ {∀ s ∈ [4^j, 4^n], ‖W(ξ+s) - W(ξ)‖ ≥ √s/n}`.
* `HeavyEscInterface d β E n₀ n t₀`: the conclusion of interface with S6, for the regenerated
  walk `avoidWalk (cycNgood N)` of the good version of `N` (equal to `N` almost surely), the
  filtration `avoidFilt`, any versions `V_{B'}` of
  `P(ℰ(ξ_{B'}) | ℱ_{ξ_{B'}})`, and the stopping time `τ_V = τ^{(6)}_esc`:
  `P(τ^{(6)}_esc < t_n ∧ t_reg) ≤ e^{-c₅ n³}`.

It is a hypothesis of the distinctly named `es6_two_of_interface` (rule 6): the corollary is proved
in §5 and is not proved here.  The adaptedness of the regenerated walk to `avoidFilt`
(ES22 Lemma 2.1 (a)) is `avoidWalk_cycNgood_adapted` (`RegenAdapted.lean`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

/-- The escape event `ℰ(ξ)` for a random time `ξ`; empty on `{ξ = ∞}`. -/
def heavyEscSet {Ω : Type*} {d : ℕ} (W : Ω → ℝ → Fin d → ℤ) (n j : ℕ) (ξ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | ξ ω ≠ ⊤ ∧ EscEvent n j (W ω) (ξ ω).toReal}

/-- The first entrance time `ξ_{B'}` of the block `B' = heavyBlock j ι'`. -/
noncomputable def heavyXi {Ω : Type*} {d : ℕ} (W : Ω → ℝ → Fin d → ℤ) (j : ℕ) (ι' : Fin d → ℤ) :
    Ω → ℝ≥0∞ :=
  fun ω => entranceTime (W ω) (heavyBlock j ι')

/-- The canonical version `P(ℰ(ξ_{B'}) | ℱ_{ξ_{B'}})` (the conditional expectation itself). -/
noncomputable def heavyEscVersion {Ω : Type*} {m0 : MeasurableSpace Ω} {f : Filtration ℝ≥0 m0}
    {d : ℕ} {W : Ω → ℝ → Fin d → ℤ} (hAd : AdaptedCyclic f W) (μ : Measure Ω) (n : ℕ)
    (ι' : Fin d → ℤ) : Ω → ℝ :=
  μ[(heavyEscSet W n (heavyScaleJ n) (heavyXi W (heavyScaleJ n) ι')).indicator
      (fun _ => (1 : ℝ)) |
    (hAd.isStoppingTime_entrance (heavyBlock (heavyScaleJ n) ι')).measurableSpace]

/-- The `d`-dimensional conclusion of interface with S6, in the form consumed by
ES22 Lemma 6.2.  Typing data: the constants `c₅`, `β₅` of `E`. -/
def HeavyEscInterface (d : ℕ) (β : ℝ) [Fact (0 < β)] (E : HeavyEscConsts) (n₀ n : ℕ) (t₀ : ℝ) :
    Prop :=
  ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ d β)} (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N'),
    E.beta5 ≤ β →
    ∀ (V : (Fin d → ℤ) → Ω → ℝ)
      (_ : ∀ ι, Measurable[((avoidWalk_cycNgood_adapted S).isStoppingTime_entrance
        (heavyBlock (heavyScaleJ n) ι)).measurableSpace] (V ι))
      (_ : ∀ ι, V ι =ᵐ[Pr] heavyEscVersion (avoidWalk_cycNgood_adapted S) Pr n ι),
    Pr {ω | heavyTauV (avoidWalk (cycNgood N) ω) (heavyScaleJ n) (fun ι => V ι ω)
        ((n : ℝ) ^ (-escGamma d)) <
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (avoidEnv (cycNgood N) ω 0))} ≤
      ENNReal.ofReal (Real.exp (-(E.c5 * (n : ℝ) ^ 3)))

end ElboimSly.Paper.Heavy
