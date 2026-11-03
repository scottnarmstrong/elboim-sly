/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib
public import ElboimSlyChallenges.ElboimSly.Defs.FinZeroEvent
public import ElboimSlyChallenges.ElboimSly.Defs.Good
public import ElboimSlyChallenges.ElboimSly.Defs.IndHyp
public import ElboimSlyChallenges.ElboimSly.Defs.InfEvent
public import ElboimSlyChallenges.ElboimSly.Defs.InterchangePi
public import ElboimSlyChallenges.ElboimSly.Defs.IsPoissonPointProcess
public import ElboimSlyChallenges.ElboimSly.Defs.RingIntensity
public import ElboimSlyChallenges.ElboimSly.Defs.RingSpace

/-!
# Challenge: infinite cycles in the interchange process in five dimensions

The main results of D. Elboim and A. Sly, *Infinite cycles in the interchange process in five
dimensions* (arXiv:2211.17023v3), stated from Mathlib alone, in the namespace `ElboimSly.Challenge`:
Theorem 1 (`root_R2`), the bound `P(the cycle of 0 is finite) < 2/β` from its proof (`root_R1`), and
Theorem 3.2 with (H1)–(H5) (`ind_main`); and four theorems behind them: existence and uniqueness of
particle trajectories (`existsUnique_trajectories`), bijectivity of `π_s` (`interchangePi_bijective`),
the KMT coupling for Poisson increments (`poisson_kmt_coupling`), and the strong approximation that
replaces Theorem 7.5 of the paper (`x1theta_coupling`). They are the library's theorems of the same
names in the namespace `ElboimSly`. Existence and uniqueness of trajectories is stated in `Defs/`, as
`ElboimSly.existsUnique_trajectories` with the body `sorry`, because `interchangePi` is defined from
it; the comparator configuration lists it under that name.

Every definition the statements use is in its own file under `Defs/`; these import Mathlib and one
another only. Each theorem below has the body `sorry`. `Solution.lean` proves the same statements
from the library, and leanprover/comparator checks that the two agree, definitions included. The
statements and definitions are generated from those of the library by `scripts/build_challenge.py`.
-/

/-! ## `IndMain` -/

public section

namespace ElboimSly.Challenge

/-- Theorem 3.2, with the index range explicit. For every `d ≥ 5` there are `β₀` and `n₀ ≥ 10` such that
`H(β, n, t₀)` holds for all `β ≥ β₀`, all `n ≥ n₀` and all `t₀ ∈ (1, 4]`. (`β > 0` is the instance
`[Fact (0 < β)]`, D19.) **Deviations:** F03 (`n₀ ≥ 10` explicit) and D11 (`θ_H = 41/100` in (H4)).
ES22 Theorem 3.2. -/
theorem ind_main (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, ∃ n₀ : ℕ, 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        IndHyp d β n t₀ :=
  sorry

end ElboimSly.Challenge

end

/-! ## `InterchangePiBijective` -/

public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Challenge

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- For good `ν` and `s ≥ 0`, `π_s` is a bijection of `ℤᵈ`. pi_s is a permutation
(the formula for the inverse, `y ↦ η_{y,s}(0)`, is not part of this statement). -/
theorem interchangePi_bijective (ν : Measure (RingSpace d β)) (hν : Good ν) (s : ℝ≥0) :
    Function.Bijective (interchangePi ν s) :=
  sorry

end ElboimSly.Challenge

end

/-! ## `PoissonKmtCoupling` -/

public section

open MeasureTheory ProbabilityTheory

namespace ElboimSly.Challenge

/-- A1: KMT coupling for Poisson increments. A1: KMT coupling for Poisson increments.
`Q` is a probability measure on `ℝᴺ × ℝᴺ` with marginals `Poisson(1)^{⊗N}` and `𝒩(0,1)^{⊗N}`;
the maximum over `j ≤ N` is written as an existential over `j : Fin N` (indices are `i ≤ j`). -/
theorem poisson_kmt_coupling :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin N → ℝ) × (Fin N → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin N => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 ≤ x →
          Q.real {p | ∃ j : Fin N,
              C * Real.log N + x ≤ |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|}
            ≤ K * Real.exp (-lam * x) :=
  sorry

end ElboimSly.Challenge

end

/-! ## `RootR1` -/

public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Challenge

universe u

/-- R1: the origin lies in a finite `π_β`-cycle with probability less than `2/β`. R1: the origin is rarely in a finite cycle. For `d ≥ 5` there is `β₀ > 0` such that for every `β ≥ β₀` and every Poisson point
process `N` of intensity `ringIntensity d β` on a probability space `(Ω, P)`,
`P(N ∈ Fin₀) < 2/β`. -/
theorem root_R1 (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          P {ω | N ω ∈ finZeroEvent d β} < ENNReal.ofReal (2 / β) :=
  sorry

end ElboimSly.Challenge

end

/-! ## `RootR2` -/

public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Challenge

universe u

/-- R2 (ES22 Theorem 1): almost surely the interchange permutation `π_β` has an infinite cycle.
R2: Theorem 1. For `d ≥ 5` there is `β₀ > 0` such that for every `β ≥ β₀` and every
Poisson point process `N` of intensity `ringIntensity d β` on a probability space `(Ω, P)`,
`N ∈ Inf` holds `P`-almost surely. -/
theorem root_R2 (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          ∀ᵐ ω ∂P, N ω ∈ infEvent d β :=
  sorry

end ElboimSly.Challenge

end

/-! ## `X1ThetaCoupling` -/

public section

open MeasureTheory ProbabilityTheory

namespace ElboimSly.Challenge

/-- X1θ: strong approximation for bounded sign-symmetric vectors. X1θ: strong approximation for bounded sign-symmetric vectors.
The norm on `Fin d → ℝ` is the sup norm (ℓ∞, D5). -/
theorem x1theta_coupling (d : ℕ) (hd : 1 ≤ d) :
    ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ M : ℝ, 1 ≤ M → M ≤ Real.log ℓ ^ 3 →
      ∀ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ →
        μ {x | ‖x‖ ≤ M} = 1 →
        (∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) → μ.map (fun x => ε * x) = μ) →
        (∀ k, ∫ x, x k ^ 2 ∂μ = 1) →
        ∃ Q : Measure ((Fin ℓ → Fin d → ℝ) × (Fin ℓ → Fin d → ℝ)), IsProbabilityMeasure Q ∧
          Q.map Prod.fst = Measure.pi (fun _ : Fin ℓ => μ) ∧
          Q.map Prod.snd = Measure.pi (fun _ : Fin ℓ =>
            Measure.pi (fun _ : Fin d => gaussianReal 0 1)) ∧
          Q.real {p | ∃ j : Fin ℓ,
              (ℓ : ℝ) ^ ((1 : ℝ) / 4) * Real.log ℓ ^ 12 ≤
                ‖∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - p.2 i)‖}
            ≤ Real.exp (-(Real.log ℓ ^ 3)) :=
  sorry

end ElboimSly.Challenge

end
