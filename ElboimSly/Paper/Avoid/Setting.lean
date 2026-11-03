/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycRegenLaw
public import ElboimSly.Foundations.Cyclic.CycThit
public import ElboimSly.Frozen.Defs.IndHyp
public import ElboimSly.Frozen.Defs.IsRelaxedTime
public import Mathlib

/-!
# ES22 §4: the standing assumptions and the setting of §4–§5

Standing assumptions and the setting of S4--S5.

* `Es4Params d β n₀ n t₀` is (S1)–(S2): the parameters and the induction hypothesis at all lower
  levels. It constrains only the parameters and the law of the regenerated walk.
* `Es4Space` is the probability space: `N`, `N'` Poisson point processes of intensity
  `# ⊗ μ_β` on `ℕ × S_β` and a `σ`-algebra `𝒢₀` with `𝒢₀, σ(N), σ(N')` independent.
* `Es4Setting` bundles the two.
* `avoidWalk N` is the regenerated walk `W` of the environment picture (construction (i) of
  The constructions of the regenerated walk); `avoidFilt` is the joint exploration filtration of the regeneration plan.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

/-- (S1)–(S2) of standing assumptions and the setting of S4--S5: `d ≥ 5`, `n₀ ≥ 8d`, `n > n₀`, `β ≥ β_σ = 10^14`,
`t₀ ∈ (1, 4]`, `t_n > β`, and the induction hypothesis `H(β, n', t₀')` for all integers
`n₀ ≤ n' < n` and all `t₀' ∈ (1, 4]`. Standing assumptions and the setting of S4--S5. -/
structure Es4Params (d : ℕ) (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ) : Prop where
  five_le : 5 ≤ d
  eight_le : 8 * d ≤ n₀
  lt : n₀ < n
  beta_sigma : (10 : ℝ) ^ 14 ≤ β
  one_lt : 1 < t₀
  le_four : t₀ ≤ 4
  beta_lt : β < indScale t₀ n
  ind : ∀ n' : ℕ, n₀ ≤ n' → n' < n → ∀ t' : ℝ, 1 < t' → t' ≤ 4 → IndHyp d β n' t'

/-- The probability space of standing assumptions and the setting of S4--S5: `N` and `N'` are Poisson point processes of
intensity `# ⊗ μ_β` on `ℕ × S_β`, `𝒢₀ ≤ 𝒜`, and `𝒢₀`, `σ(N)`, `σ(N')` are independent
(`Indep 𝒢₀ σ(N)` and `Indep σ(N') (𝒢₀ ∨ σ(N))`). The space is in universe `0`, as `IndHyp`
quantifies over such spaces. -/
structure Es4Space (d : ℕ) (β : ℝ) [Fact (0 < β)] {Ω : Type} (𝒢₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) (N N' : Ω → Measure (CycS ℕ d β)) : Prop where
  ppp : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr
  ppp' : IsPoissonPointProcess N' (cycIntensity ℕ d β) Pr
  le : 𝒢₀ ≤ mΩ
  indep : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr
  indep' : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr

/-- Standing assumptions and the setting of S4--S5: the parameters (S1)–(S2) together with the probability space. -/
structure Es4Setting (d : ℕ) (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ) {Ω : Type}
    (𝒢₀ : MeasurableSpace Ω) [MeasurableSpace Ω] (Pr : Measure Ω)
    (N N' : Ω → Measure (CycS ℕ d β)) : Prop where
  params : Es4Params d β n₀ n t₀
  space : Es4Space d β 𝒢₀ Pr N N'

section defs

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The copies `N^k` (`k = 0, 1, …`) of an environment on `ℕ × S_β`; copy `k` is piece `k + 1`
of the regenerated walk. -/
noncomputable def avoidEnv {Ω : Type*} (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) :
    ℕ → Measure (RingSpace d β) := fun k => copyEnv (N ω) k

/-- The regenerated walk `W = W_reg(ρ^{𝒫_reg}(N))` of standing assumptions and the setting of S4--S5, in the environment
picture: `W(t) = regenWalk (N^0, N^1, …) t`. -/
noncomputable def avoidWalk {Ω : Type*} (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) (t : ℝ) :
    Fin d → ℤ :=
  regenWalk (avoidEnv N ω) t

/-- The same walk as a process on `ℝ≥0`, an element of the path space `ℝ≥0 → ℤ^d`. -/
noncomputable def avoidPath {Ω : Type*} (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) :
    ℝ≥0 → Fin d → ℤ := fun t => avoidWalk N ω (t : ℝ)

/-- The filtration `𝓕_t = 𝓕^{𝒫_reg}_t` of §4–§6: the joint exploration filtration of the
regeneration plan (records of `cycNgood N`, which equals `N` almost surely). -/
noncomputable def avoidFilt {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ d β)}
    (h : Es4Space d β 𝒢₀ Pr N N') : Filtration ℝ≥0 mΩ :=
  cycMultiFilt (regPlan d β) 𝒢₀ h.ppp.measurable h.le Pr

/-- `t_hit(T)` for the regenerated walk: `inf {s > T : ∃ s' ∈ s + βℤ, α(T) < s' < T,
‖W(s) - W(s')‖ ≤ 1}`. Hitting the history; moving fast. -/
noncomputable def avoidThit {Ω : Type*} (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) (T : ℝ) :
    ℝ≥0∞ :=
  cycThit (avoidEnv N ω) T

omit [Fact (0 < β)] in
theorem avoidEnv_eq_cycSlice {Ω : Type*} (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) :
    avoidEnv N ω = fun k => cycSlice k (N ω) := by
  funext k
  exact (cycSlice_eq_map_restrict k (N ω)).symm

end defs

end ElboimSly.Paper

end
