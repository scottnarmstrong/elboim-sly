/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvProbe
public import ElboimSly.Foundations.Cyclic.CycSchemeInst
public import Mathlib

/-!
# The driving scheme (a): the driving scheme and the maps `Ψ_j`

The driving scheme (a), first sentence.

* `drvPsi P sc jx j0 U k : ℋ'_k → ℋ_k` is `Ψ_k`, defined by `Ψ_0 = *`,
  `Ψ_{k+1}(η', o') = (Ψ_k(η'), ψ_{η'}(o'))`, where the environment state is
  `stateAt P sc k (Ψ_k η')`;
* `drvScheme P sc jx j0 hj U` is the driving scheme: `R'_k η' = drvProbeR (stateAt k (Ψ_k η'))`, horizon
  `hOf (stateAt k (Ψ_k η'))`. It is an exploration scheme on `(𝒮', μ')` (`measurable_R`, `isProbe`);
* `measurable_drvPsi`: `Ψ_k` is measurable.

The auxiliary space `U` is arbitrary (the written proof takes a point); `Ψ` does not touch it.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
  {J : Type*} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  (jx : ∀ k : ℕ, CycRecN I d k → J) (j0 : J) (P : CycPlan I d β) (sc : ℝ≥0∞)
  (U : Type*) [MeasurableSpace U]

/-- The maps `Ψ_k : ℋ'_k → ℋ_k` of the driving scheme. -/
noncomputable def drvPsi : (k : ℕ) → Hist U (DrvS d J) k → Hist U (CycS I d β) k
  | 0, η => (η.1, fun i => i.elim0)
  | k + 1, η => (drvPsi k η.init).snoc
      (drvPsiOut (jx := jx) (β := β) j0 P sc (CycScheme.stateAt P sc k (drvPsi k η.init)) η.last)

variable {jx}

theorem measurable_drvPsi (hj : ∀ k, Measurable (jx k)) (k : ℕ) :
    Measurable (drvPsi jx j0 P sc U k) := by
  induction k with
  | zero => exact measurable_fst.prodMk (measurable_pi_iff.2 fun i => i.elim0)
  | succ k ih =>
    have h1 : Measurable fun η : Hist U (DrvS d J) (k + 1) => drvPsi jx j0 P sc U k η.init :=
      ih.comp (Hist.measurable_init k)
    have h2 : Measurable fun η : Hist U (DrvS d J) (k + 1) =>
        CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η.init) :=
      (CycScheme.measurable_stateAt P sc k).comp h1
    exact (Hist.measurable_snoc k).comp
      (h1.prodMk ((measurable_drvPsiOut j0 P sc hj).comp (h2.prodMk (Hist.measurable_last k))))

/-- The driving scheme (a): the driving scheme is an exploration scheme on `(𝒮', μ')`. -/
noncomputable def drvScheme (hj : ∀ k, Measurable (jx k)) :
    ExplScheme (drvIntensity d J) U where
  R k η := drvProbeR (β := β) jx j0 P sc
    (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η))
  h k η := CycScheme.hOf P sc (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η))
  measurable_R k :=
    (measurable_drvProbeR j0 P sc hj).comp
      ((((CycScheme.measurable_stateAt P sc k).comp
        ((measurable_drvPsi j0 P sc U hj k).comp measurable_fst))).prodMk measurable_snd)
  measurable_h k :=
    measurable_hOf (P := P) (sc := sc)
      ((CycScheme.measurable_stateAt P sc k).comp (measurable_drvPsi j0 P sc U hj k))
  isProbe _k _η := isProbe_drvProbeR j0 P sc hj _

end ElboimSly.Cyclic

end
