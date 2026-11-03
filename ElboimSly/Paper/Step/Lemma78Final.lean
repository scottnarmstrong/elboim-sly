/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Assemble
public import ElboimSly.Paper.Step.Lemma78H1
public import Mathlib

/-!
# Lemma 7.8 from the interface

ES22 Lemma 7.8. The event cH_1 is discharged by `step78_H1`. The only residual
hypothesis is few excursions (`Step78ClaimJ`, the excursion claim in the `{J > n³}` form, being
proved on `wip/paper-step-78b`); the theorem is named `..._of_J` until it is discharged.
-/

@[expose] public section

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

/-- ES22 Lemma 7.8 conditional only on few excursions. -/
theorem step_lemma78_of_interface_of_J {d : ℕ} (hd : 5 ≤ d) (E : ℕ → HeavyEscConsts)
    (hI : HeavyEscInterfaceAll d E) (hJ : Step78ClaimJ d) : ∃ cPp βPp, StepPp d cPp βPp :=
  step78_assemble hd E hI (step78_H1 hd hI) hJ

end ElboimSly.Paper.Step

end
