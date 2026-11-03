/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Discharge
public import Mathlib

/-!
# W_2 after zeta_i, given ℱ^+_zeta_i for `Z = ζ_i`

W_2 after zeta_i, given ℱ^+_zeta_i; Measurability. `step78_couple_zeta` is `step78_couple` with
`Z = ζ_i` of `Step78Data`, the stopping-time and measurability typing data being discharged by
`step78_isStoppingTime_T`, `step78_measurable_delta` and `isStoppingTime_zp_zeta`
(`step78_frame`). The standing data are `1 ≤ d`, `1 < β` and the independence structure of
`cyc_plan_coupling_regen_law`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS Unit d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity Unit d β) Pr)
  (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
  (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
      cycNull Pr) Pr)

include hN hN' hN'' hI1 hI2 hI3 in
/-- **w_2 after zeta_i, given ℱ^+_zeta_i** for every `(ℱ⁺_t)`-stopping time `Z`, with no typing hypothesis. -/
theorem step78_couple_of_shifted (h𝒢 : 𝒢₀ ≤ mΩ) {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) :
    (∀ {A : Set Ω},
      MeasurableSet[(step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ).measurableSpace] A →
      ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)}, MeasurableSet Γ →
      Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤} ∩
          {ω | contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z)
            (step78Delta N u q Z) ω) (contSeq N'' ω) ∈ Γ}) =
        Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤}) *
          Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈
            Γ}) ∧
    (∀ᵐ ω ∂Pr, Z ω ≠ ⊤ → ∀ s : ℝ≥0, (Z ω + (s : WithTop ℝ≥0)) ≤ step78B N u q Tn Z ω →
      cycWalk (cycSlice () (cycNgood N ω)) u q ((ElboimSly.SRW.stopReal Z ω : ℝ) + s) -
          cycWalk (cycSlice () (cycNgood N ω)) u q (ElboimSly.SRW.stopReal Z ω) =
        contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z)
          (step78Delta N u q Z) ω) (contSeq N'' ω) s) :=
  step78_couple u q Tn 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢
    (step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ)
    (step78_measurable_delta u q Tn 𝒢₀ hN h𝒢 (step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ))

include hN hN' hN'' hI1 hI2 hI3 in
/-- **w_2 after zeta_i, given ℱ^+_zeta_i** for `Z = ζ_i`: with `W' = contGlue … (contSeq N'')` the regenerated walk
of plan-level coupling after a stopping time (d), `W'` is independent of `ℱ⁺_{ζ_i}` with the law of the regenerated
walk, and a.s. on `{ζ_i < ∞}` (in particular on `{ζ_i < t'_n}`),
`W₂(ζ_i + s) - W₂(ζ_i) = W'(s)` for all `s` with `ζ_i + s ≤ b_i`. -/
theorem step78_couple_zeta (h𝒢 : 𝒢₀ ≤ mΩ) (hd : 1 ≤ d) (hβ : 1 < β) (n : ℕ) (ρ : ℝ) (i : ℕ) :
    let Z := (step78SliceData (cycNgood N) u q Tn n ρ).zeta i
    (∀ {A : Set Ω},
      MeasurableSet[(step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢
        (Step78Data.isStoppingTime_zp_zeta (step78_frame u q Tn 𝒢₀ hN h𝒢 hd hβ n ρ) i).2
        ).measurableSpace] A →
      ∀ {Γ : Set (ℝ≥0 → Fin d → ℤ)}, MeasurableSet Γ →
      Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤} ∩
          {ω | contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z)
            (step78Delta N u q Z) ω) (contSeq N'' ω) ∈ Γ}) =
        Pr (A ∩ {ω | step78T Tn Z ω ≠ ⊤}) *
          Pr {ω | (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ)) ∈
            Γ}) ∧
    (∀ᵐ ω ∂Pr, Z ω ≠ ⊤ → ∀ s : ℝ≥0, (Z ω + (s : WithTop ℝ≥0)) ≤ step78B N u q Tn Z ω →
      cycWalk (cycSlice () (cycNgood N ω)) u q ((ElboimSly.SRW.stopReal Z ω : ℝ) + s) -
          cycWalk (cycSlice () (cycNgood N ω)) u q (ElboimSly.SRW.stopReal Z ω) =
        contGlue β.toNNReal (planFirst (step78Plan d β u q Tn) N N' (step78T Tn Z)
          (step78Delta N u q Z) ω) (contSeq N'' ω) s) :=
  step78_couple_of_shifted u q Tn 𝒢₀ hN hN' hN'' hI1 hI2 hI3 h𝒢
    (Step78Data.isStoppingTime_zp_zeta (step78_frame u q Tn 𝒢₀ hN h𝒢 hd hβ n ρ) i).2

end ElboimSly.Paper.Step

end
