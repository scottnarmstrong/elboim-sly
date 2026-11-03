/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMarkovTransfer
public import ElboimSly.Foundations.Cyclic.CycMultiRM
public import Mathlib

/-!
# The ring measure and the conditional integrals, transferred to `S_β`

* `rm_cycRecStop_markov`: `cycRM(cycRec^{𝒫_W}(T)) = liftU (Σ_{x ∈ jump points of W on (0,T]} δ_x)`;
* `lintegral_restrict_liftU`: transfer of `∫⁻ G(ν|_A) dLaw(N̂)` between `Unit × S_β` and `S_β`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

theorem liftU_count_restrict (J : Set (RingSpace d β)) :
    liftU (Measure.count.restrict J) = Measure.count.restrict ({()} ×ˢ J) := by
  refine Measure.ext fun s hs => ?_
  have hpre : MeasurableSet (Prod.mk () ⁻¹' s : Set (RingSpace d β)) := measurable_prodMk_left hs
  unfold liftU
  rw [Measure.map_apply measurable_prodMk_left hs, Measure.restrict_apply hpre,
    Measure.restrict_apply hs]
  rw [← Measure.count_injective_image (f := Prod.mk ()) (fun a b h => (Prod.mk.inj h).2)]
  congr 1
  ext x
  obtain ⟨⟨⟩, y⟩ := x
  simp

theorem rm_cycRecStop_markov (N : Ω → Measure (RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    (cycRecStop (onePlan d β) (cycNgood fun ω => liftU (N ω)) T ω).rm β =
      liftU (Measure.count.restrict (markovRings N T ω)) := by
  unfold cycRecStop CycRec.rm
  rw [show cycNgood (fun ω => liftU (N ω)) ω = liftU (markovNgood N ω) from
    (liftU_markovNgood N ω).symm, trunc_envFinal_onePlan, ringSet_inl_one,
    ringSet_markovEntry (good_markovNgood N ω), liftU_count_restrict]
  unfold markovRings ElboimSly.SRW.stopReal
  cases hh : T ω using WithTop.recTopCoe with
  | top =>
    have : cycJumpRings β (fun s => ElboimSly.cycWalk (markovNgood N ω) 0 0 s) 0 0 = ∅ := by
      ext x; simp [cycJumpRings]; intro t h1 h2; exact absurd (h1.trans_le h2) (lt_irrefl _)
    simp only [WithTop.recTopCoe_top, WithTop.untopD_top, NNReal.coe_zero, this]
  | coe t =>
    simp only [WithTop.recTopCoe_coe, WithTop.untopD_coe, markovW]

theorem measurable_restrict_set {S : Type*} [MeasurableSpace S] {A : Set S} (hA : MeasurableSet A) :
    Measurable (fun ν : Measure S => ν.restrict A) :=
  Measure.measurable_of_measurable_coe _ fun B hB => by
    simp only [Measure.restrict_apply hB]
    exact Measure.measurable_coe (hB.inter hA)

/-- Transfer of the conditional integral against `Law(N̂)` to `S_β`. -/
theorem lintegral_restrict_liftU {Pr : Measure Ω} {N : Ω → Measure (RingSpace d β)}
    (hN : Measurable N) {A : Set (RingSpace d β)} (hA : MeasurableSet A)
    {G : Measure (RingSpace d β) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ νh, G (cycSlice () (νh.restrict ({()} ×ˢ A))) ∂(Pr.map fun ω => liftU (N ω)) =
      ∫⁻ ν, G (ν.restrict A) ∂(Pr.map N) := by
  have hSA : MeasurableSet ({()} ×ˢ A : Set (Unit × RingSpace d β)) :=
    (MeasurableSet.singleton ()).prod hA
  have hg : Measurable fun νh : Measure (Unit × RingSpace d β) =>
      G (cycSlice () (νh.restrict ({()} ×ˢ A))) :=
    hG.comp ((measurable_cycSlice ()).comp (measurable_restrict_set hSA))
  have hmap : (Pr.map fun ω => liftU (N ω)) = (Pr.map N).map liftU :=
    (Measure.map_map measurable_liftU hN).symm
  rw [hmap, lintegral_map hg measurable_liftU]
  refine lintegral_congr fun ν => ?_
  rw [cycSlice_restrict_liftU]

end ElboimSly.Cyclic

end
