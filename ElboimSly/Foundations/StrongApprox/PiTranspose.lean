/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Transposing iterated product measures

Auxiliary measure theory for laws in the coupling (Part II).

`(⨂_k ⨂_i ν k i).map transpose = ⨂_i ⨂_k ν k i` for finite index types.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.StrongApprox

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]

/-- Transposing an iterated product measure. -/
theorem pi_pi_transpose (ν : ι → κ → Measure E) [∀ a b, IsProbabilityMeasure (ν a b)] :
    (Measure.pi fun a : ι => Measure.pi fun b : κ => ν a b).map
        (fun (v : ι → κ → E) (b : κ) (a : ι) => v a b) =
      Measure.pi fun b : κ => Measure.pi fun a : ι => ν a b := by
  classical
  have h1 : (Measure.pi fun p : ι × κ => ν p.1 p.2).map (MeasurableEquiv.curry ι κ E) =
      Measure.pi fun a : ι => Measure.pi fun b : κ => ν a b := by
    have := Measure.infinitePi_map_curry (X := E) ν
    simpa [Measure.infinitePi_eq_pi] using this
  have h2 : (Measure.pi fun p : κ × ι => ν p.2 p.1).map (MeasurableEquiv.curry κ ι E) =
      Measure.pi fun b : κ => Measure.pi fun a : ι => ν a b := by
    have := Measure.infinitePi_map_curry (X := E) (fun b a => ν a b)
    simpa [Measure.infinitePi_eq_pi] using this
  have h3 : (Measure.pi fun p : ι × κ => ν p.1 p.2).map
      (MeasurableEquiv.piCongrLeft (fun _ => E) (Equiv.prodComm ι κ)) =
      Measure.pi fun p : κ × ι => ν p.2 p.1 :=
    Measure.pi_map_piCongrLeft (Equiv.prodComm ι κ) (fun p : κ × ι => ν p.2 p.1)
  rw [← h1, ← h2, ← h3]
  have hm1 : Measurable (MeasurableEquiv.curry ι κ E) := (MeasurableEquiv.curry ι κ E).measurable
  rw [Measure.map_map (by fun_prop) hm1, Measure.map_map (MeasurableEquiv.curry κ ι E).measurable
    (MeasurableEquiv.piCongrLeft (fun _ => E) (Equiv.prodComm ι κ)).measurable]
  congr 1

end ElboimSly.StrongApprox
