/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseOverride
public import Mathlib

/-!
# Laws of the coordinates of the base coupling

ES22 (8.3): base coupling with precision n^10 (the paragraphs "The walk" and "The Brownian motion").

* `law_flatten`: a product of `|α|` copies of a measure whose image is a product of `|β|` copies
  of `π` is, after flattening the coordinates, the product of `|α × β|` copies of `π`.
* `law_pairDiff`: for an `N(0,1)`-array indexed by `(Fin d × Bool) × Fin N`, the array
  `(G (i,true) m - G (i,false) m) / √2` is again an `N(0,1)`-array.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

section Flatten

variable {α β E Y : Type*} [Fintype α] [Fintype β] [MeasurableSpace E] [MeasurableSpace Y]

/-- Flattening of a nested product of copies. -/
theorem law_flatten (ρ : Measure E) [IsProbabilityMeasure ρ] {f : E → β → Y} (hf : Measurable f)
    (π : Measure Y) [IsProbabilityMeasure π] (hlaw : ρ.map f = Measure.pi fun _ : β => π) :
    (Measure.pi fun _ : α => ρ).map (fun a (p : α × β) => f (a p.1) p.2) =
      Measure.pi fun _ : α × β => π := by
  rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  have h1 : (fun (a : α → E) (p : α × β) => f (a p.1) p.2) =
      (MeasurableEquiv.curry α β Y).symm ∘ (fun (a : α → E) i => f (a i)) := by
    funext a p; rfl
  have hm : Measurable (fun (a : α → E) (i : α) => f (a i)) :=
    measurable_pi_iff.2 fun i => hf.comp (measurable_pi_apply i)
  rw [h1, ← Measure.map_map (MeasurableEquiv.curry α β Y).symm.measurable hm]
  have h2 := Measure.infinitePi_map_pi (μ := fun _ : α => ρ) (f := fun _ => f)
    (fun _ => hf)
  rw [h2]
  have h3 : (fun _ : α => ρ.map f) = fun _ => Measure.infinitePi fun _ : β => π := by
    funext _; rw [hlaw, Measure.infinitePi_eq_pi]
  rw [h3]
  exact Measure.infinitePi_map_curry_symm (fun (_ : α) (_ : β) => π)

end Flatten

section PairDiff

/-- The law of `(a - b)/√2` for independent standard Gaussians. -/
theorem law_boolDiff :
    (Measure.infinitePi fun _ : Bool => gaussianReal 0 1).map
        (fun f : Bool → ℝ => (f true - f false) / √2) = gaussianReal 0 1 := by
  set Pb := Measure.infinitePi fun _ : Bool => gaussianReal 0 1 with hPb
  have hind : iIndepFun (fun (i : Bool) (f : Bool → ℝ) => f i) Pb :=
    iIndepFun_infinitePi (P := fun _ : Bool => gaussianReal 0 1) (X := fun _ x => x)
      (fun _ => measurable_id)
  have hlaw : ∀ i : Bool, HasLaw (fun f : Bool → ℝ => f i) (gaussianReal 0 1) Pb := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, by
      rw [hPb, Measure.infinitePi_map_eval]⟩
  have hI : IndepFun (fun f : Bool → ℝ => f true) (fun f : Bool → ℝ => f false) Pb :=
    hind.indepFun (by simp)
  have h1 := gaussianReal_const_mul (hlaw true) (1 / √2)
  have h2 := gaussianReal_const_mul (hlaw false) (-1 / √2)
  have hI' : IndepFun (fun f : Bool → ℝ => 1 / √2 * f true)
      (fun f : Bool → ℝ => -1 / √2 * f false) Pb :=
    hI.comp (measurable_const_mul _) (measurable_const_mul _)
  have h3 := gaussianReal_add_gaussianReal_of_indepFun hI' h1 h2
  have hv : (NNReal.mk ((1 / √2) ^ 2) (sq_nonneg _) * 1 +
      NNReal.mk ((-1 / √2) ^ 2) (sq_nonneg _) * 1 : ℝ≥0) = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_mk, NNReal.coe_one, mul_one]
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hv, mul_zero, mul_zero, add_zero] at h3
  have hfun : (fun f : Bool → ℝ => (f true - f false) / √2) =
      (fun f : Bool → ℝ => 1 / √2 * f true) + (fun f : Bool → ℝ => -1 / √2 * f false) := by
    funext f; simp only [Pi.add_apply]; ring
  rw [hfun]
  exact h3

variable {d N : ℕ}

/-- Pair differences of an `N(0,1)`-array. -/
theorem law_pairDiff :
    (Measure.pi fun _ : (Fin d × Bool) × Fin N => gaussianReal 0 1).map
        (fun (G : (Fin d × Bool) × Fin N → ℝ) (m : Fin N) (i : Fin d) =>
          (G ((i, true), m) - G ((i, false), m)) / √2) =
      Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  set h : (Fin N × Fin d) × Bool → (Fin d × Bool) × Fin N := fun p => ((p.1.2, p.2), p.1.1) with hh
  have hinj : Function.Injective h := by
    rintro ⟨⟨m, i⟩, b⟩ ⟨⟨m', i'⟩, b'⟩ e
    simp only [hh, Prod.mk.injEq] at e
    obtain ⟨⟨e1, e2⟩, e3⟩ := e
    subst e1 e2 e3; rfl
  rw [← Measure.infinitePi_eq_pi]
  have s1 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : (Fin d × Bool) × Fin N => gaussianReal 0 1) hinj
  -- the nested form
  have s2 : (Measure.infinitePi fun _ : (Fin N × Fin d) × Bool => gaussianReal 0 1).map
      (MeasurableEquiv.curry (Fin N × Fin d) Bool ℝ) =
      Measure.infinitePi fun _ : Fin N × Fin d => Measure.infinitePi fun _ : Bool =>
        gaussianReal 0 1 :=
    Measure.infinitePi_map_curry (fun (_ : Fin N × Fin d) (_ : Bool) => gaussianReal 0 1)
  have s3 : (Measure.infinitePi fun _ : Fin N × Fin d => Measure.infinitePi fun _ : Bool =>
        gaussianReal 0 1).map (fun (g : Fin N × Fin d → Bool → ℝ) p => (g p true - g p false) / √2)
      = Measure.infinitePi fun _ : Fin N × Fin d => gaussianReal 0 1 := by
    have := Measure.infinitePi_map_pi
      (μ := fun _ : Fin N × Fin d => Measure.infinitePi fun _ : Bool => gaussianReal 0 1)
      (f := fun _ (f : Bool → ℝ) => (f true - f false) / √2)
      (fun _ => (by fun_prop))
    rw [this]
    simp_rw [law_boolDiff]
  have s4 : (Measure.infinitePi fun _ : Fin N × Fin d => gaussianReal 0 1).map
      (MeasurableEquiv.curry (Fin N) (Fin d) ℝ) =
      Measure.infinitePi fun _ : Fin N => Measure.infinitePi fun _ : Fin d => gaussianReal 0 1 :=
    Measure.infinitePi_map_curry (fun (_ : Fin N) (_ : Fin d) => gaussianReal 0 1)
  have hcomp : (fun (G : (Fin d × Bool) × Fin N → ℝ) (m : Fin N) (i : Fin d) =>
          (G ((i, true), m) - G ((i, false), m)) / √2) =
      (MeasurableEquiv.curry (Fin N) (Fin d) ℝ) ∘
      (fun (g : Fin N × Fin d → Bool → ℝ) p => (g p true - g p false) / √2) ∘
      (MeasurableEquiv.curry (Fin N × Fin d) Bool ℝ) ∘ (fun (G : (Fin d × Bool) × Fin N → ℝ)
        p => G (h p)) := by
    funext G m i; rfl
  have hm1 : Measurable fun (G : (Fin d × Bool) × Fin N → ℝ) (p : (Fin N × Fin d) × Bool) => G (h p) :=
    measurable_pi_iff.2 fun p => measurable_pi_apply _
  have hm3 : Measurable fun (g : Fin N × Fin d → Bool → ℝ) (p : Fin N × Fin d) =>
      (g p true - g p false) / √2 := by fun_prop
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable
    (hm3.comp ((MeasurableEquiv.curry _ _ _).measurable.comp hm1)),
    ← Measure.map_map hm3 ((MeasurableEquiv.curry _ _ _).measurable.comp hm1),
    ← Measure.map_map (MeasurableEquiv.curry _ _ _).measurable hm1, s1.trans (by rfl)]
  rw [s2, s3, s4, Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi]

end PairDiff

end StrongApprox
end ElboimSly
