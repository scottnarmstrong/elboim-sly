/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Paths with finitely many jumps and a length

Paths (definition of `Path_V`, and the constancy lemma used in (a)).

`CPath V` is the set of pairs `(ℓ, p)` with `ℓ ∈ [0, ∞]` and `p : [0, ∞) → V` right-continuous,
with finitely many discontinuities in every bounded interval and constant on `[ℓ, ∞)` if
`ℓ < ∞`. A discontinuity is a time `s > 0` at which `p` is not left-continuous (when left limits
exist this is `p(s-) ≠ p(s)`; finiteness forces the left limits to exist). The σ-algebra is generated
by `(ℓ, p) ↦ ℓ` and `(ℓ, p) ↦ p(s)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

/-- The discontinuity times of `f : [0, ∞) → V`: times `s > 0` where `f` is not left-continuous. -/
def CDisc {V : Type*} (f : ℝ≥0 → V) : Set ℝ≥0 := {s | 0 < s ∧ ¬ ∀ᶠ u in 𝓝[<] s, f u = f s}

/-- Paths with finitely many jumps and a length. Paths. -/
structure CPath (V : Type*) where
  /-- The length `ℓ ∈ [0, ∞]`. -/
  len : ℝ≥0∞
  /-- The path. -/
  fn : ℝ≥0 → V
  rc : ∀ s, ∀ᶠ u in 𝓝[≥] s, fn u = fn s
  fin : ∀ T : ℝ≥0, (CDisc fn ∩ Iic T).Finite
  const : ∀ s s' : ℝ≥0, len ≤ (s : ℝ≥0∞) → len ≤ (s' : ℝ≥0∞) → fn s = fn s'

variable {V : Type*} [MeasurableSpace V]

instance : MeasurableSpace (CPath V) :=
  MeasurableSpace.comap (fun p : CPath V => (p.len, p.fn)) inferInstance

theorem CPath.measurable_len : Measurable (fun p : CPath V => p.len) :=
  measurable_fst.comp (comap_measurable (fun p : CPath V => (p.len, p.fn)))

theorem CPath.measurable_eval (s : ℝ≥0) : Measurable (fun p : CPath V => p.fn s) :=
  (measurable_pi_apply s).comp (measurable_snd.comp
    (comap_measurable (fun p : CPath V => (p.len, p.fn))))

theorem CPath.measurable_iff {α : Type*} [MeasurableSpace α] (g : α → CPath V) :
    Measurable g ↔ Measurable (fun a => (g a).len) ∧ ∀ s, Measurable (fun a => (g a).fn s) := by
  constructor
  · intro h
    exact ⟨CPath.measurable_len.comp h, fun s => (CPath.measurable_eval s).comp h⟩
  · rintro ⟨h1, h2⟩
    exact measurable_comap_iff.mpr (h1.prodMk (measurable_pi_iff.mpr h2))

end ElboimSly.Cyclic

end
