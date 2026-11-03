/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Operations
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import Mathlib

/-!
# Invariance of the ring intensity

Invariance on E×mathbbT_β.

For countable `E`, a bijection `g` of `E` and a transformation `T` of the circle preserving
Haar measure, `(g, T)` preserves `# ⊗ Leb_β`. Applied to translation and reflection.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

theorem count_map_equiv {E : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
    (g : E ≃ E) : (Measure.count : Measure E).map g = Measure.count := by
  have hg : Measurable g := measurable_of_countable g
  refine Measure.ext_of_singleton ?_ |> fun h => h
  intro e
  rw [Measure.map_apply hg (measurableSet_singleton e)]
  have : (g ⁻¹' {e}) = {g.symm e} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff]; rw [eq_comm, Equiv.eq_symm_apply, eq_comm]
  rw [this, Measure.count_singleton, Measure.count_singleton]

/-- `(g × T)_* (# ⊗ λ) = # ⊗ λ` when `g` is a bijection and `T_* λ = λ`. -/
theorem count_prod_map_invariant {E F : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [MeasurableSpace F] (lam : Measure F) [SFinite lam] (g : E ≃ E)
    {T : F → F} (hT : Measurable T) (hlam : lam.map T = lam) :
    ((Measure.count : Measure E).prod lam).map (Prod.map g T) = (Measure.count : Measure E).prod lam := by
  have hg : Measurable g := measurable_of_countable g
  rw [← Measure.map_prod_map _ _ hg hT, count_map_equiv, hlam]

section Circle

variable (β : ℝ) [Fact (0 < β)]

theorem map_add_const_volume (r : AddCircle β) :
    (volume : Measure (AddCircle β)).map (· + r) = volume :=
  map_add_right_eq_self _ r

theorem map_neg_volume : (volume : Measure (AddCircle β)).map (fun x => -x) = volume :=
  Measure.map_neg_eq_self _

end Circle

section Ring

variable (d : ℕ) (β : ℝ) [Fact (0 < β)]

/-- Invariance on E×mathbbT_β: `(g, +r)` preserves `ringIntensity`. -/
theorem map_ringIntensity_translate (g : Edge d ≃ Edge d) (r : AddCircle β) :
    (ringIntensity d β).map (Prod.map g (· + r)) = ringIntensity d β :=
  count_prod_map_invariant _ g (measurable_id.add_const r) (map_add_const_volume β r)

/-- Invariance on E×mathbbT_β: `(g, -·)` preserves `ringIntensity`. -/
theorem map_ringIntensity_neg (g : Edge d ≃ Edge d) :
    (ringIntensity d β).map (Prod.map g (fun x => -x)) = ringIntensity d β :=
  count_prod_map_invariant _ g measurable_neg (map_neg_volume β)

end Ring

namespace IsPoissonPointProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (d : ℕ) (β : ℝ) [Fact (0 < β)]

end IsPoissonPointProcess

end ElboimSly
