/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.GoodAsCircle
public import ElboimSly.Foundations.PPP.DissectingExamples
public import ElboimSly.Foundations.PPP.Factorial
public import ElboimSly.Frozen.Defs.IsRingPath
public import Mathlib

/-!
# The set `A_v` of the Mecke argument

Configurations are a.s. good (proof of (G3)).

For a vertex path `v` of length `n`, `pathBox v a p q ⊆ S_β^n` is the set of tuples
`((e₁, θ₁), …, (eₙ, θₙ))` with `eᵢ = {v_{i-1}, vᵢ}` and the circle points `θᵢ` forming a strictly
increasing tuple in `[p, q]`. It has `μ_β^{⊗ n}`-measure at most `(q-p)^n / n!`, and it contains the
point of any ring path along `v` in `[p, q]`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The tuples of edges along a vertex path. -/
def edgeTuples {n : ℕ} (v : Fin (n + 1) → Fin d → ℤ) : Set (Fin n → Edge d) :=
  {e | ∀ i, (e i).1 = s(v i.castSucc, v i.succ)}

/-- The set `A_v` of the Mecke argument. -/
def pathBox (β : ℝ) [Fact (0 < β)] {n : ℕ} (v : Fin (n + 1) → Fin d → ℤ) (a p q : ℝ) :
    Set (Fin n → RingSpace d β) :=
  {x | (fun i => (x i).1) ∈ edgeTuples v ∧ (fun i => (x i).2) ∈ circleSimplex β a n p q}

theorem measurableSet_edgeTuples {n : ℕ} (v : Fin (n + 1) → Fin d → ℤ) :
    MeasurableSet (edgeTuples v) := by
  have : edgeTuples v = Set.pi Set.univ (fun i : Fin n => {e : Edge d | e.1 = s(v i.castSucc, v i.succ)}) := by
    ext e; simp [edgeTuples]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => MeasurableSpace.measurableSet_top

theorem pi_count_edgeTuples_le {n : ℕ} (v : Fin (n + 1) → Fin d → ℤ) :
    Measure.pi (fun _ : Fin n => (Measure.count : Measure (Edge d))) (edgeTuples v) ≤ 1 := by
  by_cases hE : (edgeTuples v).Nonempty
  · obtain ⟨e0, he0⟩ := hE
    have hsub : edgeTuples v ⊆ Set.pi Set.univ (fun i => {e0 i}) := by
      intro e he i _
      exact Subtype.ext ((he i).trans (he0 i).symm)
    refine (measure_mono hsub).trans ?_
    rw [Measure.pi_pi]
    simp
  · rw [Set.not_nonempty_iff_eq_empty] at hE
    simp [hE]

theorem pi_ringIntensity_pathBox_le {n : ℕ} (v : Fin (n + 1) → Fin d → ℤ) (a p q : ℝ) :
    Measure.pi (fun _ : Fin n => ringIntensity d β) (pathBox β v a p q) ≤
      volume (orderedSimplex n p q) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow (Edge d) (AddCircle β) (Fin n)
    (fun _ => (Measure.count : Measure (Edge d))) (fun _ => (volume : Measure (AddCircle β)))
  have hset : pathBox β v a p q =
      (MeasurableEquiv.arrowProdEquivProdArrow (Edge d) (AddCircle β) (Fin n)) ⁻¹'
        (edgeTuples v ×ˢ circleSimplex β a n p q) := by
    ext x; rfl
  have hms : MeasurableSet (edgeTuples v ×ˢ circleSimplex β a n p q) :=
    (measurableSet_edgeTuples v).prod (measurableSet_circleSimplex a n p q)
  show Measure.pi (fun _ : Fin n => (Measure.count : Measure (Edge d)).prod (volume : Measure (AddCircle β))) _ ≤ _
  rw [hset, hmp.measure_preimage hms.nullMeasurableSet, Measure.prod_prod]
  calc _ ≤ 1 * volume (orderedSimplex n p q) :=
        mul_le_mul' (pi_count_edgeTuples_le v) (volume_circleSimplex_le a n p q)
    _ = _ := one_mul _

end ElboimSly.Interchange
