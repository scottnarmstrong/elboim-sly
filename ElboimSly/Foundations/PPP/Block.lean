/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.MixedBinomial
public import Mathlib

/-!
# One block of the existence construction

Existence (the factor `Po(λ_k) ⊗ ⨂_i ν_k` and its mixed binomial process).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

/-- The law `Po(λ) ⊗ ⨂_{i∈ℕ} ν` of one block `(K, (Y_i)_i)`. -/
noncomputable def blockMeasure (ν : Measure S) [IsProbabilityMeasure ν] (lam : ℝ≥0) :
    Measure (ℕ × (ℕ → S)) :=
  (poissonMeasure lam).prod (Measure.infinitePi fun _ : ℕ => ν)

section

variable (ν : Measure S) [IsProbabilityMeasure ν] (lam : ℝ≥0)

instance : IsProbabilityMeasure (blockMeasure ν lam) := by
  unfold blockMeasure; infer_instance

/-- The mixed binomial process on a block. -/
noncomputable def blockProc (p : ℕ × (ℕ → S)) : Measure S :=
  mixedBinomial (fun p : ℕ × (ℕ → S) => p.1) (fun i p => p.2 i) p

theorem measurable_blockProc : Measurable (blockProc (S := S)) :=
  measurable_mixedBinomial measurable_fst fun i => (measurable_pi_apply i).comp measurable_snd

theorem map_fst_blockMeasure : (blockMeasure ν lam).map Prod.fst = poissonMeasure lam := by
  simp [blockMeasure]

theorem map_snd_blockMeasure :
    (blockMeasure ν lam).map Prod.snd = Measure.infinitePi fun _ : ℕ => ν := by
  simp [blockMeasure]

/-- Existence (proof): the block process is `PPP(λ ν)`. -/
theorem isPoissonPointProcess_blockProc :
    IsPoissonPointProcess (blockProc (S := S)) ((lam : ℝ≥0∞) • ν) (blockMeasure ν lam) := by
  have hYm : ∀ i : ℕ, Measurable fun p : ℕ × (ℕ → S) => p.2 i :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  have hYlaw : ∀ i : ℕ, (blockMeasure ν lam).map (fun p : ℕ × (ℕ → S) => p.2 i) = ν := by
    intro i
    have : (fun p : ℕ × (ℕ → S) => p.2 i) = (fun x : ℕ → S => x i) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply i) measurable_snd, map_snd_blockMeasure,
      Measure.infinitePi_map_eval]
  have hiid : iIndepFun (fun (i : ℕ) (p : ℕ × (ℕ → S)) => p.2 i) (blockMeasure ν lam) := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map hYm]
    simp_rw [hYlaw]
    exact map_snd_blockMeasure ν lam
  have hind : IndepFun Prod.fst (fun (p : ℕ × (ℕ → S)) i => p.2 i) (blockMeasure ν lam) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      (Measurable.of_eval hYm).aemeasurable]
    have e : (fun p : ℕ × (ℕ → S) => (p.1, fun i => p.2 i)) = id := rfl
    have e2 : (fun (p : ℕ × (ℕ → S)) i => p.2 i) = Prod.snd := rfl
    simp only [e]
    rw [Measure.map_id, map_fst_blockMeasure, map_snd_blockMeasure]
    rfl
  exact isPoissonPointProcess_mixedBinomial measurable_fst hYm (map_fst_blockMeasure ν lam)
    hiid hYlaw hind

end

end ElboimSly
