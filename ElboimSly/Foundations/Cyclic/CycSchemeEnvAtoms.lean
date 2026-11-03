/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvProbe
public import ElboimSly.Foundations.Cyclic.CycRingMeasure
public import Mathlib

/-!
# The environment scheme (b): atoms of the environment in the explored region

The environment scheme (b) (i), (iv). For a good `ν` and a record with `EnvAt`, every
entry is an initial piece of an environment path, so `ν|_{R(ρ)} = RM(ρ)` (basic properties of world-lines (b),
`restrict_region_eq_rm`): in the region, the atoms of `ν` are the known rings
(`EnvAt.atom_iff_ring`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal
namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
variable {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)}

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem EnvAt.entries {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ) :
    ∀ e, ρ.IsEntry e → ∃ ℓ : ℝ≥0∞, e = (e.1, (envPath ν e.1).cut ℓ) := by
  rintro e ⟨j, hj⟩
  rw [h.rec_eq] at hj
  simp only [CycRec.nth] at hj
  split_ifs at hj with hjk
  · have hj' := Option.some.inj hj
    subst hj'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with hlt | heq
    · have : (⟨j, hjk⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hlt⟩ := rfl
      rw [this]
      simp only [CycRec.snoc, Fin.snoc_castSucc]
      rw [P.ideal_apply]
      exact ⟨_, rfl⟩
    · have : (⟨j, hjk⟩ : Fin (k + 1)) = Fin.last k := Fin.ext heq
      rw [this]
      simp only [CycRec.snoc, Fin.snoc_last]
      exact ⟨_, rfl⟩

theorem EnvAt.restrict_eq_rm (hν : CycGood ν) {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}
    (h : EnvAt P ν k r ρ) : ν.restrict (ρ.region β) = ρ.rm β :=
  restrict_region_eq_rm hν h.entries

theorem EnvAt.atom_iff_ring (hν : CycGood ν) {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}
    (h : EnvAt P ν k r ρ) {y : I × RingSpace d β} (hy : y ∈ ρ.region β) :
    1 ≤ ν {y} ↔ y ∈ ρ.ringSet β := by
  have := congrArg (fun m : Measure (I × RingSpace d β) => m {y}) (h.restrict_eq_rm hν)
  simp only [Measure.restrict_apply (measurableSet_singleton y), Set.singleton_inter_of_mem hy,
    CycRec.rm] at this
  by_cases hr : y ∈ ρ.ringSet β
  · rw [Set.singleton_inter_of_mem hr, Measure.count_singleton] at this
    rw [this]; simp [hr]
  · rw [Set.singleton_inter_of_notMem hr] at this
    simp only [measure_empty] at this
    rw [this]; simp [hr]

end CycSchemeEnv
end ElboimSly.Cyclic

end
