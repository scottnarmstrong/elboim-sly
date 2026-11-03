/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.OneStep
import Mathlib

/-!
# Exploration schemes

Exploration scheme; the exploration of N; Measurability for schemes (a), (b).

`Hist U S k = U × (Fin k → 𝕆)` is the space `ℋ_k` of histories. An exploration scheme chooses, at
each step `k`, a parametrized raw probe `(R_k, h_k)` on `ℋ_k`. The explored region `𝒵_k(η)` and the
masked probe `R̃_k` are defined by recursion.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] (U : Type*) [MeasurableSpace U]

/-- The history space `ℋ_k = 𝕌 × 𝕆^k` (Exploration scheme; the exploration of N). -/
abbrev Hist (S : Type*) [MeasurableSpace S] (k : ℕ) : Type _ := U × (Fin k → Outcome S)

variable {U}

namespace Hist

/-- The history extended by one outcome (`Fin.snoc`). -/
def snoc {k : ℕ} (η : Hist U S k) (o : Outcome S) : Hist U S (k + 1) :=
  (η.1, Fin.snoc (α := fun _ => Outcome S) η.2 o)

/-- Forget the last outcome. -/
def init {k : ℕ} (η : Hist U S (k + 1)) : Hist U S k := (η.1, Fin.init η.2)

/-- The last outcome. -/
def last {k : ℕ} (η : Hist U S (k + 1)) : Outcome S := η.2 (Fin.last k)

theorem measurable_snoc (k : ℕ) :
    Measurable fun q : Hist U S k × Outcome S => q.1.snoc q.2 := by
  refine measurable_fst.comp measurable_fst |>.prodMk ?_
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

theorem measurable_init (k : ℕ) : Measurable fun η : Hist U S (k + 1) => η.init :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
    (measurable_pi_apply (Fin.castSucc i)).comp measurable_snd)

theorem measurable_last (k : ℕ) : Measurable fun η : Hist U S (k + 1) => η.last :=
  (measurable_pi_apply (Fin.last k)).comp measurable_snd

omit [MeasurableSpace U] in
@[simp] theorem init_snoc {k : ℕ} (η : Hist U S k) (o : Outcome S) : (η.snoc o).init = η := by
  simp [snoc, init]

omit [MeasurableSpace U] in
@[simp] theorem last_snoc {k : ℕ} (η : Hist U S k) (o : Outcome S) : (η.snoc o).last = o := by
  simp [snoc, last]

end Hist

/-- Exploration scheme; the exploration of N: an exploration scheme for `(S, μ)` with auxiliary space `U`. -/
structure ExplScheme (μ : Measure S) (U : Type*) [MeasurableSpace U] where
  /-- The raw entrance time of step `k`. -/
  R : (k : ℕ) → Hist U S k → S → ℝ≥0∞
  /-- The horizon of step `k`. -/
  h : (k : ℕ) → Hist U S k → ℝ≥0
  measurable_R : ∀ k, Measurable fun p : Hist U S k × S => R k p.1 p.2
  measurable_h : ∀ k, Measurable (h k)
  isProbe : ∀ k η, IsProbe μ (R k η) (h k η)

variable {μ : Measure S} (sch : ExplScheme μ U)

namespace ExplScheme

/-- The explored regions `𝒵_k(η)`. -/
def Z : (k : ℕ) → Hist U S k → Set S
  | 0, _ => ∅
  | k + 1, η => Z k η.init ∪ {x | x ∉ Z k η.init ∧
      sch.R k η.init x ≤ min η.last.1 (sch.h k η.init)}

open scoped Classical in
/-- The masked probe `R̃_k`. -/
noncomputable def Rt (k : ℕ) (η : Hist U S k) (x : S) : ℝ≥0∞ :=
  if x ∈ sch.Z k η then ∞ else sch.R k η x

theorem Rt_of_notMem {k : ℕ} {η : Hist U S k} {x : S} (hx : x ∉ sch.Z k η) :
    sch.Rt k η x = sch.R k η x := by
  classical
  simp [Rt, hx]

theorem Rt_of_mem {k : ℕ} {η : Hist U S k} {x : S} (hx : x ∈ sch.Z k η) :
    sch.Rt k η x = ∞ := by
  classical
  simp [Rt, hx]

theorem measurableSet_Z (k : ℕ) : MeasurableSet {p : Hist U S k × S | p.2 ∈ sch.Z k p.1} := by
  induction k with
  | zero => simp [Z]
  | succ k ih =>
    have h1 : MeasurableSet {p : Hist U S (k + 1) × S | p.2 ∈ sch.Z k p.1.init} :=
      ih.preimage ((Hist.measurable_init k).comp measurable_fst |>.prodMk measurable_snd)
    have h2 : MeasurableSet {p : Hist U S (k + 1) × S |
        sch.R k p.1.init p.2 ≤ min p.1.last.1 (sch.h k p.1.init)} := by
      refine measurableSet_le ?_ ?_
      · exact (sch.measurable_R k).comp
          ((Hist.measurable_init k).comp measurable_fst |>.prodMk measurable_snd)
      · exact (measurable_fst.comp ((Hist.measurable_last k).comp measurable_fst)).min
          (measurable_coe_nnreal_ennreal.comp ((sch.measurable_h k).comp
            ((Hist.measurable_init k).comp measurable_fst)))
    convert h1.union (h1.compl.inter h2) using 1
    ext p
    simp only [Z, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]

theorem measurable_Rt (k : ℕ) : Measurable fun p : Hist U S k × S => sch.Rt k p.1 p.2 := by
  classical
  have : (fun p : Hist U S k × S => sch.Rt k p.1 p.2) = fun p =>
      if p.2 ∈ sch.Z k p.1 then ∞ else sch.R k p.1 p.2 := rfl
  rw [this]
  exact Measurable.ite (sch.measurableSet_Z k) measurable_const (sch.measurable_R k)

/-- Measurability for schemes (a): `(R̃_k, h_k)` is again a parametrized probe. -/
theorem isProbe_Rt (k : ℕ) (η : Hist U S k) : IsProbe μ (sch.Rt k η) (sch.h k η) := by
  classical
  have hP := sch.isProbe k η
  refine ⟨(sch.measurable_Rt k).comp (measurable_const.prodMk measurable_id), ?_, ?_⟩
  · refine lt_of_le_of_lt (measure_mono fun x hx => ?_) hP.mass_lt_top
    by_cases hxZ : x ∈ sch.Z k η
    · rw [probeRegion, Set.mem_ofPred_eq, sch.Rt_of_mem hxZ] at hx
      exact absurd hx (by simp)
    · rw [probeRegion, Set.mem_ofPred_eq, sch.Rt_of_notMem hxZ] at hx
      exact hx
  · intro r hr
    refine measure_mono_null (fun x hx => ?_) (hP.measure_eq_zero r hr)
    by_cases hxZ : x ∈ sch.Z k η
    · rw [Set.mem_ofPred_eq, sch.Rt_of_mem hxZ] at hx
      exact absurd hx.symm (by simp)
    · rw [Set.mem_ofPred_eq, sch.Rt_of_notMem hxZ] at hx
      exact hx

/-- Exploration scheme; the exploration of N (X): each step probes only unexplored space. -/
theorem disjoint_region_Z (k : ℕ) (η : Hist U S k) :
    Disjoint (probeRegion (sch.Rt k η) (sch.h k η)) (sch.Z k η) := by
  rw [Set.disjoint_left]
  intro x hx hxZ
  rw [probeRegion, Set.mem_ofPred_eq, sch.Rt_of_mem hxZ] at hx
  exact absurd hx (by simp)

end ExplScheme

end ElboimSly
