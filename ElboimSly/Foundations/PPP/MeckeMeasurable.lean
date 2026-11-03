/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.FactorialCount
public import Mathlib

/-!
# Measurability of the factorial measure on `Measure S`

Factorial moment measures (measurability of `ω ↦ 𝟙_{Ω_s} N(ω)^{(n)}(A)`).

`measurable_meckePhi`: `ν ↦ meckePhi D n ν` is measurable for the Giry `σ`-algebra.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

namespace SepPartSeq

variable (D : SepPartSeq S)

/-- The union of the first `k` level-`0` cells. -/
def tK (k : ℕ) : Set S := ⋃ i : Fin k, D.cell 0 i

theorem measurableSet_tK (k : ℕ) : MeasurableSet (D.tK k) :=
  MeasurableSet.iUnion fun i => D.measurableSet_cell 0 i

theorem monotone_tK : Monotone D.tK := by
  intro k k' h x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨⟨i, lt_of_lt_of_le i.2 h⟩, hi⟩

theorem iUnion_tK : ⋃ k, D.tK k = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨D.idx 0 x + 1, Set.mem_iUnion.2 ⟨⟨D.idx 0 x, Nat.lt_succ_self _⟩, rfl⟩⟩

variable {D}

theorem finite_atoms_tK {ν : Measure S} (hν : ν ∈ D.bSimple) (k : ℕ) :
    (atoms ν ∩ D.tK k).Finite := by
  have : atoms ν ∩ D.tK k = ⋃ i : Fin k, atoms ν ∩ D.cell 0 i := by
    ext x; simp [tK]
  rw [this]
  exact Set.finite_iUnion fun i => finite_atoms_inter hν i

/-- On simple measures, the mass of `T_k^n` under `ν^{(n)}` is a falling factorial. -/
theorem meckePhi_Ek {n : ℕ} {ν : Measure S} (hν : ν ∈ D.bSimple) (k : ℕ) :
    meckePhi D n ν (Set.pi Set.univ fun _ => D.tK k) =
      extDescFactorial (ν (D.tK k)) n := by
  have := D.measurableSingletonClass
  have hfin := finite_atoms_tK hν k
  have hνT : ν (D.tK k) = ((atoms ν ∩ D.tK k).ncard : ℝ≥0∞) := by
    rw [(structure_of_mem_bSimple hν).2.2.2 _ (D.measurableSet_tK k), Set.inter_comm,
      ← Set.Finite.cast_ncard_eq (Set.inter_comm _ _ ▸ hfin)]
    simp
  have hTm := MeasurableSet.univ_pi fun _ : Fin n => D.measurableSet_tK k
  rw [meckePhi_of_mem n hν, factorialMeasure, Measure.restrict_apply hTm, hνT,
    extDescFactorial_natCast]
  have e : (Set.pi Set.univ fun _ : Fin n => D.tK k) ∩
      {x | (∀ i, x i ∈ atoms ν) ∧ Function.Injective x} =
      {x : Fin n → S | (∀ i, x i ∈ hfin.toFinset) ∧ Function.Injective x} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨fun i => ⟨h2 i, h1 i⟩, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨fun i => (h1 i).2, fun i => (h1 i).1, h3⟩
  rw [e, Measure.count_apply (measurableSet_injTuples _ _)]
  have hf : {x : Fin n → S | (∀ i, x i ∈ hfin.toFinset) ∧ Function.Injective x}.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => (hfin.toFinset : Set S))
      (fun _ => hfin.toFinset.finite_toSet)).subset ?_
    exact fun x hx i _ => hx.1 i
  rw [← hf.cast_ncard_eq, ncard_injTuples, ← Set.ncard_eq_toFinset_card _ hfin]
  simp

/-- The exhausting boxes `T_k^n`. -/
def Ek (n k : ℕ) : Set (Fin n → S) := Set.pi Set.univ fun _ => D.tK k

theorem measurableSet_Ek (n k : ℕ) : MeasurableSet (D.Ek n k) :=
  MeasurableSet.univ_pi fun _ => D.measurableSet_tK k

theorem monotone_Ek (n : ℕ) : Monotone (D.Ek n) := fun _k _k' h _x hx i hi =>
  D.monotone_tK h (hx i hi)

theorem iUnion_Ek (n : ℕ) : ⋃ k, D.Ek n k = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Ek, Set.mem_pi, true_implies]
  have h : ∀ i, ∃ k, x i ∈ D.tK k := fun i => by
    have := D.iUnion_tK
    have hx : x i ∈ ⋃ k, D.tK k := by rw [this]; trivial
    exact Set.mem_iUnion.1 hx
  choose k hk using h
  exact ⟨Finset.univ.sup k, fun i => D.monotone_tK (Finset.le_sup (Finset.mem_univ i)) (hk i)⟩

theorem meckePhi_Ek_fun (n k : ℕ) (ν : Measure S) :
    meckePhi D n ν (D.Ek n k) =
      (D.bSimple).indicator (fun ν => extDescFactorial (ν (D.tK k)) n) ν := by
  by_cases h : ν ∈ D.bSimple
  · rw [Set.indicator_of_mem h, Ek, meckePhi_Ek h]
  · rw [Set.indicator_of_notMem h, meckePhi_of_not_mem n h]; rfl

theorem measurable_meckePhi_Ek (n k : ℕ) :
    Measurable fun ν : Measure S => meckePhi D n ν (D.Ek n k) := by
  simp_rw [meckePhi_Ek_fun]
  exact ((measurable_extDescFactorial n).comp
    (Measure.measurable_coe (D.measurableSet_tK k))).indicator D.measurableSet_bSimple

theorem meckePhi_Ek_lt_top {ν : Measure S} (hν : ν ∈ D.bSimple) (n k : ℕ) :
    meckePhi D n ν (D.Ek n k) < ∞ := by
  rw [Ek, meckePhi_Ek hν]
  have hfin := finite_atoms_tK hν k
  have : ν (D.tK k) = ((atoms ν ∩ D.tK k).ncard : ℝ≥0∞) := by
    have := D.measurableSingletonClass
    rw [(structure_of_mem_bSimple hν).2.2.2 _ (D.measurableSet_tK k), Set.inter_comm,
      ← Set.Finite.cast_ncard_eq (Set.inter_comm _ _ ▸ hfin)]
    simp
  rw [this, extDescFactorial_natCast]
  exact ENNReal.natCast_lt_top _

/-- The key measurability claim, localised to `T_k^n`. -/
theorem measurable_meckePhi_inter (n k : ℕ) {A : Set (Fin n → S)} (hA : MeasurableSet A) :
    Measurable fun ν : Measure S => meckePhi D n ν (A ∩ D.Ek n k) := by
  refine MeasurableSpace.induction_on_inter (m := (inferInstance : MeasurableSpace (Fin n → S)))
    (C := fun A _ => Measurable fun ν : Measure S => meckePhi D n ν (A ∩ D.Ek n k))
    (D.generateFrom_meckeC n).symm (D.isPiSystem_meckeC n) ?_ ?_ ?_ ?_ A hA
  · simp
  · intro t ht
    rcases ht with ⟨B, hB, hc, hd, rfl⟩ | ⟨htm, hsub⟩
    · have e : Set.pi Set.univ B ∩ D.Ek n k = Set.pi Set.univ (fun j => B j ∩ D.tK k) := by
        rw [Ek, Set.pi_inter_distrib]
      have hfun : ∀ ν : Measure S, meckePhi D n ν (Set.pi Set.univ B ∩ D.Ek n k) =
          (D.bSimple).indicator (fun ν => ∏ j, ν (B j ∩ D.tK k)) ν := by
        intro ν
        rw [e]
        by_cases h : ν ∈ D.bSimple
        · rw [Set.indicator_of_mem h]
          exact meckePhi_box h (fun j => (hB j).inter (D.measurableSet_tK k))
            (fun i j hij => (hd hij).mono Set.inter_subset_left Set.inter_subset_left)
        · rw [Set.indicator_of_notMem h, meckePhi_of_not_mem n h]; rfl
      simp_rw [hfun]
      refine Measurable.indicator ?_ D.measurableSet_bSimple
      exact Finset.measurable_prod _ fun j _ =>
        Measure.measurable_coe ((hB j).inter (D.measurableSet_tK k))
    · have hz : ∀ ν : Measure S, meckePhi D n ν (t ∩ D.Ek n k) = 0 := by
        intro ν
        by_cases h : ν ∈ D.bSimple
        · rw [meckePhi_of_mem n h]
          exact factorialMeasure_eq_zero_of_subset n ν (htm.inter (D.measurableSet_Ek n k))
            (fun x hx => hsub hx.1)
        · rw [meckePhi_of_not_mem n h]; rfl
      simp_rw [hz]
      exact measurable_const
  · intro t htm ih
    have hfun : ∀ ν : Measure S, meckePhi D n ν (tᶜ ∩ D.Ek n k) =
        meckePhi D n ν (D.Ek n k) - meckePhi D n ν (t ∩ D.Ek n k) := by
      intro ν
      by_cases h : ν ∈ D.bSimple
      · have e : tᶜ ∩ D.Ek n k = D.Ek n k \ (t ∩ D.Ek n k) := by
          ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
        rw [e, measure_sdiff Set.inter_subset_right
          (htm.inter (D.measurableSet_Ek n k)).nullMeasurableSet]
        exact ne_top_of_le_ne_top (meckePhi_Ek_lt_top h n k).ne
          (measure_mono Set.inter_subset_right)
      · rw [meckePhi_of_not_mem n h]; simp
    simp_rw [hfun]
    exact (measurable_meckePhi_Ek n k).sub ih
  · intro f hdisj hfm ih
    have hfun : ∀ ν : Measure S, meckePhi D n ν ((⋃ i, f i) ∩ D.Ek n k) =
        ∑' i, meckePhi D n ν (f i ∩ D.Ek n k) := by
      intro ν
      rw [Set.iUnion_inter]
      exact measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_left
        Set.inter_subset_left) fun i => (hfm i).inter (D.measurableSet_Ek n k)
    simp_rw [hfun]
    exact Measurable.tsum ih

/-- Measurability of the factorial measure on the space of measures. -/
theorem measurable_meckePhi (n : ℕ) :
    Measurable (meckePhi D n : Measure S → Measure (Fin n → S)) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hfun : ∀ ν : Measure S, meckePhi D n ν A = ⨆ k, meckePhi D n ν (A ∩ D.Ek n k) := by
    intro ν
    have hmono : Monotone fun k => A ∩ D.Ek n k := fun k k' h =>
      Set.inter_subset_inter_right _ (D.monotone_Ek n h)
    rw [← hmono.measure_iUnion, ← Set.inter_iUnion, D.iUnion_Ek n, Set.inter_univ]
  simp_rw [hfun]
  exact Measurable.iSup fun k => measurable_meckePhi_inter n k hA

end SepPartSeq

end ElboimSly
