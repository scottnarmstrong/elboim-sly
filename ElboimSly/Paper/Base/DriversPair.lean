/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Iid
public import ElboimSly.Foundations.SRW.GoodAe
public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import Mathlib

/-!
# A pair of walks as a walk in dimension `2d`

Supports the pair of driving walks (i).

`dirMap d : Dir d × Fin 2 → Dir (d + d)` identifies `D × {1, 2}` with `D_{2d}`.  A point process
`Ñ` on `(D × Fin 2) × ℝ` is relabelled to `Ñ'` on `D_{2d} × ℝ`, and its two restrictions are
`N⁰, N¹`.  We show that, whenever the three measures `Ñ', N⁰, N¹` are good, the canonical walk of
`Ñ'` is the concatenation `(X⁰, X¹)` of the canonical walks of `N⁰, N¹`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW

variable {d : ℕ}

/-- Identification of `D × {1, 2}` with `D_{2d}`: the first copy goes to the first `d`
coordinates, the second to the last `d`. -/
def dirMap (d : ℕ) : Dir d × Fin 2 → Dir (d + d) := fun x =>
  (finSumFinEquiv (if x.2 = 0 then Sum.inl x.1.1 else Sum.inr x.1.1), x.1.2)

theorem dirMap_bijective (d : ℕ) : Function.Bijective (dirMap d) := by
  constructor
  · rintro ⟨⟨i, b⟩, j⟩ ⟨⟨i', b'⟩, j'⟩ h
    simp only [dirMap, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' := finSumFinEquiv.injective h1
    fin_cases j <;> fin_cases j' <;> simp at h1' ⊢ <;> simp_all
  · rintro ⟨u, b⟩
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective u
    rcases s with i | i
    · exact ⟨((i, b), 0), by simp [dirMap]⟩
    · exact ⟨((i, b), 1), by simp [dirMap]⟩

theorem castAdd_ne_natAdd (i k : Fin d) : Fin.castAdd d i ≠ Fin.natAdd d k := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := i.2
  omega

theorem vec_dirMap_zero (v : Dir d) :
    Dir.vec (dirMap d (v, 0)) = Fin.append (Dir.vec v) (0 : Fin d → ℤ) := by
  obtain ⟨i, b⟩ := v
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp only [dirMap, Dir.vec, Fin.append_left, ite_true, finSumFinEquiv_apply_left,
      Pi.single_apply, Fin.castAdd_inj]
  · have hne : Fin.natAdd d k ≠ Fin.castAdd d i := (castAdd_ne_natAdd i k).symm
    simp only [dirMap, Dir.vec, ite_true, finSumFinEquiv_apply_left, Pi.single_apply,
      Fin.append_right]
    rw [ite_eq_right hne]; rfl

theorem vec_dirMap_one (v : Dir d) :
    Dir.vec (dirMap d (v, 1)) = Fin.append (0 : Fin d → ℤ) (Dir.vec v) := by
  obtain ⟨i, b⟩ := v
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · have hne : Fin.castAdd d k ≠ Fin.natAdd d i := castAdd_ne_natAdd k i
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [dirMap, Dir.vec, ite_eq_right h10, finSumFinEquiv_apply_right, Pi.single_apply,
      Fin.append_left]
    rw [ite_eq_right hne]; rfl
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [dirMap, Dir.vec, ite_eq_right h10, finSumFinEquiv_apply_right, Pi.single_apply,
      Fin.append_right]
    simp only [Fin.natAdd_inj]

section Relabel

variable {D D' : Type*} [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
  [MeasurableSpace D'] [MeasurableSingletonClass D'] [Countable D']

theorem relabel_rect (ν : Measure (D × ℝ)) {S : Set D} (_hS : MeasurableSet S) (f : D → D')
    (B : Set D') (U : Set ℝ) (hU : MeasurableSet U) :
    relabel S f ν (B ×ˢ U) = ν ((f ⁻¹' B ∩ S) ×ˢ U) := by
  have hf : Measurable f := measurable_of_countable f
  have hB : MeasurableSet B := (B.to_countable).measurableSet
  unfold relabel
  rw [Measure.map_apply (hf.prodMap measurable_id) (hB.prod hU),
    Measure.restrict_apply ((hf.prodMap measurable_id) (hB.prod hU))]
  congr 1
  ext ⟨x, y⟩
  simp only [mem_inter_iff, mem_preimage, Prod.map_apply, mem_prod, id_eq, mem_univ, and_true]
  tauto

end Relabel

theorem cnt_relabel_pair (ν : Measure ((Dir d × Fin 2) × ℝ)) (v : Dir d) (j : Fin 2) (t : ℝ) :
    cnt (relabel univ (dirMap d) ν) (dirMap d (v, j)) t = cnt (relabel {x | x.2 = j} Prod.fst ν) v t
      := by
  unfold cnt
  rw [relabel_rect ν MeasurableSet.univ _ _ _ measurableSet_Ioc,
    relabel_rect ν (measurableSet_eq_fun measurable_snd measurable_const) _ _ _ measurableSet_Ioc]
  congr 2
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_univ, and_true, mem_ofPred_eq]
  constructor
  · intro h
    have := (dirMap_bijective d).1 h
    subst this
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have : x = (v, j) := Prod.ext h1 h2
    rw [this]

theorem tot_relabel_pair (ν : Measure ((Dir d × Fin 2) × ℝ)) (U : Set ℝ) (hU : MeasurableSet U) :
    tot (relabel univ (dirMap d) ν) U =
      tot (relabel {x | x.2 = 0} Prod.fst ν) U + tot (relabel {x | x.2 = 1} Prod.fst ν) U := by
  have hm : ∀ j : Fin 2, MeasurableSet {x : Dir d × Fin 2 | x.2 = j} := fun j =>
    measurableSet_eq_fun measurable_snd measurable_const
  unfold tot
  rw [relabel_rect ν MeasurableSet.univ _ _ _ hU, relabel_rect ν (hm 0) _ _ _ hU,
    relabel_rect ν (hm 1) _ _ _ hU]
  simp only [preimage_univ, univ_inter]
  rw [← measure_union _ ((hm 1).prod hU)]
  · congr 1
    ext ⟨x, y⟩
    simp only [mem_prod, mem_univ, true_and, mem_union, mem_ofPred_eq]
    have h2 : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    constructor
    · intro hy
      rcases h2 x.2 with e | e
      · exact Or.inl ⟨e, hy⟩
      · exact Or.inr ⟨e, hy⟩
    · rintro (⟨_, hy⟩ | ⟨_, hy⟩) <;> exact hy
  · refine Set.disjoint_left.2 fun p hp hq => ?_
    simp only [mem_prod, mem_ofPred_eq] at hp hq
    have := hp.1.symm.trans hq.1
    exact absurd this (by decide)

theorem walk_relabel_pair (ν : Measure ((Dir d × Fin 2) × ℝ))
    (h : relabel univ (dirMap d) ν ∈ goodSet (d + d))
    (h0 : relabel {x | x.2 = 0} Prod.fst ν ∈ goodSet d)
    (h1 : relabel {x | x.2 = 1} Prod.fst ν ∈ goodSet d) (t : ℝ) :
    walk (d + d) (relabel univ (dirMap d) ν) t =
      Fin.append (walk d (relabel {x | x.2 = 0} Prod.fst ν) t)
        (walk d (relabel {x | x.2 = 1} Prod.fst ν) t) := by
  classical
  unfold walk
  rw [ite_eq_left h, ite_eq_left h0, ite_eq_left h1]
  rw [← (Equiv.ofBijective (dirMap d) (dirMap_bijective d)).sum_comp]
  simp only [Equiv.ofBijective_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp only [cnt_relabel_pair, vec_dirMap_zero, vec_dirMap_one]
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Fin.append_left, 
      Pi.zero_apply, smul_zero, add_zero]
  · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Fin.append_right,
      Pi.zero_apply, smul_zero, zero_add]

end ElboimSly.Paper
