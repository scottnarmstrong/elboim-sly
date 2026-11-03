/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenAe
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvDef
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvEdge
public import ElboimSly.Foundations.SRW.Jumps
public import Mathlib

/-!
# The driving scheme (c): jumps of the canonical walks are atoms of the driving process

The driving scheme (c), "On `Ω'_1`, `X_j` jumps at `y > 0` by `v` iff `(j, v, y)` is an
atom of `N'`".

For a point process `Ñ` on `(𝒟 × J) × ℝ`, `srwPath Ñ j` is the canonical walk of the `j`-th
sub-process (independent families) as an element of `CycPath d`. On the good event of the `j`-th
sub-process the jump of `srwPath Ñ j` at `y > 0` is the sum of the directions of the atoms of `Ñ` at
`((·, j), y)` (`srw_jump_formula`); there is at most one such atom (good event and path properties).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ} {J : Type} [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]

/-- The canonical walk of the `j`-th sub-process of `Ñ`, as a `CycPath`. -/
noncomputable def srwPath (Ñ : Measure ((Dir d × J) × ℝ)) (j : J) : CycPath d :=
  drivingCycPath (walkPath_isDriving
    (relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ))

omit [MeasurableSingletonClass J] [Countable J] in
theorem srwPath_fn (Ñ : Measure ((Dir d × J) × ℝ)) (j : J) (s : ℝ≥0) :
    (srwPath Ñ j).1.fn s = walk d (relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ) (s : ℝ) := rfl

theorem relabel_singleton (Ñ : Measure ((Dir d × J) × ℝ)) (j : J) (v : Dir d) (y : ℝ) :
    relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ (({v} : Set (Dir d)) ×ˢ {y}) =
      Ñ ({(v, j)} ×ˢ {y}) := by
  unfold relabel
  rw [Measure.map_apply (measurable_of_countable Prod.fst |>.prodMap measurable_id)
    ((measurableSet_singleton v).prod (measurableSet_singleton y)),
    Measure.restrict_apply ((measurable_of_countable Prod.fst |>.prodMap measurable_id)
      ((measurableSet_singleton v).prod (measurableSet_singleton y)))]
  congr 1
  ext ⟨⟨v', j'⟩, y'⟩
  simp only [mem_inter_iff, mem_preimage, Prod.map_apply, id_eq, mem_prod, mem_singleton_iff,
    mem_ofPred_eq, mem_univ, and_true, Prod.mk.injEq]
  tauto

variable {Ñ : Measure ((Dir d × J) × ℝ)} {j : J}

theorem srw_left_eq (hν : relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d) {y : ℝ≥0}
    (hy : 0 < y) :
    ∃ δ : ℝ, 0 < δ ∧ δ < y ∧
      (srwPath Ñ j).1.left y = walk d (relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ) (y - δ) ∧
      (srwPath Ñ j).1.fn y - (srwPath Ñ j).1.left y =
        ∑ v : Dir d, ((natOf (Ñ ({(v, j)} ×ˢ {(y : ℝ)})) : ℕ) : ℤ) • v.vec := by
  set ν := relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ with hνdef
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  obtain ⟨δ, hδ, hδt, hconst, hjump⟩ := left_jump_formula hν hy'
  have hl : (srwPath Ñ j).1.left y = walk d ν ((y : ℝ) - δ) := by
    have hl : (srwPath Ñ j).1.left y = leftVal (srwPath Ñ j).1.fn y :=
      CPath.left_eq_leftVal_of_pos _ hy
    rw [hl]
    refine leftVal_eq_of_eventually hy ?_
    have hlt : ((y : ℝ) - δ).toNNReal < y := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by linarith)]; linarith
    filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
    have hu0 : (y : ℝ) - δ ≤ u := by
      have := hu.1
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by linarith)] at this
      exact this.le
    have hu1 : (u : ℝ) < y := by exact_mod_cast hu.2
    show walk d ν (u : ℝ) = _
    rw [hconst _ ⟨hu0, hu1⟩]
  refine ⟨δ, hδ, hδt, hl, ?_⟩
  rw [hl, srwPath_fn, hjump]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [relabel_singleton]

theorem natOf_sum_le_one {ν : Measure (Dir d × ℝ)} (hν : ν ∈ goodSet d) {t : ℝ} (ht : 0 < t) :
    ∑ v : Dir d, natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) ≤ 1 := by
  have h1 : ((∑ v : Dir d, natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) : ℕ) : ℝ≥0∞) ≤ 1 := by
    push_cast
    have : ∀ v : Dir d, ((natOf (ν (({v} : Set (Dir d)) ×ˢ {t})) : ℕ) : ℝ≥0∞) =
        ν (({v} : Set (Dir d)) ×ˢ {t}) := fun v =>
      (IsNat.natCast_natOf (by
        have := good_singleton hν v ht
        exact this))
    simp only [this]
    rw [← tot_eq_sum ν _ (measurableSet_singleton t)]
    exact good_tot_singleton_le_one hν ht
  exact_mod_cast h1

/-- A jump of the canonical walk at `y > 0`: it is the direction of the unique atom at time `y`. -/
theorem srw_jump_dir (hν : relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d) {y : ℝ≥0}
    (hy : 0 < y) {v : Dir d} (hat : Ñ ({(v, j)} ×ˢ {(y : ℝ)}) ≠ 0) :
    (srwPath Ñ j).1.fn y - (srwPath Ñ j).1.left y = v.vec := by
  classical
  obtain ⟨δ, -, -, -, hjump⟩ := srw_left_eq hν hy
  rw [hjump]
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hsum := natOf_sum_le_one hν hy'
  set m : Dir d → ℕ := fun w => natOf (relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ
    (({w} : Set (Dir d)) ×ˢ {(y : ℝ)})) with hm
  have hmeq : ∀ w, natOf (Ñ ({(w, j)} ×ˢ {(y : ℝ)})) = m w := fun w => by
    simp only [hm, relabel_singleton]
  have hmv : m v ≠ 0 := by
    intro h0
    apply hat
    have := IsNat.natCast_natOf (good_singleton hν v hy')
    rw [relabel_singleton] at this
    rw [← this]
    have h0' : natOf (Ñ ({(v, j)} ×ˢ {(y : ℝ)})) = 0 := by rw [hmeq]; exact h0
    rw [h0']; simp
  have hsum' : ∑ w, m w ≤ 1 := hsum
  have hm1 : m v = 1 := by
    have : m v ≤ ∑ w, m w := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v)
    omega
  have hother : ∀ w ∈ Finset.univ, w ≠ v → m w = 0 := by
    intro w _ hwv
    have h1 : m v + m w ≤ ∑ u, m u := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := m)
        (show ({v, w} : Finset (Dir d)) ⊆ Finset.univ from Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
      rwa [Finset.sum_pair (Ne.symm hwv)] at this
    omega
  simp only [hmeq]
  rw [Finset.sum_eq_single v (fun w hw hwv => by simp [hother w hw hwv]) (by simp)]
  simp [hm1]

/-- No atom at time `y` in copy `j`: no jump. -/
theorem srw_no_jump (hν : relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d) {y : ℝ≥0}
    (hy : 0 < y) (hno : ∀ v : Dir d, Ñ ({(v, j)} ×ˢ {(y : ℝ)}) = 0) :
    (srwPath Ñ j).1.left y = (srwPath Ñ j).1.fn y := by
  obtain ⟨δ, -, -, -, hjump⟩ := srw_left_eq hν hy
  have : ∑ v : Dir d, ((natOf (Ñ ({(v, j)} ×ˢ {(y : ℝ)})) : ℕ) : ℤ) • v.vec = 0 :=
    Finset.sum_eq_zero fun v _ => by
      rw [hno v]
      simp [natOf]
  rw [this] at hjump
  exact (sub_eq_zero.1 hjump).symm

/-- Jump characterization: the canonical walk jumps at `y > 0` iff there is an atom at time `y`
in copy `j`, and then the jump is the direction of the atom. -/
theorem srw_jump_iff (hν : relabel {x : Dir d × J | x.2 = j} Prod.fst Ñ ∈ goodSet d) {y : ℝ≥0}
    (hy : 0 < y) :
    (srwPath Ñ j).1.left y ≠ (srwPath Ñ j).1.fn y ↔
      ∃ v : Dir d, Ñ ({(v, j)} ×ˢ {(y : ℝ)}) ≠ 0 := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    exact h (srw_no_jump hν hy hno)
  · rintro ⟨v, hv⟩ h
    have := srw_jump_dir hν hy hv
    rw [h, sub_self] at this
    have h2 : v.vec v.1 = 0 := by rw [← this]; rfl
    rw [ElboimSly.Cyclic.Dir.vec_apply_fst] at h2
    split_ifs at h2; simp at h2

end ElboimSly.Cyclic

end
