/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleRec
public import ElboimSly.Foundations.Cyclic.CycMultiRegion
public import ElboimSly.Foundations.Cyclic.CycMultiDef
public import Mathlib

/-!
# The explored region of the plan `𝔭₈` at length `t'_n + t`

W_2 after zeta_i, given ℱ^+_zeta_i, proof, "Separation": the region `R_{T_i}` consists of the points
`(1, e, [r'])`, `0 < r' ≤ t'_n`, `e ∋ W₁(r'-)`, and `(1, e, [q + r'])`, `0 < r' ≤ ζ_i`,
`e ∋ W₂(r'-)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)

/-- The path rule defining the environment record. -/
noncomputable def step78Rule (ν : Measure (Unit × RingSpace d β)) : PathRule Unit d :=
  fun k ρ => envPath ν ((step78Plan d β u q Tn).start k ρ)

variable {u q Tn}

theorem step78_envFinal_nth {ν : Measure (Unit × RingSpace d β)} (j : ℕ) :
    ((step78Plan d β u q Tn).envFinal ν).nth j =
      if j < 2 then some ((step78Plan d β u q Tn).E (step78Rule u q Tn ν) j) else none := by
  classical
  have h := CycPlan.cycFinal_nth_gen (step78Plan d β u q Tn) (step78Rule u q Tn ν) j
  have e : (step78Plan d β u q Tn).envFinal ν =
      (step78Plan d β u q Tn).cycFinal (step78Rule u q Tn ν) := rfl
  rw [e, h]
  have hc : (step78Plan d β u q Tn).Cont (step78Rule u q Tn ν) j ↔ j < 2 := by
    unfold CycPlan.Cont CycPlan.AllFin
    constructor
    · rintro ⟨h1, -⟩
      have hK : (step78Plan d β u q Tn).K = 2 := rfl
      rw [hK] at h1
      exact_mod_cast h1
    · intro hj
      have hK : (step78Plan d β u q Tn).K = 2 := rfl
      refine ⟨by rw [hK]; exact_mod_cast hj, fun i hi => ?_⟩
      have : i = 0 := by omega
      subst this
      rw [step78_E_zero_len]
      exact ENNReal.coe_lt_top
  simp only [hc]

theorem step78_num_eq_of_nth {ρ : CycRec Unit d} {I : ℕ} {f : ℕ → CycEntry Unit d}
    (h : ∀ j, ρ.nth j = if j < I then some (f j) else none) : ρ.num = I := by
  rcases ρ with ⟨m, g⟩ | g
  · have h1 : ∀ j, j < m ↔ j < I := fun j => by
      constructor
      · intro hj
        by_contra hI
        have := h j
        simp [CycRec.nth, hj, hI] at this
      · intro hI
        by_contra hj
        have := h j
        simp [CycRec.nth, hj, hI] at this
    have : m = I := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd ((h1 m).2 hlt) (lt_irrefl _)
      · exact absurd ((h1 I).1 hlt) (lt_irrefl _)
    simp [CycRec.num, this]
  · have := h I
    simp [CycRec.nth] at this

theorem step78_num_envFinal (ν : Measure (Unit × RingSpace d β)) :
    ((step78Plan d β u q Tn).envFinal ν).num = 2 :=
  step78_num_eq_of_nth (step78_envFinal_nth (u := u) (q := q) (Tn := Tn) (ν := ν))

theorem step78_coord_eq_E (junk : CycEntry Unit d) (ν : Measure (Unit × RingSpace d β)) {j : ℕ}
    (hj : j < 2) :
    ((step78Plan d β u q Tn).envFinal ν).coord junk j =
      (step78Plan d β u q Tn).E (step78Rule u q Tn ν) j := by
  simp [CycRec.coord, step78_envFinal_nth, hj]

theorem step78_cum_zero (ν : Measure (Unit × RingSpace d β)) :
    ((step78Plan d β u q Tn).envFinal ν).cum 0 = 0 := by
  simp [CycRec.cum]

theorem step78_cum_one (junk : CycEntry Unit d) (ν : Measure (Unit × RingSpace d β)) :
    ((step78Plan d β u q Tn).envFinal ν).cum 1 = Tn := by
  simp only [CycRec.cum, Finset.range_one, Finset.sum_singleton]
  rw [CycRec.lenAt_eq junk, ite_eq_left (by rw [step78_num_envFinal]; norm_num),
    step78_coord_eq_E junk ν (by norm_num), step78_E_zero_len]


/-- **w_2 after zeta_i, given ℱ^+_zeta_i, separation.** The region of `Trunc_{t'_n + t}` of the environment record. -/
theorem step78_region_subset {ν : Measure (Unit × RingSpace d β)} (hν : CycGood ν)
    (junk : CycEntry Unit d) {t : ℝ≥0} {x : CycS Unit d β}
    (hx : x ∈ (CycRec.trunc (Tn + t) ((step78Plan d β u q Tn).envFinal ν)).region β) :
    (∃ r : ℝ≥0, 0 < r ∧ r ≤ Tn ∧ x.2.2 = ((r : ℝ) : AddCircle β) ∧
        ∃ z, (∀ᶠ s : ℝ≥0 in 𝓝[<] r, ElboimSly.cycWalk (cycSlice () ν) 0 0 (s : ℝ) = z) ∧
          Edge.Mem z x.2.1) ∨
    (∃ r : ℝ≥0, 0 < r ∧ r ≤ t ∧ x.2.2 = ((q + r : ℝ) : AddCircle β) ∧
        ∃ z, (∀ᶠ s : ℝ≥0 in 𝓝[<] r, ElboimSly.cycWalk (cycSlice () ν) u q (s : ℝ) = z) ∧
          Edge.Mem z x.2.1) := by
  rw [CycRec.mem_region_trunc_iff junk] at hx
  obtain ⟨j, hj, r, hr0, hrl, hcum, h1, h2, h3⟩ := hx
  rw [step78_num_envFinal] at hj
  have hj2 : j < 2 := by exact_mod_cast hj
  rw [step78_coord_eq_E junk ν hj2] at hrl h2 h3
  have hev : ∀ᶠ s : ℝ≥0 in 𝓝[<] r,
      ((step78Plan d β u q Tn).E (step78Rule u q Tn ν) j).path.fn s =
        ((step78Plan d β u q Tn).E (step78Rule u q Tn ν) j).path.left r :=
    CPath.eventually_left _ hr0
  interval_cases j
  · left
    rw [step78_cum_zero, zero_add] at hcum
    rw [step78_E_zero_len] at hrl
    have hrT : r ≤ Tn := by exact_mod_cast hrl
    refine ⟨r, hr0, hrT, ?_, _, ?_, h3⟩
    · have hd : ((step78Plan d β u q Tn).E (step78Rule u q Tn ν) 0).data =
          (((), 0, 0, true) : CycData Unit d) := rfl
      rw [h2, hd]; simp [CycData.clock, CycData.sgn, CycData.phase, CycData.fwd]
    · filter_upwards [hev, self_mem_nhdsWithin] with s hs hsr
      have hsr' : s < r := hsr
      rw [← hs]
      exact ((step78_E_zero_path_fn u q Tn hν s).trans (by rw [min_eq_left (hsr'.le.trans hrT)])).symm
  · right
    rw [step78_cum_one junk ν] at hcum
    have hrt : r ≤ t := by
      have : (Tn : ℝ≥0∞) + r ≤ Tn + t := by exact_mod_cast hcum
      have := (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).1 this
      exact_mod_cast this
    refine ⟨r, hr0, hrt, ?_, _, ?_, h3⟩
    · have hd : ((step78Plan d β u q Tn).E (step78Rule u q Tn ν) 1).data =
          (((), u, q, true) : CycData Unit d) := rfl
      rw [h2, hd]; simp [CycData.clock, CycData.sgn, CycData.phase, CycData.fwd]
    · filter_upwards [hev] with s hs
      rw [← hs]
      exact (step78_E_one_path_fn u q Tn hν s).symm

end ElboimSly.Paper.Step

end
