/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.Swap
public import ElboimSly.Frozen.Defs.EdgeInstMeasurableSingletonClass
import Mathlib

/-!
# Ring times at a vertex

Existence and uniqueness of trajectories (construction step), using (G1).

For a good configuration, the set of real times at which an edge containing `z` rings is
`β`-periodic and meets every compact interval in a finite set. Hence, if it is nonempty, it has a
least element after any time and a greatest element before any time. One step of the trajectory
construction jumps to such a time.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- Only finitely many edges contain a given vertex. -/
theorem edgesAt_finite (z : Fin d → ℤ) : {e : Edge d | e.Mem z}.Finite := by
  have hW : {w : Fin d → ℤ | ∀ i, w i ∈ Set.Icc (z i - 1) (z i + 1)}.Finite :=
    Set.Finite.pi' (fun i => Set.finite_Icc (z i - 1) (z i + 1)) |>.subset (fun w hw i => hw i)
  have hT : ((fun w => s(z, w)) '' {w : Fin d → ℤ | ∀ i, w i ∈ Set.Icc (z i - 1) (z i + 1)}).Finite :=
    hW.image _
  refine (hT.preimage Subtype.val_injective.injOn).subset ?_
  intro e he
  obtain ⟨u, v, huv, hadj⟩ := e.2
  have hz : z ∈ e.1 := he
  have hbound : ∀ i, |u i - v i| ≤ 1 := fun i => by
    rw [← hadj]
    exact Finset.single_le_sum (f := fun i => |u i - v i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  rw [huv, Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · refine ⟨v, fun i => ?_, huv.symm⟩
    have := abs_le.mp (hbound i)
    constructor <;> linarith [this.1, this.2]
  · refine ⟨u, fun i => ?_, by rw [huv, Sym2.eq_swap]⟩
    have := abs_le.mp (hbound i)
    constructor <;> linarith [this.1, this.2]

omit [Fact (0 < β)] in
/-- The ring set of an edge is finite (G1). -/
theorem ringSet_finite (hν : Good ν) (e : Edge d) : (ringSet ν e).Finite := by
  have hfin : ν ({e} ×ˢ Set.univ) < ⊤ := hν.2.1 e
  have key := Measure.finite_const_le_meas_of_disjoint_iUnion ν (ε := 1)
    (ι := AddCircle β) (As := fun θ => {((e, θ) : RingSpace d β)}) zero_lt_one
    (fun θ => measurableSet_singleton _)
    (fun θ θ' h => by
      simp only [Function.onFun, Set.disjoint_singleton]
      intro h'; exact h (by simpa using h'))
    (ne_of_lt (lt_of_le_of_lt (measure_mono (fun p hp => by
      obtain ⟨θ, rfl⟩ := Set.mem_iUnion.mp hp
      exact ⟨rfl, Set.mem_univ _⟩)) hfin))
  exact key

/-- The classes in the circle at which some edge at `z` rings. -/
def ringClasses (ν : Measure (RingSpace d β)) (z : Fin d → ℤ) : Set (AddCircle β) :=
  {θ | ∃ e : Edge d, e.Mem z ∧ θ ∈ ringSet ν e}

omit [Fact (0 < β)] in
theorem ringClasses_finite (hν : Good ν) (z : Fin d → ℤ) : (ringClasses ν z).Finite :=
  ((edgesAt_finite z).biUnion (fun e _ => ringSet_finite hν e)).subset
    (fun _ ⟨_e, he, hθ⟩ => Set.mem_biUnion he hθ)

omit [Fact (0 < β)] in
theorem ringAt_iff {z : Fin d → ℤ} {t : ℝ} :
    RingAt ν z t ↔ (t : AddCircle β) ∈ ringClasses ν z := Iff.rfl

omit [Fact (0 < β)] in
/-- Ring times are `β`-periodic. -/
theorem RingAt.add_zsmul {z : Fin d → ℤ} {t : ℝ} (h : RingAt ν z t) (n : ℤ) :
    RingAt ν z (t + n * β) := by
  have : ((t + n * β : ℝ) : AddCircle β) = (t : AddCircle β) := by
    rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero,
      add_zero]
  rw [ringAt_iff] at *
  rwa [this]

/-- Ring times at a vertex meet every compact interval in a finite set (G1). -/
theorem ringAt_finite_Icc (hν : Good ν) (z : Fin d → ℤ) (p q : ℝ) :
    {t | t ∈ Set.Icc p q ∧ RingAt ν z t}.Finite := by
  have hF := ringClasses_finite hν z
  have hβ : 0 < β := Fact.out
  choose c hc using fun θ : AddCircle β => QuotientAddGroup.mk_surjective θ
  refine (hF.biUnion (fun θ _ => (Set.finite_Icc ⌈(p - c θ) / β⌉ ⌊(q - c θ) / β⌋).image
    (fun n : ℤ => c θ + n * β))).subset ?_
  rintro t ⟨⟨hp, hq⟩, hr⟩
  refine Set.mem_biUnion (x := (t : AddCircle β)) hr ?_
  have h1 : ((t - c (t : AddCircle β) : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_sub]
    have := hc (t : AddCircle β)
    rw [show (((c (t : AddCircle β) : ℝ)) : AddCircle β) = t from this, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := β)).mp h1
  rw [zsmul_eq_mul] at hn
  refine ⟨n, ⟨?_, ?_⟩, by simp only []; linarith⟩
  · rw [Int.ceil_le, div_le_iff₀ hβ]; linarith
  · rw [Int.le_floor, le_div_iff₀ hβ]; linarith

/-- The next ring time after `t`, if the vertex ever has one. -/
theorem exists_next_ring (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) (hne : ∃ u, RingAt ν z u) :
    ∃ τ, IsLeast {u | t < u ∧ RingAt ν z u} τ := by
  obtain ⟨u0, hu0⟩ := hne
  have hβ : 0 < β := Fact.out
  obtain ⟨k, hk⟩ := exists_nat_gt ((t - u0) / β)
  have hw : RingAt ν z (u0 + (k : ℝ) * β) := by simpa using hu0.add_zsmul (k : ℤ)
  have hwt : t < u0 + (k : ℝ) * β := by
    rw [div_lt_iff₀ hβ] at hk; linarith
  set w := u0 + (k : ℝ) * β
  have hfin : {u | t < u ∧ u ≤ w ∧ RingAt ν z u}.Finite :=
    (ringAt_finite_Icc hν z t w).subset (fun u ⟨h1, h2, h3⟩ => ⟨⟨h1.le, h2⟩, h3⟩)
  have hne : {u | t < u ∧ u ≤ w ∧ RingAt ν z u}.Nonempty := ⟨w, hwt, le_rfl, hw⟩
  have hmem := hne.csInf_mem hfin
  refine ⟨sInf {u | t < u ∧ u ≤ w ∧ RingAt ν z u}, ⟨hmem.1, hmem.2.2⟩, fun u ⟨hu1, hu2⟩ => ?_⟩
  by_cases huw : u ≤ w
  · exact csInf_le hfin.bddBelow ⟨hu1, huw, hu2⟩
  · exact le_trans (hmem.2.1) (not_le.mp huw).le

/-- The previous ring time before `t`, if the vertex ever has one. -/
theorem exists_prev_ring (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) (hne : ∃ u, RingAt ν z u) :
    ∃ τ, IsGreatest {u | u < t ∧ RingAt ν z u} τ := by
  obtain ⟨u0, hu0⟩ := hne
  have hβ : 0 < β := Fact.out
  obtain ⟨k, hk⟩ := exists_nat_gt ((u0 - t) / β)
  have hw : RingAt ν z (u0 - (k : ℝ) * β) := by
    simpa [sub_eq_add_neg] using hu0.add_zsmul (-(k : ℤ))
  have hwt : u0 - (k : ℝ) * β < t := by
    rw [div_lt_iff₀ hβ] at hk; linarith
  set w := u0 - (k : ℝ) * β
  have hfin : {u | w ≤ u ∧ u < t ∧ RingAt ν z u}.Finite :=
    (ringAt_finite_Icc hν z w t).subset (fun u ⟨h1, h2, h3⟩ => ⟨⟨h1, h2.le⟩, h3⟩)
  have hne : {u | w ≤ u ∧ u < t ∧ RingAt ν z u}.Nonempty := ⟨w, le_rfl, hwt, hw⟩
  have hmem := hne.csSup_mem hfin
  refine ⟨sSup {u | w ≤ u ∧ u < t ∧ RingAt ν z u}, ⟨hmem.2.1, hmem.2.2⟩, fun u ⟨hu1, hu2⟩ => ?_⟩
  by_cases huw : w ≤ u
  · exact le_csSup hfin.bddAbove ⟨huw, hu1, hu2⟩
  · exact le_trans (not_le.mp huw).le hmem.1

/-- One forward step of the trajectory construction: the next ring time (or a dummy time if the
vertex never rings), together with the post-jump position. -/
theorem exists_step_fwd (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) :
    ∃ (τ : ℝ) (w : Fin d → ℤ), t < τ ∧ (∀ u, t < u → u < τ → ¬ RingAt ν z u) ∧
      SwapRule ν τ z w ∧
      ((∃ e : Edge d, e.1 = s(z, w) ∧ Rings ν e τ) ∨
        (τ = t + 1 ∧ w = z ∧ ∀ u, ¬ RingAt ν z u)) := by
  by_cases hne : ∃ u, RingAt ν z u
  · obtain ⟨τ, ⟨hτt, e, hez, her⟩, hlow⟩ := exists_next_ring hν z t hne
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hez
    refine ⟨τ, w, hτt, fun u hu hu' hr => ?_, swapRule_of_edge hν e hw her, Or.inl ⟨e, hw, her⟩⟩
    exact absurd (hlow ⟨hu, hr⟩) (not_le.mpr hu')
  · push Not at hne
    exact ⟨t + 1, z, by linarith, fun u _ _ => hne u, swapRule_self (hne _),
      Or.inr ⟨rfl, rfl, hne⟩⟩

/-- One backward step of the trajectory construction. -/
theorem exists_step_bwd (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) :
    ∃ (τ : ℝ) (w : Fin d → ℤ), τ < t ∧ (∀ u, τ < u → u < t → ¬ RingAt ν z u) ∧
      SwapRule ν τ z w ∧
      ((∃ e : Edge d, e.1 = s(z, w) ∧ Rings ν e τ) ∨
        (τ = t - 1 ∧ w = z ∧ ∀ u, ¬ RingAt ν z u)) := by
  by_cases hne : ∃ u, RingAt ν z u
  · obtain ⟨τ, ⟨hτt, e, hez, her⟩, hup⟩ := exists_prev_ring hν z t hne
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hez
    refine ⟨τ, w, hτt, fun u hu hu' hr => ?_, swapRule_of_edge hν e hw her, Or.inl ⟨e, hw, her⟩⟩
    exact absurd (hup ⟨hu', hr⟩) (not_le.mpr hu)
  · push Not at hne
    exact ⟨t - 1, z, by linarith, fun u _ _ => hne u, swapRule_self (hne _),
      Or.inr ⟨rfl, rfl, hne⟩⟩

/-- A gap after `b`: a time `c ∈ (b, b + 1]` such that `y` does not ring in `(b, c)`. -/
theorem exists_gap (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) :
    ∃ c, b < c ∧ c ≤ b + 1 ∧ ∀ u, b < u → u < c → ¬ RingAt ν y u := by
  by_cases hne : ∃ u, RingAt ν y u
  · obtain ⟨τ, ⟨hτt, _⟩, hlow⟩ := exists_next_ring hν y b hne
    refine ⟨min τ (b + 1), lt_min hτt (by linarith), min_le_right _ _, fun u hu hu' hr => ?_⟩
    exact absurd (hlow ⟨hu, hr⟩) (not_le.mpr (lt_of_lt_of_le hu' (min_le_left _ _)))
  · push Not at hne
    exact ⟨b + 1, by linarith, le_rfl, fun u _ _ => hne u⟩

end ElboimSly.Interchange
