/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.Greedy
import Mathlib

/-!
# Measurability of the greedy ring-path events

Measurability, Step 0.

For every window `[lo, hi]`, start vertex `y` and length `n`, the event "no ring path of length `n`
in the window starts at `y`" is, on `Nice` configurations, the trace of a measurable set of
measures (`exists_noPathFrom_set`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem measurableSet_ringsIn_lo (E : Set (Edge d)) (lo : ℝ) :
    MeasurableSet {ν : Measure (RingSpace d β) | RingsIn ν E lo} := by
  have : {ν : Measure (RingSpace d β) | RingsIn ν E lo} =
      ⋃ e ∈ E, {ν | 1 ≤ ν {(e, (lo : AddCircle β))}} := by
    ext ν; simp [RingsIn, Rings, ringSet]
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable E) fun e _ =>
    Measure.measurable_coe (measurableSet_singleton _) measurableSet_Ici

theorem measurable_gtime {lo : ℝ} {E : ℕ → Set (Edge d)} (hE : ∀ i, (E i).Finite) (i : ℕ) :
    Measurable (fun ν : NiceSet d β => gtime lo E i ν.1) := by
  induction i with
  | zero =>
    have h0 : Measurable (fun ν : NiceSet d β => nxtJ ν.1 (E 0) lo) :=
      (measurable_nxtJ (hE 0)).comp (measurable_id.prodMk measurable_const)
    simp only [gtime]
    exact Measurable.ite (measurable_subtype_coe (measurableSet_ringsIn_lo (E 0) lo))
      measurable_const h0
  | succ i ih =>
    simp only [gtime]
    exact (measurable_nxtJ (hE (i + 1))).comp (measurable_id.prodMk ih)

theorem exists_greedy_set {lo hi : ℝ} {E : ℕ → Set (Edge d)} (hE : ∀ i, (E i).Finite) (n : ℕ) :
    ∃ U : Set (Measure (RingSpace d β)), MeasurableSet U ∧
      ∀ ν, Nice ν → (GreedyOK lo hi E n ν ↔ ν ∈ U) := by
  let S : Set (NiceSet d β) :=
    (⋂ i, ⋂ (_ : i < n), Subtype.val ⁻¹' hasRingSet (E i)) ∩
      ⋂ i, ⋂ (_ : i + 1 = n), {ν | gtime lo E i ν.1 ≤ hi}
  have hS : MeasurableSet S := by
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurable_subtype_coe (measurableSet_hasRingSet _)) (MeasurableSet.iInter fun i =>
        MeasurableSet.iInter fun _ => measurableSet_le (measurable_gtime hE i) measurable_const)
  obtain ⟨U, hU, hUS⟩ := (MeasurableSpace.measurableSet_comap).1 hS
  refine ⟨U, hU, fun ν hν => ?_⟩
  have : (⟨ν, hν⟩ : NiceSet d β) ∈ S ↔ ν ∈ U := by
    rw [← hUS]; rfl
  rw [← this]
  simp only [S, GreedyOK, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    mem_hasRingSet_iff hν, Set.mem_ofPred_eq]

/-- Extension of a finite vertex sequence to `ℕ`. -/
def extSeq {n : ℕ} (w : Fin (n + 1) → Fin d → ℤ) (i : ℕ) : Fin d → ℤ :=
  if h : i < n + 1 then w ⟨i, h⟩ else w 0

omit [Fact (0 < β)] in
theorem exists_nRingPath_iff_ext (μ : Measure (RingSpace d β)) (J : Set ℝ) (y : Fin d → ℤ)
    (n : ℕ) :
    (∃ (v : ℕ → Fin d → ℤ) (t : ℕ → ℝ), v 0 = y ∧ NRingPath μ J n v t) ↔
      ∃ (w : Fin (n + 1) → Fin d → ℤ), w 0 = y ∧
        ∃ t : ℕ → ℝ, NRingPath μ J n (extSeq w) t := by
  constructor
  · rintro ⟨v, t, h0, hp⟩
    refine ⟨fun i => v i, h0, t, hp.1, hp.2.1, fun i hi => ?_⟩
    obtain ⟨e, he, hr⟩ := hp.2.2 i hi
    refine ⟨e, ?_, hr⟩
    simp only [extSeq, show i < n + 1 by omega, show i + 1 < n + 1 by omega, dite_eq_left]
    exact he
  · rintro ⟨w, h0, t, hp⟩
    exact ⟨extSeq w, t, by simpa [extSeq] using h0, hp⟩

theorem exists_noPathFrom_set (lo hi : ℝ) (y : Fin d → ℤ) (n : ℕ) :
    ∃ U : Set (Measure (RingSpace d β)), MeasurableSet U ∧
      ∀ ν, Nice ν → (NoPathFrom ν (Icc lo hi) y n ↔ ν ∈ U) := by
  have key : ∀ w : Fin (n + 1) → Fin d → ℤ, ∃ U : Set (Measure (RingSpace d β)),
      MeasurableSet U ∧ ∀ ν, Nice ν → (GreedyOK lo hi (pathE (extSeq w)) n ν ↔ ν ∈ U) :=
    fun w => exists_greedy_set (fun i => pathE_finite _ i) n
  choose U hU hUi using key
  refine ⟨⋂ w : {w : Fin (n + 1) → Fin d → ℤ // w 0 = y}, (U w.1)ᶜ,
    MeasurableSet.iInter fun w => (hU w.1).compl, fun ν hν => ?_⟩
  unfold NoPathFrom
  rw [exists_nRingPath_iff_ext]
  simp only [Set.mem_iInter, Set.mem_compl_iff, not_exists, not_and, Subtype.forall]
  constructor
  · intro h w hw hU'
    obtain ⟨t, ht⟩ := (greedy_iff hν (fun i => pathE_finite _ i) n _ rfl).mpr
      ((hUi w ν hν).mpr hU')
    exact h w hw t ht
  · intro h w hw t ht
    exact h w hw ((hUi w ν hν).mp ((greedy_iff hν (fun i => pathE_finite _ i) n _ rfl).mp ⟨t, ht⟩))

end ElboimSly.Cyclic

end
