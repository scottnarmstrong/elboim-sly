/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointGrid
import Mathlib

/-!
# The grid argument for the first-point law: probabilistic estimates

First-point law of a deterministic probe, proof of (c) (Claims A, B and the two-sided bound).

Here `W` is the law of a Poisson point process on `Measure S`: `IsPoissonPointProcess id μ W`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞} {h : ℝ≥0}
  {W : Measure (Measure S)}

/-- The law of a Poisson point process of intensity `μ` on `Measure S` (`N = id`). -/
abbrev IsPPPLaw (μ : Measure S) (W : Measure (Measure S)) : Prop :=
  IsPoissonPointProcess (fun ν : Measure S => ν) μ W

theorem gridTime_lt {h : ℝ≥0} (hh : 0 < h) {L j : ℕ} (hj : j < L) : gridTime h L j < h := by
  unfold gridTime
  have hL : (0 : ℝ≥0) < L := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hj)
  rw [div_lt_iff₀ hL]
  have : (j : ℝ≥0) < L := by exact_mod_cast hj
  calc h * j < h * L := by gcongr
    _ = h * L := rfl

theorem probeV_apply {ν : Measure S} (hν : ν ∈ lfSet μ) (_hR : Measurable R) {B : Set S}
    (hB : MeasurableSet B) :
    probeV μ R h ν B = ν (probeRegion R (probeRho μ R h ν) ∩ B) := by
  unfold probeV
  rw [Measure.restrict_apply hB, tau_of_mem μ hν, Set.inter_comm]

theorem probeV_univ {ν : Measure S} (hν : ν ∈ lfSet μ) :
    probeV μ R h ν Set.univ = ν (probeRegion R (probeRho μ R h ν)) := by
  unfold probeV
  rw [Measure.restrict_apply_univ, tau_of_mem μ hν]

/-- The almost sure event on which all the regularity properties hold. -/
def GoodSet (μ : Measure S) [SigmaFinite μ] (R : S → ℝ≥0∞) (h : ℝ≥0) (B : Set S) :
    Set (Measure S) :=
  {ν | ν ∈ lfSet μ ∧ Reg R h Set.univ ν ∧ Reg R h B ν ∧
    ∀ L i : ℕ, ∃ n : ℕ, ν (probeRegion R (gridTime h L (min i L))) = n}

theorem ae_goodSet (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) {B : Set S} (hB : MeasurableSet B) :
    ∀ᵐ ν ∂W, ν ∈ GoodSet μ R h B := by
  have h1 := hW.ae_mem_lfSet
  have h2 := ae_reg hW hP.measurable hP.mass_lt_top
    (B := fun b : Bool => if b then B else Set.univ) (fun b => by cases b <;> simp [hB])
  have h3 := hW.ae_forall_natCast_count (ι := ℕ × ℕ)
    (A := fun p => probeRegion R (gridTime h p.1 (min p.2 p.1)))
    (fun p => measurableSet_probeRegion hP.measurable _)
    (fun p => lt_of_le_of_lt (measure_mono (probeRegion_mono (by
      by_cases hp : p.1 = 0
      · have : min p.2 p.1 = 0 := by simp [hp]
        rw [this, gridTime_zero]; simp
      · exact_mod_cast gridTime_le (Nat.pos_of_ne_zero hp) (min_le_right _ _)))) hP.mass_lt_top)
  filter_upwards [h1, h2, h3] with ν hν hreg hgrid
  exact ⟨hν, by simpa using hreg false, by simpa using hreg true,
    fun L i => hgrid (L, i)⟩

section Cells

variable (hR : Measurable R) (hh : 0 < h) {B : Set S} (hB : MeasurableSet B)

include hR hh hB in
theorem cellEvent_good_subset {L i : ℕ} (hL : 0 < L) (hi1 : 1 ≤ i) (hiL : i ≤ L) {ν : Measure S}
    (hν : ν ∈ GoodSet μ R h B) (hc : ν ∈ cellEvent R h B L i) :
    ν ∈ firstEvent μ R h B ∧ ν ∈ cellIndex μ R h L i := by
  obtain ⟨hlf, hreg, hregB, hgrid⟩ := hν
  have := cell_event_imp hR hlf hreg (a := gridTime h L (i - 1)) (b := gridTime h L i)
    (gridTime_lt hh (by omega)) (gridTime_mono (Nat.sub_le i 1)) (gridTime_le hL hiL) hB hc.1
    hc.2.1 hc.2.2
  obtain ⟨hsucc, hρ1, hρB, hρa, hρb⟩ := this
  refine ⟨⟨?_, ?_, ?_⟩, hρa, hρb⟩
  · rw [tau_of_mem μ hlf]; exact hsucc
  · rw [probeV_univ hlf]; exact hρ1
  · rw [probeV_apply hlf hR hB]; exact hρB

include hR hB in
theorem cellEvent_of_firstEvent {L i : ℕ} (_hi1 : 1 ≤ i) (hiL : i ≤ L) {ν : Measure S}
    (hν : ν ∈ GoodSet μ R h B) (hf : ν ∈ firstEvent μ R h B) (hc : ν ∈ cellIndex μ R h L i) :
    ν ∈ cellEvent R h B L i ∨ 2 ≤ ν (gridCell R h L i) := by
  obtain ⟨hlf, hreg, hregB, hgrid⟩ := hν
  by_cases hlt : ν (gridCell R h L i) < 2
  · left
    have hρ1 : ν (probeRegion R (probeRho μ R h ν)) = 1 := by
      rw [← probeV_univ hlf]; exact hf.2.1
    have hρB : ν (probeRegion R (probeRho μ R h ν) ∩ B) = 1 := by
      rw [← probeV_apply hlf hR hB]; exact hf.2.2
    have hb : ∃ n : ℕ, ν (probeRegion R (gridTime h L i)) = n := by
      simpa [min_eq_left hiL] using hgrid L i
    exact cell_event_of_imp hR hlf hreg (gridTime_mono (Nat.sub_le i 1)) hB hρ1 hρB hc.1 hc.2 hb hlt
  · right
    exact not_lt.1 hlt

omit [SigmaFinite μ] in
theorem measure_cellEvent (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) {B : Set S}
    (hB : MeasurableSet B) {L i : ℕ} (hL : 0 < L) (_hi1 : 1 ≤ i) (hiL : i ≤ L) :
    W (cellEvent R h B L i) =
      μ (gridCell R h L i ∩ B) * expNeg (probeMass μ R (gridTime h L i)) := by
  have hR := hP.measurable
  have hab : (gridTime h L (i - 1) : ℝ≥0∞) ≤ gridTime h L i := by
    exact_mod_cast gridTime_mono (Nat.sub_le i 1)
  have hbh : (gridTime h L i : ℝ≥0∞) ≤ h := by exact_mod_cast gridTime_le hL hiL
  have hmeasΔ : MeasurableSet (gridCell R h L i) :=
    (measurableSet_probeRegion hR _).diff (measurableSet_probeRegion hR _)
  have hfin : ∀ A, A ⊆ probeRegion R h → μ A < ∞ := fun A hA =>
    lt_of_le_of_lt (measure_mono hA) hP.mass_lt_top
  have hsubΔ : gridCell R h L i ⊆ probeRegion R h := fun x hx =>
    probeRegion_mono hbh hx.1
  have hsub0 : probeRegion R (gridTime h L (i - 1)) ⊆ probeRegion R h :=
    probeRegion_mono (hab.trans hbh)
  have key := hW.measure_zero_one_zero (A₀ := probeRegion R (gridTime h L (i - 1)))
    (A₁ := gridCell R h L i ∩ B) (A₂ := gridCell R h L i \ B)
    (measurableSet_probeRegion hR _) (hmeasΔ.inter hB) (hmeasΔ.diff hB)
    (Set.disjoint_left.2 fun x hx hx' => hx'.1.2 hx)
    (Set.disjoint_left.2 fun x hx hx' => hx'.1.2 hx)
    (Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2)
    (hfin _ hsub0) (hfin _ (Set.inter_subset_left.trans hsubΔ))
    (hfin _ (Set.sdiff_subset.trans hsubΔ))
  have hsum : μ (probeRegion R (gridTime h L (i - 1))) + μ (gridCell R h L i ∩ B) +
      μ (gridCell R h L i \ B) = probeMass μ R (gridTime h L i) := by
    have h1 := measure_inter_add_sdiff (μ := μ) (gridCell R h L i) hB
    rw [add_assoc, h1]
    exact (measure_region_cell hR hab).symm
  rw [hsum] at key
  exact key

end Cells

end ElboimSly
