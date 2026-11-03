/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ProbeMeas
import Mathlib

/-!
# Elementary properties of probes

Elementary properties of probes.

* (a) `probeRegion_mono`, `iInter_probeRegion_ratTime`, `probeMass_eq_iInf`;
* (b) locality: `probeStep_congr`, `probeStep_restrict`;
* (c) regular configurations: `Reg`, `probeRho_le_iff` (i), `measure_region_eq_zero_of_lt` (ii),
  `exists_natCast_measure_region` and `one_le_measure_region` (iii);
* (d) `ae_reg`: a Poisson point process is almost surely regular.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} {R : S → ℝ≥0∞} {h : ℝ≥0}

/-! ### Basic facts on regions and `ρ` -/

theorem measurableSet_probeRegion (hR : Measurable R) (r : ℝ≥0∞) :
    MeasurableSet (probeRegion R r) :=
  measurableSet_le hR measurable_const

omit [MeasurableSpace S] in
theorem probeRegion_mono {r r' : ℝ≥0∞} (hr : r ≤ r') : probeRegion R r ⊆ probeRegion R r' :=
  fun _ hx => le_trans hx hr

theorem ratTime_mono {q q' : ℚ} (h : q ≤ q') : ratTime q ≤ ratTime q' := by
  unfold ratTime
  exact_mod_cast Real.toNNReal_le_toNNReal (by exact_mod_cast h)

theorem exists_ratTime_btwn {a b : ℝ≥0∞} (h : a < b) :
    ∃ q : ℚ, 0 ≤ q ∧ a < ratTime q ∧ ratTime q < b := by
  obtain ⟨q, hq, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
  exact ⟨q, hq, h1, h2⟩

section Rho

variable [SigmaFinite μ] {ν : Measure S}

theorem probeRho_le_h : probeRho μ R h ν ≤ h := min_le_left _ _

theorem probeRho_le_ratTime {q : ℚ} (hq0 : 0 ≤ q) (hq : ratTime q < h)
    (h1 : 1 ≤ tau μ ν (probeRegion R (ratTime q))) : probeRho μ R h ν ≤ ratTime q :=
  (min_le_right _ _).trans
    (iInf_le_of_le q (iInf_le_of_le ⟨hq0, hq, h1⟩ le_rfl))

theorem exists_ratTime_of_probeRho_lt {c : ℝ≥0∞} (hc : c ≤ (h : ℝ≥0∞))
    (hlt : probeRho μ R h ν < c) :
    ∃ q : ℚ, 0 ≤ q ∧ ratTime q < h ∧ 1 ≤ tau μ ν (probeRegion R (ratTime q)) ∧ ratTime q < c := by
  unfold probeRho at hlt
  rcases min_lt_iff.1 hlt with h1 | h1
  · exact absurd (lt_of_lt_of_le h1 hc) (lt_irrefl _)
  · obtain ⟨q, hq⟩ := iInf_lt_iff.1 h1
    obtain ⟨hP, hq2⟩ := iInf_lt_iff.1 hq
    exact ⟨q, hP.1, hP.2.1, hP.2.2, hq2⟩

theorem probeRho_eq_h_of_forall
    (hall : ∀ q : ℚ, 0 ≤ q → ratTime q < h → tau μ ν (probeRegion R (ratTime q)) < 1) :
    probeRho μ R h ν = h := by
  unfold probeRho
  have : (⨅ q : ℚ, ⨅ (_ : 0 ≤ q ∧ ratTime q < h ∧ 1 ≤ tau μ ν (probeRegion R (ratTime q))),
      ratTime q) = ⊤ := by
    refine le_antisymm le_top (le_iInf fun q => le_iInf fun hP => ?_)
    exact absurd hP.2.2 (not_le.2 (hall q hP.1 hP.2.1))
  rw [this, min_top_right]

end Rho

/-! ### Locality -/

section Locality

variable [SigmaFinite μ] (hR : Measurable R)

include hR in
theorem tau_region_eq_of_restrict_eq {ν ν' : Measure S}
    (hνν' : (tau μ ν).restrict (probeRegion R h) = (tau μ ν').restrict (probeRegion R h))
    {r : ℝ≥0∞} (hr : r ≤ h) : tau μ ν (probeRegion R r) = tau μ ν' (probeRegion R r) := by
  have hsub : probeRegion R r ⊆ probeRegion R h := probeRegion_mono hr
  have e := congrArg (fun m : Measure S => m (probeRegion R r)) hνν'
  simpa [Measure.restrict_apply (measurableSet_probeRegion hR r), Set.inter_eq_left.2 hsub] using e

include hR in
theorem probeRho_congr {ν ν' : Measure S}
    (hνν' : (tau μ ν).restrict (probeRegion R h) = (tau μ ν').restrict (probeRegion R h)) :
    probeRho μ R h ν = probeRho μ R h ν' := by
  unfold probeRho
  congr 1
  refine iInf_congr fun q => ?_
  refine iInf_congr_Prop ?_ fun _ => rfl
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1, by rwa [← tau_region_eq_of_restrict_eq hR hνν' h1.le]⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1, by rwa [tau_region_eq_of_restrict_eq hR hνν' h1.le]⟩

include hR in
/-- Elementary properties of probes (b), locality of the step map. -/
theorem probeStep_congr {ν ν' : Measure S}
    (hνν' : (tau μ ν).restrict (probeRegion R h) = (tau μ ν').restrict (probeRegion R h)) :
    probeStep μ R h ν = probeStep μ R h ν' := by
  have hρ := probeRho_congr hR hνν'
  unfold probeStep probeV
  rw [hρ]
  refine Prod.ext rfl ?_
  have hsub : probeRegion R (probeRho μ R h ν') ⊆ probeRegion R h :=
    probeRegion_mono probeRho_le_h
  show (tau μ ν).restrict _ = (tau μ ν').restrict _
  rw [← Measure.restrict_restrict_of_subset hsub, hνν', Measure.restrict_restrict_of_subset hsub]

theorem restrict_mem_lfSet {ν : Measure S} (hν : ν ∈ lfSet μ) (A : Set S) :
    ν.restrict A ∈ lfSet μ := fun k =>
  lt_of_le_of_lt (Measure.restrict_le_self _) (hν k)

include hR in
theorem probeRho_restrict {s : ℝ≥0} (hs : s ≤ h) {ν : Measure S} (hν : ν ∈ lfSet μ) :
    probeRho μ R s (ν.restrict (probeRegion R s)) = min (s : ℝ≥0∞) (probeRho μ R h ν) := by
  have hs' : (s : ℝ≥0∞) ≤ h := by exact_mod_cast hs
  simp only [probeRho, tau_of_mem μ (restrict_mem_lfSet hν _), tau_of_mem μ hν]
  have hreg : ∀ q : ℚ, ratTime q < s →
      (ν.restrict (probeRegion R s)) (probeRegion R (ratTime q)) = ν (probeRegion R (ratTime q)) := by
    intro q hq
    rw [Measure.restrict_apply (measurableSet_probeRegion hR _),
      Set.inter_eq_left.2 (probeRegion_mono hq.le)]
  rw [← min_assoc, min_eq_left hs']
  apply le_antisymm
  · refine le_min (min_le_left _ _) (le_iInf fun q => le_iInf fun hP => ?_)
    by_cases hq : ratTime q < s
    · refine (min_le_right _ _).trans (iInf_le_of_le q (iInf_le_of_le ⟨hP.1, hq, ?_⟩ le_rfl))
      rw [hreg q hq]; exact hP.2.2
    · exact (min_le_left _ _).trans (not_lt.1 hq)
  · refine le_min (min_le_left _ _) (le_iInf fun q => le_iInf fun hP => ?_)
    refine (min_le_right _ _).trans (iInf_le_of_le q (iInf_le_of_le ⟨hP.1, hP.2.1.trans_le hs', ?_⟩ le_rfl))
    rw [← hreg q hP.2.1]; exact hP.2.2

include hR in
/-- Elementary properties of probes (b): if `ρ(ν) ≤ s ≤ h`, the step map of `(R, h)` at `ν` is the step
map of `(R, s)` at `ν|_{D(s)}`. -/
theorem probeStep_restrict {s : ℝ≥0} (hs : s ≤ h) {ν : Measure S} (hν : ν ∈ lfSet μ)
    (hρ : probeRho μ R h ν ≤ s) :
    probeStep μ R s (ν.restrict (probeRegion R s)) = probeStep μ R h ν := by
  have h1 := probeRho_restrict hR hs hν
  rw [min_eq_right hρ] at h1
  unfold probeStep probeV
  rw [h1]
  refine Prod.ext rfl ?_
  show (tau μ (ν.restrict (probeRegion R s))).restrict _ = (tau μ ν).restrict _
  rw [tau_of_mem μ (restrict_mem_lfSet hν _), tau_of_mem μ hν,
    Measure.restrict_restrict_of_subset (probeRegion_mono hρ)]

end Locality

/-! ### Regular configurations -/

/-- Elementary properties of probes (c): `ν` is *regular relative to `B`* if the counts of
`D(q) ∩ B` are natural numbers for all rational `q < h` and for `q = h`. -/
def Reg (R : S → ℝ≥0∞) (h : ℝ≥0) (B : Set S) (ν : Measure S) : Prop :=
  (∀ q : ℚ, ∃ n : ℕ, ν (probeRegion R (min (ratTime q) h) ∩ B) = n) ∧
    ∃ n : ℕ, ν (probeRegion R h ∩ B) = n

theorem Reg.natCast_ratTime {B : Set S} {ν : Measure S} (hreg : Reg R h B ν) {q : ℚ}
    (hq : ratTime q < h) : ∃ n : ℕ, ν (probeRegion R (ratTime q) ∩ B) = n := by
  simpa [min_eq_left hq.le] using hreg.1 q

theorem Reg.lt_top {B : Set S} {ν : Measure S} (hreg : Reg R h B ν) :
    ν (probeRegion R h ∩ B) < ∞ := by
  obtain ⟨n, hn⟩ := hreg.2
  rw [hn]; exact ENNReal.natCast_lt_top n

theorem exists_natCast_iInf {ι : Type*} [Nonempty ι] (f : ι → ℝ≥0∞) (hf : ∀ i, ∃ n : ℕ, f i = n) :
    ∃ n : ℕ, ⨅ i, f i = n := by
  choose n hn using hf
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, n i₀ = sInf (Set.range n) := by
    have := Nat.sInf_mem (Set.range_nonempty n)
    obtain ⟨i₀, hi₀⟩ := this
    exact ⟨i₀, hi₀⟩
  refine ⟨n i₀, le_antisymm (hn i₀ ▸ iInf_le f i₀) (le_iInf fun i => ?_)⟩
  rw [hn i]
  exact_mod_cast hi₀ ▸ Nat.sInf_le (Set.mem_range_self i)

section Regular

variable [SigmaFinite μ] (hR : Measurable R)

/-- The rationals strictly between `r` and `h`. -/
abbrev RatBetween (h : ℝ≥0) (r : ℝ≥0∞) : Type :=
  {q : ℚ // 0 ≤ q ∧ r < ratTime q ∧ ratTime q < h}

theorem nonempty_ratBetween {r : ℝ≥0∞} (hr : r < h) : Nonempty (RatBetween h r) := by
  obtain ⟨q, h0, h1, h2⟩ := exists_ratTime_btwn hr
  exact ⟨⟨q, h0, h1, h2⟩⟩

omit [MeasurableSpace S] in
theorem iInter_ratBetween {r : ℝ≥0∞} (hr : r < h) (B : Set S) :
    ⋂ q : RatBetween h r, (probeRegion R (ratTime q.1) ∩ B) = probeRegion R r ∩ B := by
  have := nonempty_ratBetween (h := h) hr
  rw [← Set.iInter_inter]
  congr 1
  ext x
  simp only [Set.mem_iInter, probeRegion, Set.mem_ofPred_eq]
  constructor
  · intro hx
    by_contra hlt
    push Not at hlt
    obtain ⟨q, h0, h1, h2⟩ := exists_ratTime_btwn (lt_min hlt hr)
    exact absurd (hx ⟨q, h0, h1, h2.trans_le (min_le_right _ _)⟩)
      (not_le.2 (h2.trans_le (min_le_left _ _)))
  · intro hx q
    exact hx.trans q.2.2.1.le

include hR in
theorem measure_region_eq_iInf {r : ℝ≥0∞} (hr : r < h) {B : Set S} (hB : MeasurableSet B)
    {ν : Measure S} (hfin : ν (probeRegion R h ∩ B) ≠ ∞) :
    ν (probeRegion R r ∩ B) = ⨅ q : RatBetween h r, ν (probeRegion R (ratTime q.1) ∩ B) := by
  have := nonempty_ratBetween (h := h) hr
  rw [← iInter_ratBetween hr B]
  refine Directed.measure_iInter (fun q => ((measurableSet_probeRegion hR _).inter hB).nullMeasurableSet)
    ?_ ?_
  · intro q q'
    refine ⟨⟨min q.1 q'.1, le_min q.2.1 q'.2.1, ?_, ?_⟩, ?_, ?_⟩
    · rcases le_total q.1 q'.1 with hle | hle
      · rw [min_eq_left hle]; exact q.2.2.1
      · rw [min_eq_right hle]; exact q'.2.2.1
    · rcases le_total q.1 q'.1 with hle | hle
      · rw [min_eq_left hle]; exact q.2.2.2
      · rw [min_eq_right hle]; exact q'.2.2.2
    · exact Set.inter_subset_inter_left _ (probeRegion_mono (ratTime_mono (min_le_left _ _)))
    · exact Set.inter_subset_inter_left _ (probeRegion_mono (ratTime_mono (min_le_right _ _)))
  · refine ⟨Classical.choice inferInstance, ne_top_of_le_ne_top hfin (measure_mono ?_)⟩
    exact Set.inter_subset_inter_left _ (probeRegion_mono (Classical.choice inferInstance : RatBetween h r).2.2.2.le)

end Regular

section RegularFacts

variable [SigmaFinite μ] (hR : Measurable R) {ν : Measure S} (hν : ν ∈ lfSet μ)
  (hreg : Reg R h Set.univ ν)

include hR hν hreg in
/-- Elementary properties of probes (c)(i). -/
theorem probeRho_le_iff {r : ℝ≥0∞} (hr : r < h) :
    probeRho μ R h ν ≤ r ↔ 1 ≤ ν (probeRegion R r) := by
  constructor
  · intro hρ
    have hfin : ν (probeRegion R h ∩ Set.univ) ≠ ∞ := hreg.lt_top.ne
    have e := measure_region_eq_iInf hR hr MeasurableSet.univ hfin
    simp only [Set.inter_univ] at e
    rw [e]
    refine le_iInf fun q => ?_
    have hlt : probeRho μ R h ν < ratTime q.1 := hρ.trans_lt q.2.2.1
    obtain ⟨q', _, _, h1, h2⟩ := exists_ratTime_of_probeRho_lt q.2.2.2.le hlt
    rw [tau_of_mem μ hν] at h1
    exact h1.trans (measure_mono (probeRegion_mono h2.le))
  · intro h1
    by_contra hρ
    push Not at hρ
    obtain ⟨q, h0, hq1, hq2⟩ := exists_ratTime_btwn hρ
    have hqh : ratTime q < h := hq2.trans_le probeRho_le_h
    have := probeRho_le_ratTime (μ := μ) (ν := ν) (R := R) h0 hqh (by
      rw [tau_of_mem μ hν]; exact h1.trans (measure_mono (probeRegion_mono hq1.le)))
    exact absurd hq2 (not_lt.2 this)

include hν hreg in
/-- Elementary properties of probes (c)(ii). -/
theorem measure_region_eq_zero_of_lt {r : ℝ≥0∞} (hr : r < probeRho μ R h ν) :
    ν (probeRegion R r) = 0 := by
  obtain ⟨q, h0, hq1, hq2⟩ := exists_ratTime_btwn hr
  have hqh : ratTime q < h := hq2.trans_le probeRho_le_h
  obtain ⟨n, hn⟩ := hreg.natCast_ratTime hqh
  simp only [Set.inter_univ] at hn
  have hlt : ν (probeRegion R (ratTime q)) < 1 := by
    by_contra hge
    push Not at hge
    have := probeRho_le_ratTime (μ := μ) (ν := ν) (R := R) h0 hqh (by rwa [tau_of_mem μ hν])
    exact absurd hq2 (not_lt.2 this)
  have hn0 : n = 0 := by
    rw [hn] at hlt
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast hlt)
  refine le_antisymm ?_ zero_le
  calc ν (probeRegion R r) ≤ ν (probeRegion R (ratTime q)) := measure_mono (probeRegion_mono hq1.le)
    _ = 0 := by rw [hn, hn0]; simp

include hR in
/-- Elementary properties of probes (c)(iii): relative integrality at `ρ`. -/
theorem exists_natCast_measure_region {B : Set S} (hB : MeasurableSet B) (hregB : Reg R h B ν) :
    ∃ n : ℕ, ν (probeRegion R (probeRho μ R h ν) ∩ B) = n := by
  rcases lt_or_eq_of_le (probeRho_le_h (μ := μ) (R := R) (h := h) (ν := ν)) with hlt | heq
  · have := nonempty_ratBetween (h := h) hlt
    rw [measure_region_eq_iInf hR hlt hB hregB.lt_top.ne]
    exact exists_natCast_iInf _ fun q => hregB.natCast_ratTime q.2.2.2
  · rw [heq]; exact hregB.2

include hR hν hreg in
/-- Elementary properties of probes (c)(iii). -/
theorem one_le_measure_region (h1 : 1 ≤ ν (probeRegion R h)) :
    1 ≤ ν (probeRegion R (probeRho μ R h ν)) := by
  rcases lt_or_eq_of_le (probeRho_le_h (μ := μ) (R := R) (h := h) (ν := ν)) with hlt | heq
  · exact (probeRho_le_iff hR hν hreg hlt).1 le_rfl
  · rw [heq]; exact h1

include hν in
/-- Elementary properties of probes (c)(iii): if there is nothing in `D(h)`. -/
theorem probeRho_eq_h_of_measure_zero (h0 : ν (probeRegion R h) = 0) : probeRho μ R h ν = h := by
  refine probeRho_eq_h_of_forall fun q _ hq => ?_
  rw [tau_of_mem μ hν]
  calc ν (probeRegion R (ratTime q)) ≤ ν (probeRegion R h) := measure_mono (probeRegion_mono hq.le)
    _ = 0 := h0
    _ < 1 := zero_lt_one

include hν in
theorem probeV_eq_zero_of_measure_zero (h0 : ν (probeRegion R h) = 0) : probeV μ R h ν = 0 := by
  unfold probeV
  rw [probeRho_eq_h_of_measure_zero hν h0, tau_of_mem μ hν]
  exact Measure.restrict_eq_zero.2 h0

end RegularFacts

/-! ### Poisson point processes are almost surely regular -/

section AeReg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure S}

/-- Elementary properties of probes (d): almost surely, `N` is regular relative to each set of a
countable family. -/
theorem ae_reg (hN : IsPoissonPointProcess N μ P) (hR : Measurable R)
    (hfin : μ (probeRegion R h) < ∞) {ι : Type*} [Countable ι] {B : ι → Set S}
    (hB : ∀ i, MeasurableSet (B i)) : ∀ᵐ ω ∂P, ∀ i, Reg R h (B i) (N ω) := by
  let A : ι × Option ℚ → Set S := fun p =>
    match p.2 with
    | none => probeRegion R h ∩ B p.1
    | some q => probeRegion R (min (ratTime q) h) ∩ B p.1
  have hA : ∀ p, MeasurableSet (A p) := by
    rintro ⟨i, o⟩
    cases o <;> exact (measurableSet_probeRegion hR _).inter (hB i)
  have hAfin : ∀ p, μ (A p) < ∞ := by
    rintro ⟨i, o⟩
    refine lt_of_le_of_lt (measure_mono ?_) hfin
    cases o
    · exact Set.inter_subset_left
    · exact Set.inter_subset_left.trans (probeRegion_mono (min_le_right _ _))
  filter_upwards [hN.ae_forall_natCast_count hA hAfin] with ω hω i
  exact ⟨fun q => hω (i, some q), hω (i, none)⟩

end AeReg

end ElboimSly
