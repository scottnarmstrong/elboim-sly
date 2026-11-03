/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.OneStepCeil
import Mathlib

/-!
# One step: the limit of the dyadic approximations

The unexplored part after one step, Step 2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly

theorem exists_stable_of_antitone (a : ℕ → ℝ≥0∞) (ha : Antitone a) (hn : ∀ n, ∃ k : ℕ, a n = k) :
    ∃ N, ∀ n ≥ N, a n = ⨅ m, a m := by
  choose k hk using hn
  obtain ⟨N, hN⟩ := Nat.sInf_mem (Set.range_nonempty k)
  have hle : ∀ m, k N ≤ k m := fun m => hN ▸ Nat.sInf_le (Set.mem_range_self m)
  have hinf : ⨅ m, a m = a N := by
    refine le_antisymm (iInf_le _ N) (le_iInf fun m => ?_)
    rw [hk N, hk m]; exact_mod_cast hle m
  refine ⟨N, fun n hn => ?_⟩
  rw [hinf]
  exact le_antisymm (ha hn) (by rw [← hinf]; exact iInf_le _ n)

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

theorem exists_dyadic_lt {ε : ℝ≥0} (hε : 0 < ε) : ∃ n : ℕ, h / (2 ^ n : ℕ) < ε := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (h / ε) (show (1 : ℝ≥0) < 2 by norm_num)
  refine ⟨n, ?_⟩
  push_cast
  rw [div_lt_iff₀ (by positivity)]
  rwa [div_lt_iff₀ hε, mul_comm] at hn

theorem iInter_region_gridCeil {B : Set S} (_hB : MeasurableSet B) {r : ℝ≥0∞} (hr : r ≤ h) :
    ⋂ n : ℕ, (probeRegion R (gridCeil h (2 ^ n) r) ∩ B) = probeRegion R r ∩ B := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro hx
    refine ⟨?_, (hx 0).2⟩
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := exists_dyadic_lt (h := h) hε
    have h1 := (hx n).1
    have h2 := gridCeil_le_add (h := h) (L := 2 ^ n) (by positivity) hr
    refine le_trans h1 (h2.trans ?_)
    have h3 : ((h / ((2 ^ n : ℕ) : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤ (ε : ℝ≥0∞) := by
      exact_mod_cast hn.le
    exact add_le_add le_rfl h3
  · rintro ⟨hx, hxB⟩ n
    exact ⟨hx.trans le_gridCeil, hxB⟩

theorem eventually_region_eq {B : Set S} (hB : MeasurableSet B) (hR : Measurable R)
    {κ : Measure S} {r : ℝ≥0∞} (hr : r ≤ h)
    (hnat : ∀ L i : ℕ, ∃ n : ℕ, κ (probeRegion R (gridTime h L (min i L)) ∩ B) = n) :
    ∃ N : ℕ, ∀ n ≥ N, κ (probeRegion R (gridCeil h (2 ^ n) r) ∩ B) =
      κ (probeRegion R r ∩ B) := by
  have hnat' : ∀ n : ℕ, ∃ k : ℕ, κ (probeRegion R (gridCeil h (2 ^ n) r) ∩ B) = k := by
    intro n
    obtain ⟨i, hi, he⟩ := exists_gridCeil_eq (h := h) (L := 2 ^ n) (by positivity) hr
    rw [he]
    simpa [min_eq_left hi] using hnat (2 ^ n) i
  have hsets : Antitone fun n : ℕ => probeRegion R (gridCeil h (2 ^ n) r) ∩ B :=
    fun m n hmn => Set.inter_subset_inter_left _ (probeRegion_mono (gridCeil_dyadic_anti r hmn))
  have hanti : Antitone fun n : ℕ => κ (probeRegion R (gridCeil h (2 ^ n) r) ∩ B) :=
    fun m n hmn => measure_mono (hsets hmn)
  obtain ⟨N, hN⟩ := exists_stable_of_antitone _ hanti hnat'
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn, ← iInter_region_gridCeil hB hr]
  obtain ⟨k, hk⟩ := hnat' 0
  exact (Antitone.measure_iInter hsets
    (fun n => ((measurableSet_probeRegion hR _).inter hB).nullMeasurableSet)
    ⟨0, by rw [hk]; exact ENNReal.natCast_ne_top k⟩).symm

theorem measure_inter_compl_eq {κ : Measure S} {B A A' : Set S} (hB : MeasurableSet B)
    (hA : MeasurableSet A) (hsub : A ⊆ A') (heq : κ (A' ∩ B) = κ (A ∩ B))
    (hfin : κ (A' ∩ B) ≠ ∞) : κ (A'ᶜ ∩ B) = κ (Aᶜ ∩ B) := by
  apply le_antisymm
  · exact measure_mono (Set.inter_subset_inter_left _ (Set.compl_subset_compl.2 hsub))
  · have hz : κ ((A' ∩ B) \ (A ∩ B)) = 0 := by
      rw [measure_sdiff (Set.inter_subset_inter_left _ hsub) (hA.inter hB).nullMeasurableSet
        (heq ▸ hfin), heq, tsub_self]
    calc κ (Aᶜ ∩ B) ≤ κ ((A'ᶜ ∩ B) ∪ ((A' ∩ B) \ (A ∩ B))) := by
          refine measure_mono fun x hx => ?_
          by_cases hx' : x ∈ A'
          · exact Or.inr ⟨⟨hx', hx.2⟩, fun h => hx.1 h.1⟩
          · exact Or.inl ⟨hx', hx.2⟩
      _ ≤ κ (A'ᶜ ∩ B) + κ ((A' ∩ B) \ (A ∩ B)) := measure_union_le _ _
      _ = κ (A'ᶜ ∩ B) := by rw [hz, add_zero]

theorem eventually_renew_eq {B : Set S} (hB : MeasurableSet B) (hR : Measurable R)
    {ν ν₂ : Measure S} (hν : ν ∈ lfSet μ) (hν₂ : ν₂ ∈ lfSet μ)
    (hnat : ∀ L i : ℕ, ∃ n : ℕ, ν (probeRegion R (gridTime h L (min i L)) ∩ B) = n)
    (hnat₂ : ∀ L i : ℕ, ∃ n : ℕ, ν₂ (probeRegion R (gridTime h L (min i L)) ∩ B) = n) :
    ∃ N : ℕ, ∀ n ≥ N,
      renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h ν))) (ν, ν₂) B =
        probeRenew μ R h ν ν₂ B := by
  obtain ⟨N1, hN1⟩ := eventually_region_eq hB hR
    (probeRho_le_h (μ := μ) (R := R) (h := h) (ν := ν)) hnat
  obtain ⟨N2, hN2⟩ := eventually_region_eq hB hR
    (probeRho_le_h (μ := μ) (R := R) (h := h) (ν := ν)) hnat₂
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  have hρt : probeRegion R (probeRho μ R h ν) ⊆
      probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h ν)) := probeRegion_mono le_gridCeil
  have hk : ∃ k : ℕ, ν (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h ν)) ∩ B) = k := by
    obtain ⟨i, hi, he⟩ := exists_gridCeil_eq (h := h) (L := 2 ^ n) (by positivity)
      (probeRho_le_h (μ := μ) (R := R) (h := h) (ν := ν))
    rw [he]
    obtain ⟨k, hk⟩ := hnat (2 ^ n) i
    exact ⟨k, by simpa [min_eq_left hi] using hk⟩
  have hfin : ν (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h ν)) ∩ B) ≠ ∞ := by
    obtain ⟨k, hk⟩ := hk
    rw [hk]; exact ENNReal.natCast_ne_top k
  have h3 := measure_inter_compl_eq (κ := ν) hB (measurableSet_probeRegion hR _) hρt h1 hfin
  unfold renewAt probeRenew
  rw [Measure.add_apply, Measure.add_apply, Measure.restrict_apply hB, Measure.restrict_apply hB,
    Measure.restrict_apply hB, Measure.restrict_apply hB, tau_of_mem μ hν, tau_of_mem μ hν₂]
  simp only [Set.inter_comm B]
  exact congrArg₂ (· + ·) h3 h2

end ElboimSly
