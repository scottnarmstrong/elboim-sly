/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe
public import ElboimSly.Foundations.Cyclic.CycThitDriven
public import ElboimSly.Foundations.Cyclic.CycDrivenLawRegion
public import Mathlib

/-!
# ES22 Lemma 2.2: the regenerated walk is right-continuous

ES22 Lemma 2.2 ("the event is measurable by right-continuity", countable reduction of path events (i)).

* `gluedWalk_rc`: a gluing of right-continuous pieces at times `σ_k` with `σ_k → ∞` is
  right-continuous;
* `regenWalk_rc`: for a good environment on `ℕ × S_β`, the regenerated walk of the slices is
  right-continuous.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

theorem gluedWalk_rc {V : Type*} {σ : ℕ → ℝ≥0∞} (hm : Monotone σ) (h0 : σ 0 = 0)
    (hbdd : ∀ t : ℝ≥0, BddAbove {k : ℕ | σ k ≤ t}) {w : ℕ → ℝ≥0 → V}
    (hw : ∀ k s, ∀ᶠ u in 𝓝[≥] s, w k u = w k s) (s : ℝ≥0) :
    ∀ᶠ u in 𝓝[≥] s, gluedWalk σ w u = gluedWalk σ w s := by
  obtain ⟨h1, h2⟩ := gluedCount_spec h0 (hbdd s)
  set N := gluedCount σ s with hN
  have hlt : σ N < ⊤ := lt_of_le_of_lt h1 ENNReal.coe_lt_top
  set c := (σ N).toNNReal with hc
  have hcoe : σ N = (c : ℝ≥0∞) := (ENNReal.coe_toNNReal hlt.ne).symm
  have hcs : c ≤ s := by rw [hcoe] at h1; exact_mod_cast h1
  have hn1 : ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, (u : ℝ≥0∞) < σ (N + 1) :=
    mem_nhdsWithin_of_mem_nhds
      ((isOpen_Iio.preimage ENNReal.continuous_coe).mem_nhds h2)
  have hn2 : ∀ᶠ u in 𝓝[≥] s, w N (u - c) = w N (s - c) := by
    have ht : Tendsto (fun u : ℝ≥0 => u - c) (𝓝[≥] s) (𝓝[≥] (s - c)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (((continuous_id.sub continuous_const).tendsto s).mono_left nhdsWithin_le_nhds)
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact mem_Ici.2 (tsub_le_tsub_right (mem_Ici.1 hu) c)
    exact ht.eventually (hw N (s - c))
  filter_upwards [hn1, hn2, self_mem_nhdsWithin] with u hu1 hu2 hu3
  have hcnt : gluedCount σ u = N := by
    refine gluedCount_eq hm ?_ hu1
    exact h1.trans (by exact_mod_cast hu3)
  unfold gluedWalk
  rw [hcnt, ← hN, ← hc]
  exact hu2

theorem bdd_partialSums {τ : ℕ → ℝ≥0∞} {b : ℝ≥0} (hb : 0 < b) (hτ : ∀ k, (b : ℝ≥0∞) ≤ τ k)
    (t : ℝ≥0) : BddAbove {k : ℕ | partialSums τ k ≤ t} := by
  obtain ⟨N, hN⟩ := exists_lt_nsmul hb t
  refine ⟨N, fun k hk => ?_⟩
  by_contra hkN
  rw [not_le] at hkN
  have h1 := sum_ge_nsmul hτ k
  have h2 : ((k : ℝ≥0) * b : ℝ≥0) ≤ t := by
    have : ((k : ℝ≥0) * b : ℝ≥0) ≤ (t : ℝ≥0∞) := by
      calc (((k : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) = (k : ℝ≥0∞) * b := by push_cast; rfl
        _ ≤ _ := h1
        _ ≤ t := hk
    exact_mod_cast this
  have h3 : (N : ℝ≥0) * b ≤ k * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hkN.le) zero_le
  rw [nsmul_eq_mul] at hN
  exact absurd (lt_of_lt_of_le hN h3) (not_lt.2 h2)

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk of the slices of a good environment is right-continuous. -/
theorem regenWalk_rc {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (s : ℝ≥0) :
    ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, ElboimSly.regenWalk (fun k => cycSlice k ν) (u : ℝ) =
      ElboimSly.regenWalk (fun k => cycSlice k ν) (s : ℝ) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  set σ := partialSums fun k => ElboimSly.cycTreg (cycSlice k ν) with hσ
  have hm : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ, partialSums_succ]; exact le_self_add
  have h0 : σ 0 = 0 := by simp [hσ, partialSums]
  have hbdd := bdd_partialSums hb (τ := fun k => ElboimSly.cycTreg (cycSlice k ν))
    (fun k => regPlan_tau_ge _)
  have hw : ∀ (k : ℕ) (s : ℝ≥0), ∀ᶠ u : ℝ≥0 in 𝓝[≥] s,
      ElboimSly.cycWalk (cycSlice k ν) 0 0 (u : ℝ) = ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ) := by
    intro k s
    have hlen := envPath_len (δ := regionData d k) (ν := ν) (hν k)
    have hfn : ∀ u : ℝ≥0, ElboimSly.cycWalk (cycSlice k ν) 0 0 (u : ℝ) =
        (envPath ν (regionData d k)).1.fn u := fun u => by
      rw [hlen.2]; exact (envFn_regionData' ν k u).symm
    simp only [hfn]
    exact (envPath ν (regionData d k)).1.rc s
  have := gluedWalk_rc hm h0 hbdd (w := fun k s => ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ)) hw s
  simpa only [hσ, gluedWalk_eq_regenWalk] using this

end ElboimSly.Cyclic

end
