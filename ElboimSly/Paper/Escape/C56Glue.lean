/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFarRc
public import ElboimSly.Foundations.Cyclic.CPath
public import ElboimSly.Foundations.Cyclic.DrivenDef
public import ElboimSly.Paper.Avoid.CoupleAux
public import Mathlib

/-!
# Glued walks have finitely many jumps on bounded intervals

Used for ES22 Claim 5.6: the regenerated walk of a good environment is a `CPath`, so that the
first-relaxed-time machinery of first relaxed times are relaxed and are stopping times applies.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic

variable {V : Type*}

theorem gluedWalk_fin {σ : ℕ → ℝ≥0∞} (hm : Monotone σ) (h0 : σ 0 = 0)
    (hbdd : ∀ t : ℝ≥0, BddAbove {k : ℕ | σ k ≤ t}) {w : ℕ → ℝ≥0 → V}
    (hw : ∀ k T, (CDisc (w k) ∩ Iic T).Finite) (T : ℝ≥0) :
    (CDisc (gluedWalk σ w) ∩ Iic T).Finite := by
  set K := gluedCount σ T with hK
  have hS : (⋃ k ∈ Finset.range (K + 1), ({(σ k).toNNReal} ∪
      (fun r => r + (σ k).toNNReal) '' (CDisc (w k) ∩ Iic T))).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun k _ => ?_
    exact (Set.finite_singleton _).union ((hw k T).image _)
  refine hS.subset ?_
  rintro s ⟨⟨hs0, hsd⟩, hsT⟩
  have hsT' : s ≤ T := hsT
  obtain ⟨h1, h2⟩ := gluedCount_spec h0 (hbdd s)
  set N := gluedCount σ s with hN
  have hNK : N ≤ K := csSup_le_csSup (hbdd T) ⟨0, by simp [h0]⟩
    (fun k (hk : σ k ≤ (s : ℝ≥0∞)) => show σ k ≤ (T : ℝ≥0∞) from
      le_trans hk (by exact_mod_cast hsT'))
  have hlt : σ N < ⊤ := lt_of_le_of_lt h1 ENNReal.coe_lt_top
  set c := (σ N).toNNReal with hc
  have hcoe : σ N = (c : ℝ≥0∞) := (ENNReal.coe_toNNReal hlt.ne).symm
  have hcs : c ≤ s := by rw [hcoe] at h1; exact_mod_cast h1
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_image]
  refine ⟨N, by omega, ?_⟩
  rcases hcs.eq_or_lt with hcs' | hcs'
  · exact Or.inl hcs'.symm
  · right
    refine ⟨s - c, ⟨⟨tsub_pos_of_lt hcs', ?_⟩, ?_⟩, tsub_add_cancel_of_le hcs⟩
    · intro hev
      apply hsd
      have ht : Tendsto (fun u : ℝ≥0 => u - c) (𝓝[<] s) (𝓝[<] (s - c)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact ((continuous_id.sub continuous_const).tendsto s).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with u hu
          have hu' : u < s := hu
          show u - c < s - c
          rcases le_or_gt u c with huc | huc
          · rw [tsub_eq_zero_of_le huc]; exact tsub_pos_of_lt hcs'
          · exact tsub_lt_tsub_right_of_le huc.le hu'
      have h3 := ht.eventually hev
      have h4 : ∀ᶠ u in 𝓝[<] s, c < u := by
        have : Ioo c s ∈ 𝓝[<] s := Ioo_mem_nhdsLT hcs'
        filter_upwards [this] with u hu using hu.1
      filter_upwards [h3, h4, self_mem_nhdsWithin] with u hu3 hu4 hu5
      have hu5' : u < s := hu5
      have hcnt : gluedCount σ u = N := by
        refine gluedCount_eq hm ?_ (lt_of_lt_of_le (by exact_mod_cast hu5') h2.le)
        rw [hcoe]; exact_mod_cast hu4.le
      have hgu : gluedWalk σ w u = w N (u - c) := by
        unfold gluedWalk; rw [hcnt, ← hc]
      have hgs : gluedWalk σ w s = w N (s - c) := by
        unfold gluedWalk; rw [← hN, ← hc]
      rw [hgu, hgs]; exact hu3
    · show s - c ≤ T
      exact (tsub_le_self).trans hsT'

section Regen

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk of a good environment is a regular path (right-continuous, finitely many
jumps on bounded intervals). -/
theorem isRegPath_regenWalk {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) :
    IsRegPath (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k ν) (t : ℝ)) := by
  refine ⟨regenWalk_rc hν, fun T => ?_⟩
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  set σ := partialSums fun k => ElboimSly.cycTreg (cycSlice k ν) with hσ
  have hm : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ, partialSums_succ]; exact le_self_add
  have h0 : σ 0 = 0 := by simp [hσ, partialSums]
  have hbdd := bdd_partialSums hb (τ := fun k => ElboimSly.cycTreg (cycSlice k ν))
    (fun k => regPlan_tau_ge _)
  have hfn : ∀ k (u : ℝ≥0), ElboimSly.cycWalk (cycSlice k ν) 0 0 (u : ℝ) =
      (envPath ν (regionData d k)).1.fn u := fun k u => by
    rw [(envPath_len (δ := regionData d k) (ν := ν) (hν k)).2]
    exact (envFn_regionData' ν k u).symm
  have := gluedWalk_fin hm h0 (fun t => hbdd t)
    (w := fun k s => ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ)) (fun k T => by
      have e : (fun s : ℝ≥0 => ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ)) =
          (envPath ν (regionData d k)).1.fn := funext (hfn k)
      rw [e]; exact (envPath ν (regionData d k)).1.fin T) T
  have e2 : gluedWalk σ (fun k s => ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ)) =
      fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k ν) (t : ℝ) :=
    funext fun t => gluedWalk_eq_regenWalk _ t
  rw [e2] at this
  exact this

end Regen

end ElboimSly.Paper.Escape

end
