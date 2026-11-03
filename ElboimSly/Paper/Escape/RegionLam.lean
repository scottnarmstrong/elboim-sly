/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.LamStopping
public import Mathlib

/-!
# The explored region at the time `Λ_k`

The connecting plan; ES22 Lemma 5.5 ("`R_{S₂}`", "`D_{S₃}`").

At the time `Λ_k` the explored region is the union of the regions of the first `k` world-lines
(the `k`-th and later entries have been explored for time `0` only and contribute nothing):

* `region_cut_zero`: the region of a world-line cut at length `0` is empty;
* `region_trunc_lam_subset`: `R(Trunc_{Λ_k}(ρ)) ⊆ ⋃_{m<k} region(E m)`;
* `cycRegionStop_lamT_subset`: the same for `cycRegionStop` at the stopping time `lamT`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

theorem region_eq_empty_of_len_zero (e : CycEntry I d) (h : e.len = 0) : e.region β = ∅ := by
  ext x
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨r, hr, hl, -⟩
  rw [h] at hl
  have : (r : ℝ≥0∞) = 0 := le_antisymm hl zero_le
  exact absurd (by exact_mod_cast this) hr.ne'

theorem cut_len_entry (e : CycEntry I d) (t : ℝ≥0∞) : (e.cut t).len = t :=
  cycPath_cut_len e.2 t

theorem region_trunc_lam_subset {P : CycPlan I d β} (hP : PlanFin P) {ν : Measure (CycS I d β)}
    (hν : CycGood ν) {k : ℕ} (hk : (k : ℕ∞) ≤ P.K) :
    (CycRec.trunc (lam P ν k).toNNReal (P.envFinal ν)).region β ⊆
      ⋃ m ∈ Finset.range k, (P.E (rule P ν) m).region β := by
  classical
  have hlamfin : lam P ν k ≠ ⊤ :=
    lam_ne_top (fun i hi => hP ν hν i (lt_of_lt_of_le (by exact_mod_cast hi) hk))
  set s := (lam P ν k).toNNReal with hs
  have hse : (s : ℝ≥0∞) = lam P ν k := ENNReal.coe_toNNReal hlamfin
  rintro x ⟨e, ⟨i, hi⟩, hx⟩
  have hnth := trunc_envFinal_nth (P := P) (ν := ν) P.junk s i
  rw [hi] at hnth
  by_cases hc : P.Cont (rule P ν) i ∧ lam P ν i ≤ (s : ℝ≥0∞)
  · rw [ite_eq_left hc] at hnth
    obtain rfl : e = tgt P ν s i := Option.some.inj hnth
    by_cases hik : i < k
    · have : tgt P ν s i = P.E (rule P ν) i := by
        unfold tgt; rw [ite_eq_left]
        rw [← lam_succ, hse]
        exact lam_mono (Nat.succ_le_of_lt hik)
      rw [this] at hx
      simp only [mem_iUnion, Finset.mem_range]
      exact ⟨i, hik, hx⟩
    · exfalso
      have hki : k ≤ i := not_lt.1 hik
      have hle : lam P ν i = lam P ν k := by
        refine le_antisymm (by rw [← hse]; exact hc.2) (lam_mono hki)
      unfold tgt at hx
      split_ifs at hx with hcc
      · have hlen : (P.E (rule P ν) i).len = 0 := by
          have h1 : lam P ν i + (P.E (rule P ν) i).len ≤ lam P ν i := by
            rwa [hse, ← hle] at hcc
          have hl : lam P ν i ≠ ⊤ := by rw [hle]; exact hlamfin
          have h1' : lam P ν i + (P.E (rule P ν) i).len ≤ lam P ν i + 0 := by simpa using h1
          exact le_antisymm (ENNReal.le_of_add_le_add_left hl h1') zero_le
        rw [region_eq_empty_of_len_zero _ hlen] at hx
        exact hx
      · rw [hse, ← hle, tsub_self] at hx
        rw [region_eq_empty_of_len_zero _ (by rw [cut_len_entry])] at hx
        exact hx
  · rw [ite_eq_right hc] at hnth
    exact absurd hnth (by simp)

theorem cycRegionStop_lamT_subset {Ω : Type*} [MeasurableSpace Ω] {P : CycPlan I d β} (hP : PlanFin P)
    (N : Ω → Measure (CycS I d β)) {k : ℕ} (hk : (k : ℕ∞) ≤ P.K) (ω : Ω) :
    cycRegionStop P (cycNgood N) (lamT P N k) ω ⊆
      ⋃ m ∈ Finset.range k, (P.E (rule P (cycNgood N ω)) m).region β := by
  have hν := cycGood_cycNgood N ω
  have hfin : lam P (cycNgood N ω) k ≠ ⊤ :=
    lam_ne_top (fun i hi => hP _ hν i (lt_of_lt_of_le (by exact_mod_cast hi) hk))
  have : lamT P N k ω = (((lam P (cycNgood N ω) k).toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
    (ENNReal.coe_toNNReal hfin).symm
  unfold cycRegionStop
  rw [this]
  exact region_trunc_lam_subset hP hν hk

end ElboimSly.Paper.Escape
