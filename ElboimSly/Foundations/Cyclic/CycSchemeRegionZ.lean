/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeRegionId
public import Mathlib

/-!
# The explored-region identity `Z_j(η) = cycReg(ρ_j(η))`

The environment scheme (a), "explored region" paragraph.

* `CycScheme.region_upd_eq_probe`: the one-step identity
  `cycReg(ρ_{j+1}) = cycReg(ρ_j) ∪ {x ∉ cycReg(ρ_j) : R_j(x) ≤ min(r', h_j)}`, the recursion of
  `ExplScheme.Z` for the pure scheme.
* `CycScheme.wf_stateAt`: every state along a history is well formed.
* `CycScheme.Z_eq_region`: for any `ExplScheme` whose raw probes and horizons are those of the pure
  scheme (`probeR`, `hOf` of the states `stateAt`), `sch.Z k η = cycReg (ρ_k(η))`.
* `CycScheme.Rt_eq_probeM`: the masked probe is the segment probe with mask `cycReg(ρ_k(η))`, i.e.
  the raw probe restricted to the unexplored region.
* `CycScheme.region_stateAt_mono`: the regions grow along the history.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

namespace CycScheme

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  (P : CycPlan I d β) (sc : ℝ≥0∞)

omit [Fact (0 < β)] in
theorem wf_init : WF (init P : State I d) := by
  refine ⟨0, CycRec.snoc (fun i : Fin 0 => i.elim0) (P.startOf CycRec.empty).newEntry, rfl, ?_⟩
  have : CycRec.snoc (fun i : Fin 0 => i.elim0) (P.startOf CycRec.empty).newEntry (Fin.last 0) =
      (P.startOf CycRec.empty).newEntry := Fin.snoc_last _ _
  rw [this]; exact newEntry_len_ne_top _

omit [Fact (0 < β)] in
/-- The initial record has empty region (`ρ_0` has length `0`). -/
theorem region_init : (init P : State I d).1.region β = ∅ := by
  have h := CycRec.region_push_inl (β := β) (Fin.elim0 : Fin 0 → CycEntry I d)
    (P.startOf CycRec.empty).newEntry
  refine h.trans ?_
  rw [newEntry_region]
  ext x
  simp [CycRec.mem_region_inl]

theorem wf_stateAt [Countable I] [MeasurableSingletonClass I] {U : Type*} [MeasurableSpace U] :
    ∀ (k : ℕ) (η : Hist U (CycS I d β) k), WF (stateAt P sc k η)
  | 0, _ => wf_init P
  | k + 1, η => (WF.region_upd (P := P) (sc := sc) (wf_stateAt k η.init) η.last).2

variable [Countable I] [MeasurableSingletonClass I]

/-- The one-step identity: the recursion of `ExplScheme.Z` for the pure scheme. -/
theorem region_upd_eq_probe {st : State I d} (hW : WF st) (o : Outcome (CycS I d β)) :
    (upd P sc st o).1.region β = st.1.region β ∪
      {x | x ∉ st.1.region β ∧ probeR P sc st x ≤ min o.1 (hOf P sc st : ℝ≥0∞)} := by
  have hne : min o.1 (hOf P sc st : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hmin : min o.1 (hOf P sc st : ℝ≥0∞) = (sStar P sc st o : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hne).symm
  have hle : sStar P sc st o ≤ hOf P sc st := by
    have : (sStar P sc st o : ℝ≥0∞) ≤ (hOf P sc st : ℝ≥0∞) := hmin ▸ min_le_right _ _
    exact_mod_cast this
  rw [(WF.region_upd (P := P) (sc := sc) hW o).1]
  ext x
  have key := probeR_le_iff P sc st hle x
  simp only [Set.mem_union, Set.mem_ofPred_eq, hmin, key]
  by_cases hx : x ∈ st.1.region β <;> simp [hx]

/-- The environment scheme (a): `𝒵_k(η) = cycReg(ρ_k(η))` for every exploration scheme
whose raw probes and horizons are those of the pure scheme. -/
theorem Z_eq_region {U : Type*} [MeasurableSpace U] (sch : ExplScheme (cycIntensity I d β) U)
    (hR : ∀ k η, sch.R k η = probeR P sc (stateAt P sc k η))
    (hh : ∀ k η, sch.h k η = hOf P sc (stateAt P sc k η)) :
    ∀ (k : ℕ) (η : Hist U (CycS I d β) k), sch.Z k η = (stateAt P sc k η).1.region β
  | 0, _ => by
      show (∅ : Set _) = _
      exact (region_init P).symm
  | k + 1, η => by
      have ih := Z_eq_region sch hR hh k η.init
      show sch.Z k η.init ∪ {x | x ∉ sch.Z k η.init ∧
        sch.R k η.init x ≤ min η.last.1 (sch.h k η.init)} = _
      rw [ih, hR, hh]
      exact (region_upd_eq_probe P sc (wf_stateAt P sc k η.init) η.last).symm

/-- The masked probe of step `k` is the segment probe with mask `cycReg(ρ_k(η))`. -/
theorem Rt_eq_probeM {U : Type*} [MeasurableSpace U] (sch : ExplScheme (cycIntensity I d β) U)
    (hR : ∀ k η, sch.R k η = probeR P sc (stateAt P sc k η))
    (hh : ∀ k η, sch.h k η = hOf P sc (stateAt P sc k η)) (k : ℕ) (η : Hist U (CycS I d β) k) :
    sch.Rt k η = probeM P sc (stateAt P sc k η) := by
  funext x
  classical
  rw [probeM_eq, ExplScheme.Rt, Z_eq_region P sc sch hR hh k η, hR]

/-- Regions grow along the history. -/
theorem region_stateAt_mono {U : Type*} [MeasurableSpace U] (k : ℕ) (η : Hist U (CycS I d β) (k + 1)) :
    (stateAt P sc k η.init).1.region β ⊆ (stateAt P sc (k + 1) η).1.region β := by
  show _ ⊆ (upd P sc (stateAt P sc k η.init) η.last).1.region β
  rw [region_upd_eq_probe P sc (wf_stateAt P sc k η.init) η.last]
  exact Set.subset_union_left

end CycScheme

end ElboimSly.Cyclic

end
