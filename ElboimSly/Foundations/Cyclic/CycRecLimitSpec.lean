/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRecLimitMeas
public import Mathlib

/-!
# Measurability of record functionals (e): the limit record has the limiting data

Measurability of record functionals (e). On `Θ_0` the limit record `Φ(ϑ)` has `numLim` entries, each
`ρ_j(ϑ)` is extended by it, and its entries have the limiting datum, length `⨆_j ℓ_j` and jump times
`τ_a = ⨅_j ς_a(p_j)`. In particular a record whose entries are extended by all `ρ_j(ϑ)` and have the
same limiting jump lists equals `Φ(ϑ)` (`CPath.jumpList_injective`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {Θ : Type*} {ρ : ℕ → Θ → CycRec I d}
  (junk : CycEntry I d) (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ))

omit [MeasurableSpace I] in
theorem firstStage_le {ϑ : Θ} {k j : ℕ} (hk : (k : ℕ∞) < (ρ j ϑ).num) :
    firstStage ρ k ϑ ≤ j := by
  classical
  have hex : ∃ j, (k : ℕ∞) < (ρ j ϑ).num := ⟨j, hk⟩
  unfold firstStage
  rw [dite_eq_left hex]
  exact Nat.find_min' hex hk

omit [MeasurableSpace I] in
theorem recLim_nth {ϑ : Θ} (hϑ : ϑ ∈ thetaZero ρ junk) {k : ℕ} (hk : (k : ℕ∞) < numLim ρ ϑ) :
    (recLim junk hext ϑ).nth k = some (limEntry junk hext k ϑ) := by
  classical
  unfold recLim
  rw [ite_eq_left hϑ]
  by_cases ht : numLim ρ ϑ = ⊤
  · rw [ite_eq_left ht]; simp [CycRec.nth]
  · rw [ite_eq_right ht]
    have : k < (numLim ρ ϑ).toNat := by
      have := ENat.natCast_toNat ht
      rw [← this] at hk
      exact_mod_cast hk
    simp [CycRec.nth, this]

omit [MeasurableSpace I] in
/-- The limit record is extended by every `ρ_j(ϑ)`. -/
theorem extends_recLim {ϑ : Θ} (hϑ : ϑ ∈ thetaZero ρ junk) (j : ℕ) :
    (ρ j ϑ).Extends (recLim junk hext ϑ) := by
  intro k e he
  have hkj : (k : ℕ∞) < (ρ j ϑ).num := lt_num_of_nth he
  have hk : (k : ℕ∞) < numLim ρ ϑ := lt_numLim_iff.mpr ⟨j, hkj⟩
  refine ⟨limEntry junk hext k ϑ, recLim_nth junk hext hϑ hk, ?_⟩
  have hfs : firstStage ρ k ϑ ≤ j := firstStage_le hkj
  have hent : stageEntry ρ junk k j ϑ = e := by
    have h1 := stageEntry_nth hext junk ϑ hk j
    rw [max_eq_left hfs, he] at h1
    exact (Option.some.inj h1).symm
  have hgood := hϑ k hk
  have hchain := stagePath_isChain hext junk ϑ hk
  have hlim : limEntry junk hext k ϑ =
      ((stageEntry ρ junk k 0 ϑ).data,
        ⟨hchain.limPath (LimGood.nnreal junk hgood),
          unitJumps_limPath hchain (LimGood.nnreal junk hgood)
            (fun j => (stageEntry ρ junk k j ϑ).2.2)⟩) := by
    unfold limEntry
    exact dite_eq_left ⟨hk, hgood⟩
  rw [hlim]
  refine ⟨?_, ?_⟩
  · rw [← hent]; exact stageEntry_data hext junk ϑ hk j
  · have := hchain.isPiece_limPath (LimGood.nnreal junk hgood) j
    rw [← hent]
    exact this

end ElboimSly.Cyclic

end
