/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvEvFin
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvLim
public import Mathlib

/-!
# The environment scheme (b), finite horizon: the limit entries

The environment scheme (b), convergence for finite `s_∘`.

* `limEntry_of_const`: if the stage entries of a chain are eventually a fixed entry (and the
  limiting jump times diverge), the limit entry is that entry.
* `Traj.lt_numLim_iff_fin`: entry `k` occurs in the limit iff `Cont k` and `Λ_k ≤ s_∘`.
* `tgt`: the entry `k` of `Trunc_{s_∘}(ρ^𝒫(ν))`; `Traj.limEntry_fin`: the limit entry `k` is `tgt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
/-- If the stage entries of entry `k` are eventually a fixed entry, the limit entry is that entry. -/
theorem limEntry_of_const {Θ : Type*} {ρ : ℕ → Θ → CycRec I d} (junk : CycEntry I d)
    (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) {k : ℕ} {ϑ : Θ}
    (hk : (k : ℕ∞) < numLim ρ ϑ) (hg : LimGood ρ junk k ϑ) (e0 : CycEntry I d) (J : ℕ)
    (hJ : ∀ j, J ≤ j → stageEntry ρ junk k j ϑ = e0) :
    limEntry junk hext k ϑ = e0 := by
  have hchain := stagePath_isChain hext junk ϑ hk
  have hgood' := LimGood.nnreal junk hg
  unfold limEntry
  rw [dite_eq_left ⟨hk, hg⟩]
  refine Prod.ext ?_ (Subtype.ext (CPath.ext' ?_ (funext fun t => ?_)))
  · show (stageEntry ρ junk k 0 ϑ).data = e0.data
    rw [← stageEntry_data hext junk ϑ hk J, hJ J le_rfl]
  · show (hchain.limPath hgood').len = e0.2.1.len
    rw [CPath.IsChain.limPath_len]
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · have : (stagePath ρ junk k ϑ j).len ≤ (stagePath ρ junk k ϑ (max j J)).len :=
        hchain.len_mono (le_max_left j J)
      have h2 : stagePath ρ junk k ϑ (max j J) = e0.2.1 := by
        show (stageEntry ρ junk k (max j J) ϑ).2.1 = _
        rw [hJ _ (le_max_right _ _)]
      rw [h2] at this
      exact this
    · refine le_iSup_of_le J ?_
      show _ ≤ (stageEntry ρ junk k J ϑ).2.1.len
      rw [hJ J le_rfl]
  · show (hchain.limPath hgood').fn t = e0.2.1.fn t
    rw [CPath.IsChain.limPath_fn]
    obtain ⟨J', hJ'⟩ := hchain.limFn_spec hgood' t
    rw [hJ' (max J J') (le_max_right _ _) t le_rfl]
    show (stageEntry ρ junk k (max J J') ϑ).2.1.fn t = _
    rw [hJ _ (le_max_left _ _)]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem shape_num (k : ℕ) (r : ℝ≥0) : (shape P ν k r).num = ((k + 1 : ℕ) : ℕ∞) := rfl

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem shape_k_eq {k k' : ℕ} {r r' : ℝ≥0} (h : shape P ν k r = shape P ν k' r') : k = k' := by
  have := congrArg CycRec.num h
  rw [shape_num, shape_num] at this
  exact_mod_cast Nat.succ_injective (Nat.cast_injective (R := ℕ∞) this)

variable (T : Traj P sc ν)

/-- An entry of a record of the trajectory comes from a walk of the recursion within the budget. -/
theorem Traj.cont_of_nth (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) {j k : ℕ}
    {e : CycEntry I d} (h : (T.S j).1.nth k = some e) : P.Cont (rule P ν) k ∧ lam P ν k ≤ sc := by
  have key : ∀ k' r', (T.S j).1 = shape P ν k' r' → P.Cont (rule P ν) k' →
      lam P ν k' + r' ≤ sc → P.Cont (rule P ν) k ∧ lam P ν k ≤ sc := by
    intro k' r' hs hc hb
    have hkk : k ≤ k' := by
      by_contra hlt
      rw [hs, nth_shape_gt k' r' (not_le.1 hlt)] at h
      exact absurd h (by simp)
    exact ⟨CycPlan.Cont.anti P (rule P ν) hkk hc,
      (lam_mono hkk).trans (le_self_add.trans hb)⟩
  have hB := T.bud hν hK h0 j
  rcases T.inv hν hK h0 j with ⟨hf, k', r', hE⟩ | ⟨ht, k', r', hrec, hall, hlt, -, -⟩
  · exact key k' r' hE.eq_shape ⟨hE.lt_K, hE.allFin⟩ (hB.1 hf k' r' hE)
  · obtain ⟨k'', r'', hs'', -, hb'', -⟩ := hB.2 ht
    have hs : (T.S j).1 = shape P ν k' r' := hrec
    have hk := shape_k_eq (hs.symm.trans hs'')
    subst hk
    exact key k' r'' hs'' ⟨hlt, hall⟩ hb''

end CycSchemeEnv
end ElboimSly.Cyclic

end
