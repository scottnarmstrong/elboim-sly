/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenDriven
public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Frozen.Defs.RegenWalk
public import Mathlib

/-!
# The constructions of the regenerated walk (i): `W_reg` of the environment final record (deterministic part)

The constructions of the regenerated walk (i). For a good environment `ν` on `ℕ × S_β`, walk `k` of the
environment final record of `regPlan` is the cyclic walk of the slice `ν^k`, up to its closing
time `cycTreg (ν^k)`. Hence `W_reg` of the record is the gluing of these pieces
(`regRecWalk_envFinal`), which is the regenerated walk `regenWalk` of the slices
(`regRecWalk_envFinal_eq_regenWalk`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem envMeasure_regionData (ν : Measure (ℕ × RingSpace d β)) (k : ℕ) :
    envMeasure ν (regionData d k) = cycSlice k ν := by
  simp [envMeasure, regionData, CycData.fwd, CycData.copy]

omit [Fact (0 < β)] in
/-- The environment path of walk data `(k, 0, 0, +1)` is the cyclic walk of the slice `ν^k`. -/
theorem envFn_regionData (ν : Measure (ℕ × RingSpace d β)) (k : ℕ) (s : ℝ≥0) :
    envFn ν (regionData d k) s = ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ) := by
  unfold envFn ElboimSly.cycWalk
  have h0 : (0 : ℝ) ≤ s := s.2
  simp only [h0, ↓reduceIte]
  rw [envMeasure_regionData, Real.toNNReal_coe]
  simp [regionData, CycData.start, CycData.sgn, CycData.phase, CycData.fwd]

theorem pathTreg_cycWalk (μ : Measure (RingSpace d β)) :
    pathTreg β.toNNReal (fun s : ℝ≥0 => ElboimSly.cycWalk μ 0 0 (s : ℝ)) =
      ElboimSly.cycTreg μ := by
  have hβ : 0 < β := Fact.out
  have hc : ∀ j : ℕ, (((j : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ) = (j : ℝ) * β := fun j => by
    push_cast; rw [Real.coe_toNNReal β hβ.le]
  unfold pathTreg ElboimSly.cycTreg
  apply le_antisymm
  · refine le_iInf fun k => ?_
    have hk : ElboimSly.cycWalk μ 0 0 (((k.1 : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ) = 0 := by
      rw [hc]; exact k.2.2
    refine iInf_le_of_le ⟨k.1, k.2.1, hk⟩ (le_of_eq ?_)
    rw [← ENNReal.ofReal_coe_nnreal, hc]
  · refine le_iInf fun k => ?_
    have h1 : ElboimSly.cycWalk μ 0 0 (((k.1 : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ) = 0 := k.2.2
    rw [hc] at h1
    refine iInf_le_of_le ⟨k.1, k.2.1, h1⟩ (le_of_eq ?_)
    rw [← ENNReal.ofReal_coe_nnreal, hc]

/-- Walk `k` of the environment final record of `𝒫_reg` is the cyclic walk of the slice `ν^k`
up to its closing time. -/
theorem regPlan_E_env {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (k : ℕ) :
    ((regPlan d β).E (fun k ρ => envPath ν ((regPlan d β).start k ρ)) k).len =
        ElboimSly.cycTreg (cycSlice k ν) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ElboimSly.cycTreg (cycSlice k ν) →
        ((regPlan d β).E (fun k ρ => envPath ν ((regPlan d β).start k ρ)) k).path.fn s =
          ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ) := by
  set P := regPlan d β with hP
  set path : PathRule ℕ d := fun k ρ => envPath ν (P.start k ρ) with hpath
  have hfn : (path k (P.ideal path k)).1.fn = fun s : ℝ≥0 =>
      ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ) := by
    show (envPath ν (regionData d k)).1.fn = _
    rw [(envPath_len (δ := regionData d k) (hν k)).2]
    funext s
    exact envFn_regionData ν k s
  have hstop : P.stopLen k (P.ideal path k) (path k (P.ideal path k)) =
      ElboimSly.cycTreg (cycSlice k ν) := by
    show (closingPlan β ⊤ _ _).stopLen _ _ _ = _
    rw [closingPlan_stopLen, hfn]
    exact pathTreg_cycWalk _
  have hE : P.E path k = (regionData d k, (path k (P.ideal path k)).cut
      (ElboimSly.cycTreg (cycSlice k ν))) := by
    unfold CycPlan.E CycPlan.nextEntry
    rw [hstop]; rfl
  refine ⟨?_, fun s hs => ?_⟩
  · rw [hE]
    show ((path k (P.ideal path k)).1.cut _).len = _
    rw [CPath.cut_len]
  · rw [hE]
    show ((path k (P.ideal path k)).1.cut _).fn s = _
    rw [CPath.cut_fn, min_eq_left hs, ENNReal.toNNReal_coe, hfn]

theorem regPlan_tau_ge (μ : Measure (RingSpace d β)) :
    (β.toNNReal : ℝ≥0∞) ≤ ElboimSly.cycTreg μ := by
  have hβ : 0 < β := Fact.out
  refine le_iInf fun k => ?_
  have hk : (1 : ℝ) ≤ k.1 := by exact_mod_cast k.2.1
  show ENNReal.ofReal β ≤ _
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- **the constructions of the regenerated walk (i)**: `W_reg` of the environment final record of `𝒫_reg` is the gluing
of the cyclic walks of the slices `ν^k` at the partial sums of the closing times, for a good
environment. -/
theorem regRecWalk_envFinal {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (t : ℝ≥0) :
    regRecWalk ((regPlan d β).envFinal ν) t =
      gluedWalk (partialSums fun k => ElboimSly.cycTreg (cycSlice k ν))
        (fun k s => ElboimSly.cycWalk (cycSlice k ν) 0 0 (s : ℝ)) t :=
  (regPlan d β).regRecWalk_cycFinal (fun k ρ => envPath ν ((regPlan d β).start k ρ)) rfl
    (Real.toNNReal_pos.2 Fact.out) _ _ (fun _ => regPlan_tau_ge _)
    (fun k _ => regPlan_E_env hν k) t

end ElboimSly.Cyclic

end
