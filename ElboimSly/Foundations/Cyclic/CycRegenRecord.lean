/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenThitEq
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncNth
public import ElboimSly.Foundations.Cyclic.CycRecLimit
public import Mathlib

/-!
# ES22 Lemma 2.1: the truncated record of the regeneration plan

ES22 Lemma 2.1, proof, "Freezing": the record `cycRec^{𝒫_reg}(t)` has
`k_t + 1` entries (`k_t = regenCount`), the entries `i < k_t` are complete pieces and the last one
is piece `k_t` cut at `L = t - α(t)`.

For a good environment `ν` and `t ≥ 0`, with `σ_i = regenSigma (cycSlice · ν) i`:
* `trunc_regPlan_nth`: entry `i` of `Trunc_t(ρ^{𝒫_reg}(ν))` is present iff `σ_i ≤ t`;
* `regPlan_num_trunc`: it has `k_t + 1` entries.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open CycSchemeEnv

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The slices `ν^0, ν^1, …` of an environment on `ℕ × S_β`. -/
noncomputable abbrev slices (ν : Measure (ℕ × RingSpace d β)) : ℕ → Measure (RingSpace d β) :=
  fun k => cycSlice k ν

omit [Fact (0 < β)] in
theorem regPlan_K : (regPlan d β).K = ⊤ := rfl

theorem regE_len {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (k : ℕ) :
    ((regPlan d β).E (rule (regPlan d β) ν) k).len = ElboimSly.cycTreg (cycSlice k ν) :=
  (regPlan_E_env hν k).1

theorem lam_regPlan {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (k : ℕ) :
    lam (regPlan d β) ν k = ElboimSly.regenSigma (slices ν) k := by
  unfold lam ElboimSly.regenSigma
  exact Finset.sum_congr rfl fun i _ => regE_len hν i

theorem cont_regPlan {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) {k : ℕ}
    (hk : ElboimSly.regenSigma (slices ν) k < ⊤) :
    (regPlan d β).Cont (rule (regPlan d β) ν) k := by
  refine ⟨by rw [regPlan_K]; exact_mod_cast ENat.natCast_lt_top k, fun i hi => ?_⟩
  rw [regE_len hν i]
  have : ElboimSly.cycTreg (cycSlice i ν) ≤ ElboimSly.regenSigma (slices ν) k := by
    unfold ElboimSly.regenSigma
    exact Finset.single_le_sum (f := fun j => ElboimSly.cycTreg (cycSlice j ν))
      (fun _ _ => zero_le) (Finset.mem_range.2 hi)
  exact lt_of_le_of_lt this hk

open scoped Classical in
theorem trunc_regPlan_nth {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (t : ℝ≥0)
    (k : ℕ) :
    (CycRec.trunc t ((regPlan d β).envFinal ν)).nth k =
      if ElboimSly.regenSigma (slices ν) k ≤ (t : ℝ≥0∞)
      then some (tgt (regPlan d β) ν t k) else none := by
  rw [trunc_envFinal_nth ((regPlan d β).junk) t k]
  simp only [lam_regPlan hν]
  by_cases h : ElboimSly.regenSigma (slices ν) k ≤ (t : ℝ≥0∞)
  · have hc := cont_regPlan hν (lt_of_le_of_lt h ENNReal.coe_lt_top)
    simp [h, hc]
  · simp [h]

theorem regenSigma_le_iff {ν : Measure (ℕ × RingSpace d β)} (t : ℝ≥0) (k : ℕ) :
    ElboimSly.regenSigma (slices ν) k ≤ (t : ℝ≥0∞) ↔ k ≤ ElboimSly.regenCount (slices ν) (t : ℝ) := by
  have := le_regenCount_iff (slices ν) t.2 k
  simpa using this.symm

end ElboimSly.Cyclic

end
