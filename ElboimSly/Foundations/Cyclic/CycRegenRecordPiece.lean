/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenRecord
public import ElboimSly.Foundations.Cyclic.CycMarkovRegion
public import Mathlib

/-!
# ES22 Lemma 2.1: the entries and the region of the truncated record

ES22 Lemma 2.1, proof, "Freezing" and "Case `L > 0`": the region `R_t` of
the truncated record `cycRec^{𝒫_reg}(t)` meets copy `k_t` in the region `ℛ_{(0,L]}(w)` of the
current piece `w = W^{ν^{k_t}}_{0,0}` and does not meet the copies `> k_t`
(`preimage_region_last`, `preimage_region_gt`).

* `regE_eq`: walk `k` of the environment final record is `(regionData d k, P^{ν^k}_{0,0} ∧ treg)`;
* `coord_last_trunc`, `num_trunc`: the truncated record has `k_t + 1` entries, the last one is
  piece `k_t` cut at `L = t - α(t)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open CycSchemeEnv

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace d β)}

theorem regE_eq (hν : CycGood ν) (k : ℕ) :
    (regPlan d β).E (rule (regPlan d β) ν) k =
      (regionData d k, (envPath ν (regionData d k)).cut (ElboimSly.cycTreg (cycSlice k ν))) := by
  set P := regPlan d β with hP
  set path : PathRule ℕ d := rule P ν with hpath
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
  unfold CycPlan.E CycPlan.nextEntry
  rw [hstop]; rfl

theorem regE_data (hν : CycGood ν) (k : ℕ) :
    ((regPlan d β).E (rule (regPlan d β) ν) k).data = regionData d k := by
  rw [regE_eq hν]; rfl

theorem envPath_fn_regionData (hν : CycGood ν) (k : ℕ) (r : ℝ≥0) :
    (envPath ν (regionData d k)).1.fn r = ElboimSly.cycWalk (cycSlice k ν) 0 0 (r : ℝ) := by
  rw [(envPath_len (δ := regionData d k) (hν k)).2]
  exact envFn_regionData ν k r

omit [Fact (0 < β)] in
theorem regionData_clock (k : ℕ) (r : ℝ≥0) :
    (regionData d k).clock β r = ((r : ℝ) : AddCircle β) := by
  simp [regionData, CycData.clock, CycData.phase, CycData.sgn, CycData.fwd]

/-- The region of piece `k` cut at `L ≤ treg`: `{k} × ℛ_{(0,L]}(W^{ν^k}_{0,0})`. -/
theorem region_cut_regE (hν : CycGood ν) (k : ℕ) {L : ℝ≥0}
    (hL : (L : ℝ≥0∞) ≤ ElboimSly.cycTreg (cycSlice k ν)) :
    (((regPlan d β).E (rule (regPlan d β) ν) k).cut (L : ℝ≥0∞)).region β =
      {k} ×ˢ cycRegion β (fun s => ElboimSly.cycWalk (cycSlice k ν) 0 0 s) 0 (L : ℝ) := by
  set q := (envPath ν (regionData d k)).1 with hq
  have hLL := fun {r : ℝ≥0} (hr : 0 < r) (z : Fin d → ℤ) =>
    isLeftLimitAbove_walk_iff (hν k) q (envPath_fn_regionData hν k) hr z
  have hleft : ∀ {r : ℝ≥0}, 0 < r → (r : ℝ≥0∞) ≤ L →
      ((((regPlan d β).E (rule (regPlan d β) ν) k).cut (L : ℝ≥0∞)).path).left r = q.left r := by
    intro r hr hrL
    rw [regE_eq hν k]
    show ((q.cut (ElboimSly.cycTreg (cycSlice k ν))).cut (L : ℝ≥0∞)).left r = _
    rw [CPath.left_cut _ _ hr hrL, CPath.left_cut _ _ hr (hrL.trans hL)]
  have hlen : (((regPlan d β).E (rule (regPlan d β) ν) k).cut (L : ℝ≥0∞)).len = L :=
    CycEntry.len_cut _ _
  have hdata : (((regPlan d β).E (rule (regPlan d β) ν) k).cut (L : ℝ≥0∞)).data.copy = k := by
    show ((regPlan d β).E (rule (regPlan d β) ν) k).data.copy = k
    rw [regE_data hν]; rfl
  have hclock : (((regPlan d β).E (rule (regPlan d β) ν) k).cut (L : ℝ≥0∞)).data.clock β =
      (regionData d k).clock β := by
    show ((regPlan d β).E (rule (regPlan d β) ν) k).data.clock β = _
    rw [regE_data hν]
  ext x
  obtain ⟨a, e, θ⟩ := x
  simp only [CycEntry.region, mem_prod, mem_singleton_iff, mem_ofPred_eq, cycRegion]
  constructor
  · rintro ⟨r, hr0, hrt, hk, hθ, hmem⟩
    rw [hlen] at hrt
    refine ⟨hk.trans hdata, r, by exact_mod_cast hr0, by exact_mod_cast hrt, ?_,
      q.left r, (hLL hr0 _).2 rfl, ?_⟩
    · rw [hθ, hclock, regionData_clock]
    · rwa [hleft hr0 hrt] at hmem
  · rintro ⟨hk, τ, hτ0, hτt, hθ, z, hz, hmem⟩
    have hτ0' : 0 < τ.toNNReal := Real.toNNReal_pos.2 hτ0
    have hτe : ((τ.toNNReal : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal _ hτ0.le
    have hrt' : τ.toNNReal ≤ L := by
      rw [← NNReal.coe_le_coe, hτe]; exact hτt
    rw [← hτe] at hz
    have hzl := (hLL hτ0' z).1 hz
    refine ⟨τ.toNNReal, hτ0', ?_, ?_, ?_, ?_⟩
    · rw [hlen]; exact_mod_cast hrt'
    · rw [hdata]; exact hk
    · rw [hθ, hclock, regionData_clock, hτe]
    · rw [hleft hτ0' (by exact_mod_cast hrt'), hzl]; exact hmem

/-- Entries of a complete piece lie in their own copy. -/
theorem region_regE_subset (hν : CycGood ν) (k : ℕ) {x : ℕ × RingSpace d β}
    (hx : x ∈ ((regPlan d β).E (rule (regPlan d β) ν) k).region β) : x.1 = k := by
  obtain ⟨r, -, -, h1, -⟩ := hx
  rw [h1]
  show ((regPlan d β).E (rule (regPlan d β) ν) k).data.copy = k
  rw [regE_data hν]; rfl

end ElboimSly.Cyclic

end
