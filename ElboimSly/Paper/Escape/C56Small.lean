/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56LastProb
public import Mathlib

/-!
# ES22 Claim 5.6, the case `4^j ≤ β`

ES22 Claim 5.6, "Case `4^j ≤ β`" (ES22 Claim 5.6).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.SRW

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}

theorem escFace_subset {j : ℕ} {u z : Fin (k + 2) → ℤ} {v : Fin (k + 2) → ℤ}
    (hgeom : EscGeom j u v z) : z ∈ escBlockMinus j u := by
  have hj := hgeom.hj
  refine ⟨?_, fun c hc => ?_⟩
  · have := hgeom.hz.1
    have h2 : (0 : ℤ) < 2 ^ (j - 1) := by positivity
    constructor <;> omega
  · have h1 := (hgeom.zc hc)
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    constructor
    · have : ((u c : ℤ) : ℝ) ≤ z c := by linarith [h1.1]
      exact_mod_cast this
    · have : (z c : ℝ) < ((u c + 2 ^ j : ℤ) : ℝ) := by push_cast; linarith [h1.2]
      exact_mod_cast this

omit mΩ in
theorem avoidWalk_zero_time {ω : Ω} (hν : ∀ l, Good (avoidEnv N ω l)) :
    avoidWalk N ω 0 = 0 := by
  have hβ : 0 < β := Fact.out
  have hlt : ENNReal.ofReal (0 : ℝ) < cycTreg (avoidEnv N ω 0) := by
    rw [ENNReal.ofReal_zero]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hβ) (le_cycTreg _)
  have hc : regenCount (avoidEnv N ω) 0 = 0 := regenCount_eq_zero hlt
  have hs : regenStart (avoidEnv N ω) 0 = 0 := regenStart_eq_zero_of_lt_treg le_rfl hlt
  show regenWalk (avoidEnv N ω) 0 = 0
  unfold regenWalk
  rw [hc, hs, sub_zero]
  exact cycWalk_zero (hν 0) 0 0


/-- **The case `4^j ≤ β`.** -/
theorem small_case (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr) {j : ℕ}
    {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {t : ℝ} (hβj : (4 : ℝ) ^ j ≤ β)
    (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j) :
    ENNReal.ofReal (cBox ^ (k + 2) / ((2 : ℝ) ^ j) ^ ((k + 2) * CBox)) ≤
      Pr {ω | Esc56Event β j u v z t (escYv N v ω)} := by
  have := hN.isProbabilityMeasure
  have hβ0 : 0 < β := Fact.out
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have htβ : t ≤ β := ht2.trans hβj
  set R : ℝ≥0 := t.toNNReal with hRdef
  have hRc : (R : ℝ) = t := Real.coe_toNNReal _ ht0.le
  have hv : v ∈ claimBox (d := k + 2) u j := by rw [claimBox_eq]; exact hgeom.hvm
  have hw : z ∈ claimBox (d := k + 2) u j := by rw [claimBox_eq]; exact escFace_subset hgeom
  have hker := claim56_small_kernel (d := k + 2) (by have := hgeom.hj; omega) u hv hw
    (t := R) (by rw [hRc]; exact ht1) (by rw [hRc]; exact ht2)
  have hkerP := prob_ker_regen hN (R := R) (by rw [hRc]; exact htβ) (claimBox u j) v z
  have hvz : v ≠ z := by
    intro h
    have := hgeom.norm_vz_ge
    rw [h, sub_self, norm_zero] at this
    have h6 : (2 : ℝ) ^ 6 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hgeom.hj
    linarith
  refine le_trans (ENNReal.ofReal_le_ofReal hker) ?_
  rw [← hkerP]
  refine measure_mono_ae ?_
  filter_upwards [ae_cycNgood_eq hN] with ω hω hmem
  obtain ⟨hz, hQ⟩ := hmem
  have hgood : ∀ l, Good (avoidEnv N ω l) := by
    intro l; rw [avoidEnv_eq_cycSlice, ← hω]; exact cycGood_cycNgood N ω l
  have hy : ∀ s : ℝ, escYv N v ω s = v + escW N ω s.toNNReal := fun s => rfl
  have hgood' : ∀ l, Good (avoidEnv (cycNgood N) ω l) := by
    intro l; rw [avoidEnv_eq_cycSlice]; exact cycGood_cycNgood N ω l
  have hW0 : escW N ω 0 = 0 := avoidWalk_zero_time (N := cycNgood N) hgood'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hy, show t.toNNReal = R from rfl]; exact hz
  · intro s hs0 hst
    rw [hy]
    have := hQ s.toNNReal (Real.toNNReal_le_toNNReal hst)
    rw [claimBox_eq] at this
    exact this
  · intro s hs hst heq
    have hsR : s = t := by linarith
    rw [hsR, hy, show t.toNNReal = R from rfl, hz] at heq
    exact hvz heq.symm
  · intro s hs0 hst heq
    have hs : s = 0 := by linarith
    rw [hs, hy, Real.toNNReal_zero, hW0, add_zero] at heq
    exact hvz heq

end ElboimSly.Paper.Escape

end
