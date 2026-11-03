/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.GeometricDet
public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe
public import ElboimSly.Foundations.Cyclic.CycEvents
public import ElboimSly.Foundations.Cyclic.CycClosing
public import Mathlib

/-!
# Pieces of the regenerated walk: events and a regeneration at a closing time

Geometric domination of regenerations. The setting is construction (i) of the constructions of the regenerated walk: the pieces
of the regenerated walk are the copies `N^k` (`cycSlice k (N ω)`) of a `PPP(# ⊗ μ_β)`. This file
gives the measurable events `{N^j good, t_reg(N^j) ≤ T}` with their independence and common
probability, and the step of (a): on `{t_reg^{(1)} = iβ}` the regenerated walk is at `0` at time `iβ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]

/-- The environments of the pieces: piece `k + 1` uses `N^k`. -/
@[reducible] noncomputable def geoSlices (N : Ω → Measure (ℕ × RingSpace d β)) (ω : Ω) :
    ℕ → Measure (RingSpace d β) := fun k => cycSlice k (N ω)

/-- The event `{N^j` good and `t_reg(N^j) ≤ T}`. -/
def geoTregLe (N : Ω → Measure (ℕ × RingSpace d β)) (T : ℝ) (j : ℕ) : Set Ω :=
  (fun ω => cycSlice j (N ω)) ⁻¹' {ν | Good ν ∧ cycTreg ν ≤ ENNReal.ofReal T}

/-- The event `{N^j` good and `t_reg(N^j) < ∞}`. -/
def geoTregFin (N : Ω → Measure (ℕ × RingSpace d β)) (j : ℕ) : Set Ω :=
  (fun ω => cycSlice j (N ω)) ⁻¹' {ν | Good ν ∧ cycTreg ν < ⊤}

section ppp

variable {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
  (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
include hN

theorem measure_geoTregLe (T : ℝ) (j : ℕ) : P (geoTregLe N T j) = P (geoTregLe N T 0) := by
  have h := (isPoissonPointProcess_slice hN 0).map_eq_map (isPoissonPointProcess_slice hN j)
  have hm := measurableSet_cycTreg_le (d := d) (β := β) T
  have e1 := congrArg (fun m => m {ν | Good ν ∧ cycTreg ν ≤ ENNReal.ofReal T}) h
  simp only [Measure.map_apply (isPoissonPointProcess_slice hN j).measurable hm,
    Measure.map_apply (isPoissonPointProcess_slice hN 0).measurable hm] at e1
  exact e1

theorem measure_geoTregFin (j : ℕ) : P (geoTregFin N j) = P (geoTregFin N 0) := by
  have h := (isPoissonPointProcess_slice hN 0).map_eq_map (isPoissonPointProcess_slice hN j)
  have hm := measurableSet_cycTreg_lt_top (d := d) (β := β)
  have e1 := congrArg (fun m => m {ν | Good ν ∧ cycTreg ν < ⊤}) h
  simp only [Measure.map_apply (isPoissonPointProcess_slice hN j).measurable hm,
    Measure.map_apply (isPoissonPointProcess_slice hN 0).measurable hm] at e1
  exact e1

theorem measure_inter_geoTregLe (T : ℝ) (J : Finset ℕ) :
    P (⋂ j ∈ J, geoTregLe N T j) = P (geoTregLe N T 0) ^ J.card := by
  have h := (iIndepFun_slice hN).measure_inter_preimage_eq_mul J
    (sets := fun _ => {ν | Good ν ∧ cycTreg ν ≤ ENNReal.ofReal T})
    (fun _ _ => measurableSet_cycTreg_le T)
  have e : ∏ i ∈ J, P ((fun ω => cycSlice i (N ω)) ⁻¹'
      {ν | Good ν ∧ cycTreg ν ≤ ENNReal.ofReal T}) = ∏ _i ∈ J, P (geoTregLe N T 0) :=
    Finset.prod_congr rfl (fun j _ => measure_geoTregLe hN T j)
  simp only [geoTregLe] at e ⊢
  rw [h, e, Finset.prod_const]

theorem measure_inter_geoTregFin (k : ℕ) :
    P (⋂ j ∈ Finset.range k, geoTregFin N j) = P (geoTregFin N 0) ^ k := by
  have h := (iIndepFun_slice hN).measure_inter_preimage_eq_mul (Finset.range k)
    (sets := fun _ => {ν | Good ν ∧ cycTreg ν < ⊤})
    (fun _ _ => measurableSet_cycTreg_lt_top)
  have e : ∏ i ∈ Finset.range k, P ((fun ω => cycSlice i (N ω)) ⁻¹'
      {ν | Good ν ∧ cycTreg ν < ⊤}) = ∏ _i ∈ Finset.range k, P (geoTregFin N 0) :=
    Finset.prod_congr rfl (fun j _ => measure_geoTregFin hN j)
  simp only [geoTregFin] at e ⊢
  rw [h, e, Finset.prod_const, Finset.card_range]

end ppp

/-- On `{t_reg^{(1)} = nβ}` (all pieces good), the regenerated walk is at `0` at time `nβ`. -/
theorem regenWalk_at_treg {ν : ℕ → Measure (RingSpace d β)} (hg : ∀ k, Good (ν k)) {n : ℕ}
    (hn : ElboimSly.cycTreg (ν 0) = ENNReal.ofReal ((n : ℝ) * β)) :
    ElboimSly.regenWalk ν ((n : ℝ) * β) = 0 := by
  have hβ : 0 < β := Fact.out
  have hnn : 0 ≤ (n : ℝ) * β := by positivity
  have s1 : ElboimSly.regenSigma ν 1 = ENNReal.ofReal ((n : ℝ) * β) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, regenSigma_succ, regenSigma_zero, zero_add, hn]
  have s2 : ENNReal.ofReal ((n : ℝ) * β) < ElboimSly.regenSigma ν (1 + 1) := by
    rw [regenSigma_succ, s1]
    refine ENNReal.lt_add_right ENNReal.ofReal_ne_top ?_
    exact (ne_of_gt (lt_of_lt_of_le (by simpa using hβ) (regPlan_tau_ge (ν 1))))
  have hc : ElboimSly.regenCount ν ((n : ℝ) * β) = 1 :=
    regenCount_eq ν hnn s1.le s2
  have hs : ElboimSly.regenStart ν ((n : ℝ) * β) = (n : ℝ) * β := by
    unfold ElboimSly.regenStart
    rw [hc, s1, ENNReal.toReal_ofReal hnn]
  unfold ElboimSly.regenWalk
  rw [hc, hs, sub_self]
  exact cycWalk_zero (hg 1) 0 0

/-- If `t_reg^{(1)} ≤ T` (all pieces good), the regenerated walk is `0` at some time `iβ` with
`1 ≤ i ≤ T/β`. -/
theorem exists_regenWalk_zero_of_treg_le {ν : ℕ → Measure (RingSpace d β)}
    (hg : ∀ k, Good (ν k)) {T : ℝ} (hT : 0 < T)
    (h : ElboimSly.cycTreg (ν 0) ≤ ENNReal.ofReal T) :
    ∃ i ∈ Finset.Icc 1 ⌊T / β⌋₊, ElboimSly.regenWalk ν ((i : ℝ) * β) = 0 := by
  have hβ : 0 < β := Fact.out
  obtain ⟨n, hn1, -, hne⟩ := exists_cycTreg_eq (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  refine ⟨n, Finset.mem_Icc.2 ⟨hn1, Nat.le_floor ?_⟩, regenWalk_at_treg hg hne⟩
  rw [le_div_iff₀ hβ]
  rw [hne, ENNReal.ofReal_le_ofReal_iff hT.le] at h
  exact h

end ElboimSly.Cyclic

end
