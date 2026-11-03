/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Good
public import ElboimSly.Foundations.Brownian.SchauderCov
import Mathlib

/-!
# The Lévy–Ciesielski process: paths, measurability, integer times

The L'evy--Ciesielski process and the pathwise parts (BM0), (BM1) and "integer values" of
L'evy--Ciesielski.

For a family `ξ : Idx d → Ω → ℝ` the process is
`B(t)_i = ∑_m [ξ_{(i,m,*)} clamp(t-m) + 1_G ∑_n ∑_k ξ_{(i,m,(n,k))} S_{n,k}(t-m)]`,
where `G = goodSet ξ`. We show that, for every `ω`, the path is continuous with `B(0) = 0`, that
each `B(t)` is measurable, and that `B(j) = ∑_{m<j} ξ_{(·,m,*)}` at integer times.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal Topology

namespace ElboimSly.Brownian

variable {Ω : Type*} {d : ℕ}

/-- The level-`n` sum `F_{i,m,n}(t) = ∑_k ξ_{(i,m,(n,k))} S_{n,k}(t-m)` (The L'evy--Ciesielski process). -/
noncomputable def levelSum (ξ : Idx d → Ω → ℝ) (i : Fin d) (m n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin (2 ^ n), ξ (i, m, some ⟨n, k⟩) ω * schauder n k (t - m)

/-- The `m`th summand of the Lévy–Ciesielski series in coordinate `i`
(The L'evy--Ciesielski process). -/
noncomputable def lcTerm (ξ : Idx d → Ω → ℝ) (i : Fin d) (m : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ξ (i, m, none) ω * clamp (t - m) +
    (goodSet ξ).indicator (fun ω => ∑' n : ℕ, levelSum ξ i m n t ω) ω

/-- The L'evy--Ciesielski process. The Lévy–Ciesielski process `LC[ξ] : ℝ≥0 → Ω → (Fin d → ℝ)`. -/
noncomputable def levyCiesielski (ξ : Idx d → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  fun i => ∑' m : ℕ, lcTerm ξ i m t ω

lemma levelSum_of_le (ξ : Idx d → Ω → ℝ) (i : Fin d) (m n : ℕ) {t : ℝ} (ω : Ω)
    (h : t ≤ m) : levelSum ξ i m n t ω = 0 := by
  unfold levelSum
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [schauder_of_nonpos _ _ (by linarith), mul_zero]

lemma lcTerm_of_le (ξ : Idx d → Ω → ℝ) (i : Fin d) (m : ℕ) {t : ℝ} (ω : Ω) (h : t ≤ m) :
    lcTerm ξ i m t ω = 0 := by
  unfold lcTerm
  rw [clamp_of_nonpos (by linarith), mul_zero, zero_add]
  by_cases hω : ω ∈ goodSet ξ
  · rw [Set.indicator_of_mem hω]; simp [levelSum_of_le, h]
  · rw [Set.indicator_of_notMem hω]

lemma levyCiesielski_eq_sum (ξ : Idx d → Ω → ℝ) {t : ℝ≥0} (M : ℕ) (ht : (t : ℝ) ≤ M) (ω : Ω)
    (i : Fin d) :
    levyCiesielski ξ t ω i = ∑ m ∈ Finset.range M, lcTerm ξ i m t ω := by
  unfold levyCiesielski
  refine tsum_eq_sum fun m hm => lcTerm_of_le ξ i m ω ?_
  rw [Finset.mem_range, not_lt] at hm
  exact ht.trans (by exact_mod_cast hm)

/-- (BM1), `B(0) = 0`. -/
lemma levyCiesielski_zero (ξ : Idx d → Ω → ℝ) (ω : Ω) : levyCiesielski ξ 0 ω = 0 := by
  funext i
  rw [levyCiesielski_eq_sum ξ (t := 0) 0 (by simp) ω i]
  simp

/-- L'evy--Ciesielski, integer values: `B(j) = ∑_{m<j} ξ_{(·,m,*)}`
holds everywhere on `Ω`. -/
lemma levyCiesielski_nat (ξ : Idx d → Ω → ℝ) (j : ℕ) (ω : Ω) (i : Fin d) :
    levyCiesielski ξ (j : ℝ≥0) ω i = ∑ m ∈ Finset.range j, ξ (i, m, none) ω := by
  rw [levyCiesielski_eq_sum ξ j (by simp) ω i]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : (m : ℝ) + 1 ≤ j := by exact_mod_cast Finset.mem_range.mp hm
  have h1 : (1 : ℝ) ≤ (j : ℝ) - m := by linarith
  have hz : ∀ n ω', levelSum ξ i m n (j : ℝ) ω' = 0 := by
    intro n ω'
    unfold levelSum
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [schauder_of_one_le k.2 h1, mul_zero]
  unfold lcTerm
  simp only [NNReal.coe_natCast]
  simp [hz, clamp_of_one_le h1]

/-! ### Continuity of paths -/

lemma summable_levelSum {ξ : Idx d → Ω → ℝ} {ω : Ω} (hω : ω ∈ goodSet ξ) (i : Fin d)
    (m : ℕ) (t : ℝ) : Summable fun n => levelSum ξ i m n t ω :=
  Summable.of_norm_bounded (summable_of_mem_goodSet hω i m) fun n => by
    rw [Real.norm_eq_abs]
    exact abs_sum_schauder_le n (t - m) (fun k => ξ (i, m, some ⟨n, k⟩) ω)
      (levelMax_nonneg ξ i m n ω) (fun k => abs_le_levelMax ξ i m n ω k)

lemma continuous_levelSum (ξ : Idx d → Ω → ℝ) (i : Fin d) (m n : ℕ) (ω : Ω) :
    Continuous fun t : ℝ => levelSum ξ i m n t ω := by
  unfold levelSum
  have := continuous_schauder
  fun_prop

lemma continuous_lcTerm (ξ : Idx d → Ω → ℝ) (i : Fin d) (m : ℕ) (ω : Ω) :
    Continuous fun t : ℝ => lcTerm ξ i m t ω := by
  unfold lcTerm
  refine Continuous.add (by have := continuous_clamp; fun_prop) ?_
  by_cases hω : ω ∈ goodSet ξ
  · simp only [Set.indicator_of_mem hω]
    refine continuous_tsum (u := fun n => schauderAmp n * levelMax ξ i m n ω)
      (continuous_levelSum ξ i m · ω) (summable_of_mem_goodSet hω i m) fun n t => ?_
    rw [Real.norm_eq_abs]
    exact abs_sum_schauder_le n (t - m) (fun k => ξ (i, m, some ⟨n, k⟩) ω)
      (levelMax_nonneg ξ i m n ω) (fun k => abs_le_levelMax ξ i m n ω k)
  · simp only [Set.indicator_of_notMem hω]
    exact continuous_const

/-- (BM1): every path of the Lévy–Ciesielski process is continuous. -/
lemma continuous_levyCiesielski (ξ : Idx d → Ω → ℝ) (ω : Ω) :
    Continuous fun t : ℝ≥0 => levyCiesielski ξ t ω := by
  refine continuous_pi fun i => ?_
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (t₀ : ℝ)
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝 t₀, (t : ℝ) ≤ M := by
    have : IsOpen {t : ℝ≥0 | (t : ℝ) < M} := isOpen_lt NNReal.continuous_coe continuous_const
    filter_upwards [this.mem_nhds hM] with t ht using le_of_lt ht
  have hc : Continuous fun t : ℝ≥0 => ∑ m ∈ Finset.range M, lcTerm ξ i m t ω :=
    continuous_finsetSum _ fun m _ => (continuous_lcTerm ξ i m ω).comp NNReal.continuous_coe
  refine hc.continuousAt.congr ?_
  filter_upwards [hev] with t ht
  exact (levyCiesielski_eq_sum ξ M ht ω i).symm

/-! ### Measurability -/

variable [MeasurableSpace Ω]

lemma measurable_lcTerm {ξ : Idx d → Ω → ℝ} (hξ : ∀ α, Measurable (ξ α)) (i : Fin d) (m : ℕ)
    (t : ℝ) : Measurable (lcTerm ξ i m t) := by
  unfold lcTerm
  refine Measurable.add ((hξ _).mul_const _) ?_
  have hG := measurableSet_goodSet hξ
  have hpart : ∀ N : ℕ, Measurable fun ω => ∑ n ∈ Finset.range N, levelSum ξ i m n t ω := by
    intro N
    refine Finset.measurable_sum _ fun n _ => ?_
    unfold levelSum
    exact Finset.measurable_sum _ fun k _ => (hξ _).mul_const _
  refine measurable_of_tendsto_metrizable (f := fun N ω =>
    (goodSet ξ).indicator (fun ω => ∑ n ∈ Finset.range N, levelSum ξ i m n t ω) ω)
    (fun N => (hpart N).indicator hG) (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ goodSet ξ
  · simp only [Set.indicator_of_mem hω]
    exact (summable_levelSum hω i m t).hasSum.tendsto_sum_nat
  · simp only [Set.indicator_of_notMem hω]
    exact tendsto_const_nhds

/-- (BM0): each `B(t)` is measurable. -/
lemma measurable_levyCiesielski {ξ : Idx d → Ω → ℝ} (hξ : ∀ α, Measurable (ξ α)) (t : ℝ≥0) :
    Measurable (levyCiesielski ξ t) := by
  refine measurable_pi_iff.2 fun i => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (t : ℝ)
  have : (fun ω => levyCiesielski ξ t ω i) = fun ω => ∑ m ∈ Finset.range M, lcTerm ξ i m t ω :=
    funext fun ω => levyCiesielski_eq_sum ξ M hM.le ω i
  rw [this]
  exact Finset.measurable_sum _ fun m _ => measurable_lcTerm hξ i m t

end ElboimSly.Brownian
