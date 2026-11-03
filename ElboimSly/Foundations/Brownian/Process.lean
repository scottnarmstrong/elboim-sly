/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.LevyCiesielski
public import ElboimSly.Foundations.Brownian.GaussianSeries
import Mathlib

/-!
# Gaussian structure of the Lévy–Ciesielski process

L'evy--Ciesielski, "Gaussian structure" paragraph.

Every finite linear combination `Y = ∑_j λ_j B^{i_j}(t_j)` of coordinates of
`B = levyCiesielski ξ` is the almost sure limit of `∑_{α ∈ F_N} c_α ξ_α`, where
`F_N = {(i,m,h) : m < N, h ∈ ℋ_{<N}}` and `c_α = ∑_j λ_j 1{i_j = i} a_h(t_j - m)`, and
`∑_{F_N} c_α² → ∑_{j,k} λ_j λ_k 1{i_j = i_k} min(t_j, t_k)`. By series of independent Gaussians
(`hasLaw_of_tendsto_sums`), `Y` is centred Gaussian with this variance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace ElboimSly.Brownian

variable {Ω : Type*} {d : ℕ}

/-! ### Kernel partial sums over the exhaustion -/

lemma kernelPartial_of_nonpos (N : ℕ) {u : ℝ} (hu : u ≤ 0) (v : ℝ) : kernelPartial N u v = 0 := by
  unfold kernelPartial
  simp [clamp_of_nonpos hu, schauder_of_nonpos _ _ hu]

lemma kernel_of_nonpos {u : ℝ} (hu : u ≤ 0) (v : ℝ) : kernel u v = 0 := by
  rw [kernel_eq_min, clamp_of_nonpos hu]
  exact min_eq_left (clamp_nonneg v)

lemma tendsto_sum_kernelPartial {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Tendsto (fun N => ∑ m ∈ Finset.range N, kernelPartial N (s - m) (t - m)) atTop
      (𝓝 (min s t)) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (max s t)
  have hsM : s ≤ M := (le_max_left _ _).trans hM
  have htM : t ≤ M := (le_max_right _ _).trans hM
  have hev : ∀ N ≥ M, ∑ m ∈ Finset.range N, kernelPartial N (s - m) (t - m) =
      ∑ m ∈ Finset.range M, kernelPartial N (s - m) (t - m) := by
    intro N hN
    symm
    refine Finset.sum_subset (Finset.range_mono hN) fun m _ hm => ?_
    rw [Finset.mem_range, not_lt] at hm
    have : (M : ℝ) ≤ m := by exact_mod_cast hm
    exact kernelPartial_of_nonpos N (by linarith) _
  have hlim : Tendsto (fun N => ∑ m ∈ Finset.range M, kernelPartial N (s - m) (t - m)) atTop
      (𝓝 (∑ m ∈ Finset.range M, kernel (s - m) (t - m))) :=
    tendsto_finsetSum _ fun m _ => tendsto_kernelPartial _ _
  have hval : ∑ m ∈ Finset.range M, kernel (s - m) (t - m) = min s t := by
    rw [← (hasSum_kernel_sub hs ht).tsum_eq]
    symm
    refine tsum_eq_sum fun m hm => ?_
    rw [Finset.mem_range, not_lt] at hm
    have : (M : ℝ) ≤ m := by exact_mod_cast hm
    exact kernel_of_nonpos (by linarith) _
  rw [hval] at hlim
  exact hlim.congr' ((eventually_ge_atTop M).mono fun N hN => (hev N hN).symm)

/-! ### The exhaustion `F_N` -/

/-- The finite Haar index set `ℋ_{<N} = {*} ∪ {(n,k) : n < N}`. -/
def haarFin (N : ℕ) : Finset HaarIdx :=
  Finset.insertNone ((Finset.range N).sigma fun n => (Finset.univ : Finset (Fin (2 ^ n))))

/-- The finite set `F_N = {(i,m,h) : m < N, h ∈ ℋ_{<N}}` of indices. -/
def expFin (d N : ℕ) : Finset (Idx d) :=
  Finset.univ ×ˢ (Finset.range N ×ˢ haarFin N)

lemma sum_expFin (N : ℕ) (f : Idx d → ℝ) :
    ∑ α ∈ expFin d N, f α = ∑ i : Fin d, ∑ m ∈ Finset.range N,
      (f (i, m, none) + ∑ n ∈ Finset.range N, ∑ k : Fin (2 ^ n), f (i, m, some ⟨n, k⟩)) := by
  unfold expFin haarFin
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_insertNone, Finset.sum_sigma]

/-- Partial sums of the series in coordinate `i`: `∑_{m<N} [ξ_{(i,m,*)} cl(t-m) + ∑_{n<N} F_{i,m,n}(t)]`. -/
noncomputable def partialSum (ξ : Idx d → Ω → ℝ) (N : ℕ) (i : Fin d) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range N,
    (ξ (i, m, none) ω * clamp (t - m) + ∑ n ∈ Finset.range N, levelSum ξ i m n t ω)

lemma tendsto_partialSum {ξ : Idx d → Ω → ℝ} {ω : Ω} (hω : ω ∈ goodSet ξ) (i : Fin d)
    (t : ℝ≥0) :
    Tendsto (fun N => partialSum ξ N i t ω) atTop (𝓝 (levyCiesielski ξ t ω i)) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (t : ℝ)
  have hev : ∀ N ≥ M, partialSum ξ N i t ω = ∑ m ∈ Finset.range M,
      (ξ (i, m, none) ω * clamp (t - m) + ∑ n ∈ Finset.range N, levelSum ξ i m n t ω) := by
    intro N hN
    unfold partialSum
    symm
    refine Finset.sum_subset (Finset.range_mono hN) fun m _ hm => ?_
    rw [Finset.mem_range, not_lt] at hm
    have : (t : ℝ) ≤ m := hM.trans (by exact_mod_cast hm)
    simp [clamp_of_nonpos (by linarith : (t : ℝ) - m ≤ 0), levelSum_of_le ξ i m _ ω this]
  have hlim : Tendsto (fun N => ∑ m ∈ Finset.range M,
      (ξ (i, m, none) ω * clamp (t - m) + ∑ n ∈ Finset.range N, levelSum ξ i m n t ω)) atTop
      (𝓝 (∑ m ∈ Finset.range M,
      (ξ (i, m, none) ω * clamp (t - m) + ∑' n, levelSum ξ i m n t ω))) :=
    tendsto_finsetSum _ fun m _ =>
      tendsto_const_nhds.add (summable_levelSum hω i m t).hasSum.tendsto_sum_nat
  have hval : levyCiesielski ξ t ω i = ∑ m ∈ Finset.range M,
      (ξ (i, m, none) ω * clamp (t - m) + ∑' n, levelSum ξ i m n t ω) := by
    rw [levyCiesielski_eq_sum ξ M hM ω i]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold lcTerm
    rw [Set.indicator_of_mem hω]
  rw [hval]
  exact hlim.congr' ((eventually_ge_atTop M).mono fun N hN => (hev N hN).symm)

/-! ### The coefficients -/

section Coeff

variable {ι : Type*} [Fintype ι]

/-- The coefficient `c_α = ∑_j λ_j 1{i_j = i} a_h(t_j - m)` of `ξ_α`, `α = (i, m, h)`. -/
noncomputable def lcCoeff (x : ι → Σ _ : Fin d, ℝ≥0) (lam : ι → ℝ) (α : Idx d) : ℝ :=
  ∑ j, lam j * (if (x j).1 = α.1 then haarFun α.2.2 ((x j).2 - α.2.1) else 0)

lemma sum_expFin_coord (ξ : Idx d → Ω → ℝ) (N : ℕ) (i₀ : Fin d) (t : ℝ) (ω : Ω) :
    ∑ α ∈ expFin d N,
      (if i₀ = α.1 then haarFun α.2.2 (t - α.2.1) else 0) * ξ α ω = partialSum ξ N i₀ t ω := by
  rw [sum_expFin]
  have : ∀ i : Fin d, ∑ m ∈ Finset.range N,
      ((if i₀ = i then haarFun none (t - m) else 0) * ξ (i, m, none) ω +
        ∑ n ∈ Finset.range N, ∑ k : Fin (2 ^ n),
          (if i₀ = i then haarFun (some ⟨n, k⟩) (t - m) else 0) * ξ (i, m, some ⟨n, k⟩) ω) =
      if i₀ = i then partialSum ξ N i t ω else 0 := by
    intro i
    by_cases h : i₀ = i
    · subst h
      simp only [ite_true, partialSum, haarFun, levelSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_comm]
      congr 1
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
    · simp [h]
  simp only [Finset.sum_congr rfl fun i _ => this i, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma sum_expFin_coeff (ξ : Idx d → Ω → ℝ) (N : ℕ) (x : ι → Σ _ : Fin d, ℝ≥0) (lam : ι → ℝ)
    (ω : Ω) : ∑ α ∈ expFin d N, lcCoeff x lam α * ξ α ω =
      ∑ j, lam j * partialSum ξ N (x j).1 (x j).2 ω := by
  unfold lcCoeff
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sum_expFin_coord ξ N (x j).1 (x j).2 ω, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

lemma sum_expFin_sq (N : ℕ) (x : ι → Σ _ : Fin d, ℝ≥0) (lam : ι → ℝ) :
    ∑ α ∈ expFin d N, lcCoeff x lam α ^ 2 =
      ∑ j, ∑ k, lam j * lam k *
        (if (x j).1 = (x k).1 then
          ∑ m ∈ Finset.range N, kernelPartial N ((x j).2 - m) ((x k).2 - m) else 0) := by
  have hpair : ∀ j k : ι, ∑ α ∈ expFin d N,
      (lam j * (if (x j).1 = α.1 then haarFun α.2.2 ((x j).2 - α.2.1) else 0)) *
        (lam k * (if (x k).1 = α.1 then haarFun α.2.2 ((x k).2 - α.2.1) else 0)) =
      lam j * lam k * (if (x j).1 = (x k).1 then
          ∑ m ∈ Finset.range N, kernelPartial N ((x j).2 - m) ((x k).2 - m) else 0) := by
    intro j k
    have e : ∀ α : Idx d,
        (lam j * (if (x j).1 = α.1 then haarFun α.2.2 ((x j).2 - α.2.1) else 0)) *
          (lam k * (if (x k).1 = α.1 then haarFun α.2.2 ((x k).2 - α.2.1) else 0)) =
        lam j * lam k * ((if (x j).1 = α.1 then haarFun α.2.2 ((x j).2 - α.2.1) else 0) *
          (if (x k).1 = α.1 then haarFun α.2.2 ((x k).2 - α.2.1) else 0)) := fun α => by ring
    simp only [e]
    rw [← Finset.mul_sum, sum_expFin]
    congr 1
    by_cases hjk : (x j).1 = (x k).1
    · rw [ite_eq_left hjk]
      have : ∀ i : Fin d, ∑ m ∈ Finset.range N,
          ((if (x j).1 = i then haarFun none ((x j).2 - m) else 0) *
              (if (x k).1 = i then haarFun none ((x k).2 - m) else 0) +
            ∑ n ∈ Finset.range N, ∑ l : Fin (2 ^ n),
              (if (x j).1 = i then haarFun (some ⟨n, l⟩) ((x j).2 - m) else 0) *
                (if (x k).1 = i then haarFun (some ⟨n, l⟩) ((x k).2 - m) else 0)) =
          if (x j).1 = i then ∑ m ∈ Finset.range N,
            kernelPartial N ((x j).2 - m) ((x k).2 - m) else 0 := by
        intro i
        by_cases h : (x j).1 = i
        · have h' : (x k).1 = i := hjk ▸ h
          simp only [h, h', ite_true, kernelPartial, haarFun]
        · simp [h]
      refine (Finset.sum_congr rfl fun i _ => this i).trans ?_
      simp
    · rw [ite_eq_right hjk]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun m _ => ?_
      by_cases h : (x j).1 = i
      · have h' : (x k).1 ≠ i := fun h' => hjk (h.trans h'.symm)
        simp [h']
      · simp [h]
  calc ∑ α ∈ expFin d N, lcCoeff x lam α ^ 2
      = ∑ α ∈ expFin d N, ∑ j, ∑ k,
        (lam j * (if (x j).1 = α.1 then haarFun α.2.2 ((x j).2 - α.2.1) else 0)) *
          (lam k * (if (x k).1 = α.1 then haarFun α.2.2 ((x k).2 - α.2.1) else 0)) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        unfold lcCoeff
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ j, ∑ k, ∑ α ∈ expFin d N,
        (lam j * (if (x j).1 = α.1 then haarFun α.2.2 ((x j).2 - α.2.1) else 0)) *
          (lam k * (if (x k).1 = α.1 then haarFun α.2.2 ((x k).2 - α.2.1) else 0)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hpair j k

lemma tendsto_sum_expFin_sq (x : ι → Σ _ : Fin d, ℝ≥0) (lam : ι → ℝ) :
    Tendsto (fun N => ∑ α ∈ expFin d N, lcCoeff x lam α ^ 2) atTop
      (𝓝 (∑ j, ∑ k, lam j * lam k *
        (if (x j).1 = (x k).1 then min ((x j).2 : ℝ) ((x k).2 : ℝ) else 0))) := by
  simp only [sum_expFin_sq]
  refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => ?_
  refine Tendsto.const_mul _ ?_
  by_cases h : (x j).1 = (x k).1
  · simp only [h, ite_true]
    exact tendsto_sum_kernelPartial (x j).2.2 (x k).2.2
  · simp [h]

lemma tendsto_sum_expFin {ξ : Idx d → Ω → ℝ} {ω : Ω} (hω : ω ∈ goodSet ξ)
    (x : ι → Σ _ : Fin d, ℝ≥0) (lam : ι → ℝ) :
    Tendsto (fun N => ∑ α ∈ expFin d N, lcCoeff x lam α * ξ α ω) atTop
      (𝓝 (∑ j, lam j * levyCiesielski ξ (x j).2 ω (x j).1)) := by
  simp only [sum_expFin_coeff]
  exact tendsto_finsetSum _ fun j _ => (tendsto_partialSum hω _ _).const_mul _

end Coeff

/-- L'evy--Ciesielski, "Gaussian structure". Any finite linear combination
of coordinates of the Lévy–Ciesielski process of an i.i.d. `N(0,1)` family is centred Gaussian,
with variance `∑_{j,k} λ_j λ_k 1{i_j = i_k} min(t_j, t_k)`. -/
theorem hasLaw_linear_combination [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Idx d → Ω → ℝ} (hmeas : ∀ α, Measurable (ξ α)) (hind : iIndepFun ξ P)
    (hlaw : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P)
    {ι : Type*} [Fintype ι] (x : ι → Σ _ : Fin d, ℝ≥0) (lam : ι → ℝ) :
    0 ≤ (∑ j, ∑ k, lam j * lam k *
        (if (x j).1 = (x k).1 then min ((x j).2 : ℝ) ((x k).2 : ℝ) else 0)) ∧
    HasLaw (fun ω => ∑ j, lam j * levyCiesielski ξ (x j).2 ω (x j).1)
      (gaussianReal 0 (Real.toNNReal (∑ j, ∑ k, lam j * lam k *
        (if (x j).1 = (x k).1 then min ((x j).2 : ℝ) ((x k).2 : ℝ) else 0)))) P := by
  have hvar := tendsto_sum_expFin_sq x lam
  have hnn : 0 ≤ (∑ j, ∑ k, lam j * lam k *
        (if (x j).1 = (x k).1 then min ((x j).2 : ℝ) ((x k).2 : ℝ) else 0)) :=
    ge_of_tendsto' hvar fun N => Finset.sum_nonneg fun α _ => sq_nonneg _
  refine ⟨hnn, ?_⟩
  refine hasLaw_of_tendsto_sums hind hlaw (lcCoeff x lam) (expFin d) ?_ ?_ ?_
  · exact (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply (x j).1).comp (measurable_levyCiesielski hmeas (x j).2)).const_mul
        (lam j)).aemeasurable
  · rw [Real.coe_toNNReal _ hnn]; exact hvar
  · filter_upwards [ae_mem_goodSet hlaw] with ω hω using tendsto_sum_expFin hω x lam

end ElboimSly.Brownian
