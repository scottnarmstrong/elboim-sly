/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Regular
public import ElboimSly.Paper.Base.Riemann
public import Mathlib

/-!
# Regular functionals of pairs of paths: regular paths

Regular functionals of pairs of paths (supplement), part (b).

For a regular `γ ∈ Π_T`: `V(γ)` is the range of `γ_i` on `[0, L]` and is finite;
`{s ∈ [0, T] : f^γ(s) = 1}` is a finite union of intervals; and `Φ(γ)` is the Lebesgue measure
of `{s ∈ [0, T] : ∃ s' ∈ [0, L], ‖γ_j(s) - γ_i(s')‖ ≤ ρ}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Paper.Base

variable {d k : ℕ}

/-- `{s ∈ [0, T] : ∃ s' ∈ [0, L], ‖γ_j(s) - γ_i(s')‖ ≤ ρ}`, in real time. -/
def lebSet (T L : ℝ≥0) (ρ : ℝ) (i j : Fin k) (γ : PathsOn d k T) : Set ℝ :=
  {x | 0 ≤ x ∧ x ≤ T ∧ ∃ y : ℝ, 0 ≤ y ∧ y ≤ L ∧
    ‖extT T γ j x.toNNReal - extT T γ i y.toNNReal‖ ≤ ρ}

/-- The Lebesgue measure of `lebSet`. -/
noncomputable def lebMeas (T L : ℝ≥0) (ρ : ℝ) (i j : Fin k) (γ : PathsOn d k T) : ℝ :=
  (volume (lebSet T L ρ i j γ)).toReal

theorem vset_eq_image {T L : ℝ≥0} {i : Fin k} {γ : PathsOn d k T}
    (hγ : IsRegularPaths T γ) : vset T L i γ = extT T γ i '' Iic L := by
  unfold vset
  refine Subset.antisymm (image_mono ?_) ?_
  · rintro q (⟨hq, _⟩ | rfl)
    · exact hq.le
    · exact le_rfl
  · rintro _ ⟨s, hs, rfl⟩
    rcases (show s ≤ L from hs).lt_or_eq with hlt | heq
    · obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp ((hγ i).rc s)
      obtain ⟨q, hq0, hq1, hq2⟩ := (NNReal.lt_iff_exists_rat_btwn s (min u' L)).1
        (lt_min hu' hlt)
      refine ⟨Real.toNNReal q, Or.inl ⟨hq2.trans_le (min_le_right _ _), q, hq0, rfl⟩, ?_⟩
      exact hsub ⟨hq1.le, hq2.trans_le (min_le_left _ _)⟩
    · rw [heq]; exact ⟨L, Or.inr rfl, rfl⟩

theorem vset_finite {T L : ℝ≥0} {i : Fin k} {γ : PathsOn d k T} (hγ : IsRegularPaths T γ) :
    (vset T L i γ).Finite := by
  rw [vset_eq_image hγ]; exact finite_image_Iic (hγ i) L

theorem infDist_le_iff {T L : ℝ≥0} {i : Fin k} {γ : PathsOn d k T} (hγ : IsRegularPaths T γ)
    (ρ : ℝ) (z : Fin d → ℤ) :
    Metric.infDist z (vset T L i γ) ≤ ρ ↔ ∃ s' ≤ L, ‖z - extT T γ i s'‖ ≤ ρ := by
  have hne : (vset T L i γ).Nonempty := (qSet_nonempty L).image _
  obtain ⟨y, hy, hyeq⟩ := (vset_finite hγ).isCompact.exists_infDist_eq_dist hne z
  rw [vset_eq_image hγ] at hy
  constructor
  · intro h
    obtain ⟨s', hs', rfl⟩ := hy
    exact ⟨s', hs', by rw [← dist_eq_norm, ← hyeq]; exact h⟩
  · rintro ⟨s', hs', h⟩
    calc Metric.infDist z (vset T L i γ) ≤ dist z (extT T γ i s') :=
          Metric.infDist_le_dist_of_mem (by rw [vset_eq_image hγ]; exact ⟨s', hs', rfl⟩)
      _ ≤ ρ := by rwa [dist_eq_norm]

theorem lebSet_eq_levelSet {T L : ℝ≥0} (ρ : ℝ) {i j : Fin k} {γ : PathsOn d k T}
    (hγ : IsRegularPaths T γ) :
    lebSet T L ρ i j γ =
      levelSet (extT T γ j) {z | Metric.infDist z (vset T L i γ) ≤ ρ} T := by
  ext x
  simp only [lebSet, levelSet, mem_ofPred_eq, infDist_le_iff hγ]
  refine and_congr_right fun hx0 => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨y, hy0, hyL, h⟩
    exact ⟨y.toNNReal, by rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hy0], h⟩
  · rintro ⟨s', hs', h⟩
    exact ⟨s', s'.2, by exact_mod_cast hs', by simpa using h⟩

theorem Phi_eq_lebMeas {T L : ℝ≥0} (ρ : ℝ) {i j : Fin k} {γ : PathsOn d k T}
    (hγ : IsRegularPaths T γ) : Phi T L ρ i j γ = lebMeas T L ρ i j γ := by
  set B : Set (Fin d → ℤ) := {z | Metric.infDist z (vset T L i γ) ≤ ρ} with hB
  have hfv : ∀ s, fval T L ρ i j γ s = indVal (extT T γ j) B s := fun s => by
    unfold fval indVal; rfl
  rcases eq_or_ne T 0 with rfl | hT0
  · have h0 : Phi (0 : ℝ≥0) L ρ i j γ = 0 := by
      unfold Phi; simp
    rw [h0]
    unfold lebMeas
    have : volume (lebSet (0 : ℝ≥0) L ρ i j γ) = 0 := by
      refine measure_mono_null (t := {0}) ?_ Real.volume_singleton
      intro x hx
      exact le_antisymm (by simpa using hx.2.1) hx.1
    rw [this]; simp
  · have hT : 0 < T := pos_iff_ne_zero.2 hT0
    unfold Phi lebMeas
    rw [lebSet_eq_levelSet ρ hγ]
    refine Filter.Tendsto.limsup_eq ?_
    have hbound := fun m : ℕ => riemann_error (hγ j) B hT m
    have hlim : Tendsto (fun m : ℕ => (discCount (extT T γ j) T : ℝ) * ((T : ℝ) / 2 ^ m))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => (T : ℝ) / 2 ^ m) atTop (𝓝 0) :=
        (tendsto_const_nhds (x := (T : ℝ))).div_atTop
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
      simpa using (tendsto_const_nhds (x := (discCount (extT T γ j) T : ℝ))).mul h1
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hlim
    have := hbound m
    simp only [hfv, meshPt] at this ⊢
    rw [Real.norm_eq_abs]
    exact this

end ElboimSly.Paper
