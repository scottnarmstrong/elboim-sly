/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.LevyGrid
public import Mathlib

/-!
# Lévy's maximal inequality

L'evy's maximal inequality.  For every one-dimensional SRW `Y`, `T > 0` and `λ ∈ ℝ`,
`P(∃ s ∈ [0,T], Y(s) ≥ λ) ≤ 2 P(Y(T) ≥ λ)` and the same for `|Y|`.  The proof passes to the limit
along the nested dyadic grids, using right-continuity (local constancy) of the paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical

namespace ElboimSly
namespace SRW

/-- The dyadic grid of mesh `2^{-m}` in `[0,T]`, together with `T`. -/
noncomputable def levyGrid (T : ℝ≥0) (m : ℕ) : Finset ℝ≥0 :=
  insert T ((Finset.range (⌊T * 2 ^ m⌋₊ + 1)).image (dt m))

theorem levyGrid_le {T : ℝ≥0} {m : ℕ} {σ : ℝ≥0} (h : σ ∈ levyGrid T m) : σ ≤ T := by
  unfold levyGrid at h
  rw [Finset.mem_insert, Finset.mem_image] at h
  rcases h with rfl | ⟨k, hk, rfl⟩
  · exact le_rfl
  · rw [Finset.mem_range] at hk
    unfold dt
    rw [div_le_iff₀ (by positivity)]
    exact (Nat.le_floor_iff (by positivity)).1 (by omega)

theorem levyGrid_mono (T : ℝ≥0) (m : ℕ) : levyGrid T m ⊆ levyGrid T (m + 1) := by
  intro σ h
  unfold levyGrid at h ⊢
  rw [Finset.mem_insert, Finset.mem_image] at h
  rw [Finset.mem_insert, Finset.mem_image]
  rcases h with rfl | ⟨k, hk, rfl⟩
  · exact Or.inl rfl
  · right
    refine ⟨2 * k, ?_, ?_⟩
    · rw [Finset.mem_range] at hk ⊢
      have h1 : (k : ℝ≥0) ≤ T * 2 ^ m := (Nat.le_floor_iff (by positivity)).1 (by omega)
      have h2 : ((2 * k : ℕ) : ℝ≥0) ≤ T * 2 ^ (m + 1) := by
        push_cast; rw [pow_succ]; nlinarith
      have := (Nat.le_floor_iff (by positivity)).2 h2
      omega
    · unfold dt
      push_cast
      rw [pow_succ]
      field_simp

theorem levyGrid_exists {T : ℝ≥0} {γ : PathSpace 1} (hγ : IsRegularPath γ) (hit : ℤ → Prop) :
    (∃ s, s ≤ T ∧ hit (γ s 0)) ↔ ∃ m, ∃ σ ∈ levyGrid T m, hit (γ σ 0) := by
  constructor
  · rintro ⟨s, hsT, hs⟩
    obtain ⟨δ, hδ, hconst⟩ := hγ s
    have hev : ∀ᶠ m in atTop, dy m s < s + δ :=
      (tendsto_dy s).eventually (gt_mem_nhds (lt_add_of_pos_right s hδ))
    obtain ⟨m, hm⟩ := hev.exists
    refine ⟨m, ?_⟩
    by_cases hT : dy m s ≤ T
    · refine ⟨dy m s, ?_, ?_⟩
      · unfold levyGrid
        rw [Finset.mem_insert, Finset.mem_image]
        right
        refine ⟨⌈s * 2 ^ m⌉₊, ?_, rfl⟩
        rw [Finset.mem_range]
        have : (⌈s * 2 ^ m⌉₊ : ℝ≥0) ≤ T * 2 ^ m := by
          have h := hT
          unfold dy at h
          rwa [div_le_iff₀ (by positivity)] at h
        have := (Nat.le_floor_iff (by positivity)).2 this
        omega
      · rw [hconst _ (le_dy m s) hm]; exact hs
    · refine ⟨T, Finset.mem_insert_self _ _, ?_⟩
      push Not at hT
      rw [hconst T hsT (lt_trans hT hm)]
      exact hs
  · rintro ⟨m, σ, hσ, hs⟩
    exact ⟨σ, levyGrid_le hσ, hs⟩

/-- Passing to the limit along the grids. -/
theorem IsSRW.levy_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace 1}
    (hY : IsSRW P Y) (T : ℝ≥0) (hit : ℤ → Prop) {c : ℝ≥0∞}
    (hc : ∀ m, P {ω | ∃ σ ∈ levyGrid T m, hit (Y ω σ 0)} ≤ c) :
    P {ω | ∃ s, s ≤ T ∧ hit (Y ω s 0)} ≤ c := by
  have hmono : Monotone fun m => {ω | ∃ σ ∈ levyGrid T m, hit (Y ω σ 0)} := by
    refine monotone_nat_of_le_succ fun m ω ⟨σ, hσ, h⟩ => ⟨σ, levyGrid_mono T m hσ, h⟩
  have hset : {ω | ∃ s, s ≤ T ∧ hit (Y ω s 0)} =
      ⋃ m, {ω | ∃ σ ∈ levyGrid T m, hit (Y ω σ 0)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    exact levyGrid_exists (hY.2.1 ω) hit
  rw [hset, hmono.measure_iUnion]
  exact iSup_le hc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- L'evy's maximal inequality, one-sided, as measures. -/
theorem IsSRW.levy_measure {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (T : ℝ≥0) (lam : ℝ) :
    P {ω | ∃ s, s ≤ T ∧ lam ≤ (Y ω s 0 : ℝ)} ≤ 2 * P {ω | lam ≤ (Y ω T 0 : ℝ)} :=
  hY.levy_limit T (fun x => lam ≤ (x : ℝ)) fun m =>
    hY.levy_grid (levyGrid T m) (fun _ h => levyGrid_le h) lam

/-- L'evy's maximal inequality, two-sided, as measures. -/
theorem IsSRW.levy_abs_measure {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (T : ℝ≥0) (lam : ℝ) :
    P {ω | ∃ s, s ≤ T ∧ lam ≤ |(Y ω s 0 : ℝ)|} ≤ 2 * P {ω | lam ≤ |(Y ω T 0 : ℝ)|} :=
  hY.levy_limit T (fun x => lam ≤ |(x : ℝ)|) fun m =>
    hY.levy_grid_abs (levyGrid T m) (fun _ h => levyGrid_le h) lam

/-- L'evy's maximal inequality, one-sided. -/
theorem IsSRW.levy {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (T : ℝ≥0) (lam : ℝ) :
    P.real {ω | ∃ s, s ≤ T ∧ lam ≤ (Y ω s 0 : ℝ)} ≤ 2 * P.real {ω | lam ≤ (Y ω T 0 : ℝ)} := by
  have := hY.isProbabilityMeasure
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (hY.levy_measure T lam)
  rwa [ENNReal.toReal_mul] at this

/-- L'evy's maximal inequality, two-sided. -/
theorem IsSRW.levy_abs {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (T : ℝ≥0) (lam : ℝ) :
    P.real {ω | ∃ s, s ≤ T ∧ lam ≤ |(Y ω s 0 : ℝ)|} ≤
      2 * P.real {ω | lam ≤ |(Y ω T 0 : ℝ)|} := by
  have := hY.isProbabilityMeasure
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)) (hY.levy_abs_measure T lam)
  rwa [ENNReal.toReal_mul] at this

end SRW
end ElboimSly
