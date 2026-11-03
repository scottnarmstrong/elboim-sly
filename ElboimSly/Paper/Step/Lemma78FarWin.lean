/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Sets
public import ElboimSly.Paper.Avoid.Claim3Window
public import Mathlib

/-!
# The far event, window estimate with general centres

One excursion succeeds with probability at least frac12, "The far event". This is `es4_window3` (ES22 Claim 4.3) for a
finite set of centres `c` and the window `[3.89ⁿ, 4ⁿ)` of rational times: by the induction hypothesis at arbitrary times (d)
the walk is within `(4ⁿ)^θ` of `σB` (`σ ≥ 1`) except with probability `e^{-(n-1)²}`, and
ES22 Lemma 9.2: hitting a cube after time s^2 (centre `-z`, `z ∈ c`) bounds the probability that `σB` enters the ball of
radius `r` around `z` after time `s²`, once for each centre.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ}

/-- The far event relative to a finite set `c` of centres, at radius `ρ`. -/
def step78FarCyl (n : ℕ) (ρ : ℝ) (c : Finset (Fin d → ℤ)) : Set (ℝ≥0 → Fin d → ℤ) :=
  {y | ∃ g ∈ step78Grid, (389 / 100 : ℝ) ^ n ≤ g ∧ (g : ℝ) < (4 : ℝ) ^ n ∧ ∃ z ∈ c, ‖y g - z‖ ≤ ρ}

theorem measurableSet_step78FarCyl (n : ℕ) (ρ : ℝ) (c : Finset (Fin d → ℤ)) :
    MeasurableSet (step78FarCyl n ρ c) := by
  have : step78FarCyl n ρ c = ⋃ g ∈ step78Grid, {y | (389 / 100 : ℝ) ^ n ≤ g ∧
      (g : ℝ) < (4 : ℝ) ^ n ∧ ∃ z ∈ c, ‖y g - z‖ ≤ ρ} := by
    ext y
    simp only [step78FarCyl, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [this]
  refine MeasurableSet.biUnion step78Grid_countable fun g _ => ?_
  by_cases h : (389 / 100 : ℝ) ^ n ≤ g ∧ (g : ℝ) < (4 : ℝ) ^ n
  · have : {y : ℝ≥0 → Fin d → ℤ | (389 / 100 : ℝ) ^ n ≤ g ∧ (g : ℝ) < (4 : ℝ) ^ n ∧
        ∃ z ∈ c, ‖y g - z‖ ≤ ρ} =
        (fun y : ℝ≥0 → Fin d → ℤ => y g) ⁻¹' {w | ∃ z ∈ c, ‖w - z‖ ≤ ρ} := by
      ext y; simp [h]
    rw [this]
    exact (measurable_pi_apply g) (Set.to_countable _).measurableSet
  · have : {y : ℝ≥0 → Fin d → ℤ | (389 / 100 : ℝ) ^ n ≤ g ∧ (g : ℝ) < (4 : ℝ) ^ n ∧
        ∃ z ∈ c, ‖y g - z‖ ≤ ρ} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      tauto
    rw [this]
    exact MeasurableSet.empty

variable {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ d β)}

/-- **The far window with centres.** -/
theorem step78_far_window (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) {s r ρ : ℝ} (hs : 0 < s)
    (hs2 : s ^ 2 ≤ (389 / 100 : ℝ) ^ n) (hr : ρ + ((4 : ℝ) ^ n) ^ indThetaH ≤ r)
    (hρ : 0 ≤ ρ) (c : Finset (Fin d → ℤ)) :
    (Pr.map (avoidPath N)) (step78FarCyl n ρ c) ≤
      ENNReal.ofReal (Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2))) +
        (c.card : ℝ≥0∞) * ENNReal.ofReal (ElboimSly.Brownian.Cfar d * (r / s) ^ (d - 2)) := by
  have hn1 : 1 ≤ n := by have := hp.eight_le; have := hp.lt; omega
  have hd3 : 3 ≤ d := by have := hp.five_le; omega
  have hh1 : (4 : ℝ) ^ n₀ < 4 ^ n := pow_lt_pow_right₀ (by norm_num) hp.lt
  obtain ⟨σ, hσ, hc⟩ := es4_hyp_d hp hN hh1 le_rfl
  rw [avoidLevel_pow n hn1] at hc
  set b : ℝ≥0 := ((4 : ℝ) ^ n).toNNReal with hb
  have hbR : (b : ℝ) = 4 ^ n := Real.coe_toNNReal _ (by positivity)
  set ε : ℝ := ((4 : ℝ) ^ n) ^ indThetaH with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨Q, hQ, hlaw, hB, hae, hfail⟩ :=
    Bridge.exists_standardBrownianMotion_of_admitsBMCoupling hc
  -- the index set of test times
  let I : Set ℝ≥0 := {g | g ∈ step78Grid ∧ (389 / 100 : ℝ) ^ n ≤ g ∧ (g : ℝ) < (4 : ℝ) ^ n}
  have hIb : ∀ g ∈ I, g ≤ b := by
    intro g hg
    rw [← NNReal.coe_le_coe, hbR]; exact hg.2.2.le
  have : Countable I := (step78Grid_countable.mono fun g hg => hg.1).to_subtype
  set S : Set (Set.Icc (0 : ℝ≥0) b → Fin d → ℤ) :=
    {w | ∃ g : I, ∃ z ∈ c, ‖w ⟨(g : ℝ≥0), bot_le, hIb g g.2⟩ - z‖ ≤ ρ} with hS
  have hSm : MeasurableSet S := by
    have : S = ⋃ g : I, {w : Set.Icc (0 : ℝ≥0) b → Fin d → ℤ |
        ∃ z ∈ c, ‖w ⟨(g : ℝ≥0), bot_le, hIb g g.2⟩ - z‖ ≤ ρ} := by
      ext w; simp [hS]
    rw [this]
    have hm : MeasurableSet {v : Fin d → ℤ | ∃ z ∈ c, ‖v - z‖ ≤ ρ} :=
      (Set.to_countable _).measurableSet
    exact MeasurableSet.iUnion fun g =>
      (measurable_pi_apply (X := fun _ : Set.Icc (0 : ℝ≥0) b => Fin d → ℤ)
        (⟨(g : ℝ≥0), bot_le, hIb g g.2⟩ : Set.Icc (0 : ℝ≥0) b)) hm
  set Φ : Ω → Set.Icc (0 : ℝ≥0) b → Fin d → ℤ := fun ω t => avoidWalk N ω ((t : ℝ≥0) : ℝ)
    with hΦ
  have hΦm : AEMeasurable Φ Pr := by
    have : Φ = (fun (x : ℝ≥0 → Fin d → ℤ) (t : Set.Icc (0 : ℝ≥0) b) => x t) ∘ avoidPath N := rfl
    rw [this]
    exact (Measurable.of_eval fun t => measurable_pi_apply _).comp_aemeasurable
      (aemeasurable_avoidPath hN)
  have hev : avoidPath N ⁻¹' (step78FarCyl n ρ c) = Φ ⁻¹' S := by
    ext ω
    constructor
    · rintro ⟨g, hg, h1, h2, z, hz, h⟩
      exact ⟨⟨g, hg, h1, h2⟩, z, hz, h⟩
    · rintro ⟨⟨g, hg, h1, h2⟩, z, hz, h⟩
      exact ⟨g, hg, h1, h2, z, hz, h⟩
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_avoidPath hN)
    (measurableSet_step78FarCyl n ρ c), hev]
  have hf : Measurable (fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) :=
    measurable_subtype_coe.comp measurable_fst
  have h1 : Pr (Φ ⁻¹' S) = Q ((fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' S) := by
    calc Pr (Φ ⁻¹' S) = (Pr.map Φ) S := (Measure.map_apply_of_aemeasurable hΦm hSm).symm
      _ = (Q.map (fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1)) S :=
        (congrArg (fun m => m S) hlaw).symm
      _ = _ := Measure.map_apply hf hSm
  rw [h1]
  set Bz := Bridge.zeroMod (Prod.snd : WalkPath d b × C(ℝ≥0, Fin d → ℝ) → _) with hBz
  set G : Set (WalkPath d b × C(ℝ≥0, Fin d → ℝ)) := {p | ENNReal.ofReal ε ≤
    ⨆ t : Set.Icc (0 : ℝ≥0) b,
      ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖} with hG
  set K : (Fin d → ℤ) → Set (WalkPath d b × C(ℝ≥0, Fin d → ℝ)) := fun z =>
    {p | ⨅ (t : ℝ≥0) (_ : s ^ 2 ≤ (t : ℝ)),
      ((‖(-(fun i => ((z i : ℤ) : ℝ))) + σ • Bz t p‖ : ℝ) : EReal) ≤ (r : EReal)} with hK
  have hsub : (fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' S ⊆ G ∪ ⋃ z ∈ c, K z := by
    intro p hp'
    by_cases hg : p ∈ G
    · exact Or.inl hg
    right
    obtain ⟨⟨g, hgI⟩, z, hz, hqL⟩ := hp'
    have hgt : ∀ t : Set.Icc (0 : ℝ≥0) b,
        ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖ < ε := by
      intro t
      have h2 : ⨆ t : Set.Icc (0 : ℝ≥0) b, ENNReal.ofReal
          ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • Bz (t : ℝ≥0) p‖ < ENNReal.ofReal ε :=
        not_le.1 hg
      have := lt_of_le_of_lt (le_iSup _ t) h2
      exact (ENNReal.ofReal_lt_ofReal_iff hε0).1 this
    have hn := hgt ⟨g, bot_le, hIb g hgI⟩
    have hqq : ‖(-(fun i => ((z i : ℤ) : ℝ))) + σ • Bz g p‖ < ρ + ε := by
      set a : Fin d → ℝ := fun i => ((p.1.1 ⟨g, bot_le, hIb g hgI⟩ i : ℤ) : ℝ) with ha
      have e : (-(fun i => ((z i : ℤ) : ℝ))) + σ • Bz g p =
          (a - (fun i => ((z i : ℤ) : ℝ))) - (a - σ • Bz g p) := by abel
      have h3 : ‖a - (fun i => ((z i : ℤ) : ℝ))‖ ≤ ρ := by
        have : a - (fun i => ((z i : ℤ) : ℝ)) =
            fun i => (((p.1.1 ⟨g, bot_le, hIb g hgI⟩ - z) i : ℤ) : ℝ) := by
          funext i; simp [ha]
        rw [this, avoid_norm_intCast_pi]; exact hqL
      rw [e]
      calc _ ≤ ‖a - (fun i => ((z i : ℤ) : ℝ))‖ + ‖a - σ • Bz g p‖ := norm_sub_le _ _
        _ < ρ + ε := by linarith
    have hqge : s ^ 2 ≤ (g : ℝ) := hs2.trans hgI.2.1
    have hmem : (⨅ (t : ℝ≥0) (_ : s ^ 2 ≤ (t : ℝ)),
        ((‖(-(fun i => ((z i : ℤ) : ℝ))) + σ • Bz t p‖ : ℝ) : EReal)) ≤ (r : EReal) :=
      le_trans (iInf₂_le g hqge) (by exact_mod_cast (hqq.le.trans hr))
    exact Set.mem_biUnion hz hmem
  have hKb : ∀ z ∈ c, Q (K z) ≤
      ENNReal.ofReal (ElboimSly.Brownian.Cfar d * (r / s) ^ (d - 2)) := by
    intro z _
    have hr0 : 0 < r := by linarith
    have hσ0 : 0 < σ := by linarith [hσ.1]
    have := hQ
    have hfh := ElboimSly.Brownian.far_hit_le (P := Q) (B := Bz) hB hd3
      (-(fun i => ((z i : ℤ) : ℝ))) hr0 hs hσ0
    refine hfh.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left hr0.le hs (le_mul_of_one_le_left hs.le hσ.1)) _)
      (ElboimSly.Brownian.Cfar_pos d).le
  calc Q ((fun p : WalkPath d b × C(ℝ≥0, Fin d → ℝ) => p.1.1) ⁻¹' S) ≤ Q (G ∪ ⋃ z ∈ c, K z) :=
        measure_mono hsub
    _ ≤ Q G + Q (⋃ z ∈ c, K z) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2))) +
        (c.card : ℝ≥0∞) * ENNReal.ofReal (ElboimSly.Brownian.Cfar d * (r / s) ^ (d - 2)) := by
        refine add_le_add hfail ?_
        calc Q (⋃ z ∈ c, K z) ≤ ∑ z ∈ c, Q (K z) := measure_biUnion_finset_le _ _
          _ ≤ ∑ z ∈ c, ENNReal.ofReal (ElboimSly.Brownian.Cfar d * (r / s) ^ (d - 2)) :=
            Finset.sum_le_sum hKb
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem step78_theta_le : ∀ m : ℕ, ((4 : ℝ) ^ m) ^ indThetaH ≤ (19 / 10 : ℝ) ^ m := by
  intro m
  have h4 : (4 : ℝ) ^ indThetaH ≤ 19 / 10 := by
    have h1 : ((4 : ℝ) ^ indThetaH) ^ 100 = 4 ^ 41 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      unfold indThetaH
      norm_num
    have h2 : ((4 : ℝ) ^ (41 : ℕ)) ≤ (19 / 10 : ℝ) ^ 100 := by norm_num
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (100 : ℕ) ≠ 0)
    rw [h1] at this
    linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]
  exact pow_le_pow_left₀ (by positivity) h4 m

/-- **The far event `E_far`** for the regenerated walk, given a finite cover `Z` of `V` by balls
of radius `1.9ⁿ`. -/
theorem step78_law_Sfar (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) (x : Fin d → ℤ)
    (V : Set (Fin d → ℤ)) (Z : Finset (Fin d → ℤ))
    (hcov : ∀ v ∈ V, ∃ z ∈ Z, ‖v - z‖ ≤ (19 / 10 : ℝ) ^ n) :
    (Pr.map (avoidPath N)) (step78Sfar n x V) ≤
      ENNReal.ofReal (Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2))) +
        (Z.card : ℝ≥0∞) * ENNReal.ofReal (ElboimSly.Brownian.Cfar d *
          (3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n)) ^ (d - 2)) := by
  classical
  have hpos : (0 : ℝ) < (389 / 100 : ℝ) ^ n := by positivity
  have hs : 0 < Real.sqrt ((389 / 100 : ℝ) ^ n) := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt ((389 / 100 : ℝ) ^ n) ^ 2 ≤ (389 / 100 : ℝ) ^ n :=
    (Real.sq_sqrt hpos.le).le
  have hθ := step78_theta_le n
  have h19 : (0 : ℝ) ≤ (19 / 10 : ℝ) ^ n := by positivity
  have hsub : step78Sfar n x V ⊆ step78FarCyl n (2 * (19 / 10 : ℝ) ^ n) (Z.image fun z => z - x) := by
    rintro y ⟨g, hg, h1, h2, v, hv, hvn⟩
    obtain ⟨z, hz, hvz⟩ := hcov v hv
    refine ⟨g, hg, h1, h2, z - x, Finset.mem_image.2 ⟨z, hz, rfl⟩, ?_⟩
    have e : y g - (z - x) = (x + y g - v) + (v - z) := by abel
    rw [e]
    calc _ ≤ ‖x + y g - v‖ + ‖v - z‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  refine (measure_mono hsub).trans ?_
  refine (step78_far_window hp hN (r := 3 * (19 / 10 : ℝ) ^ n) hs hs2 (by linarith) (by positivity)
    _).trans ?_
  exact add_le_add le_rfl (mul_le_mul_left (by exact_mod_cast Finset.card_image_le) _)

end ElboimSly.Paper.Step

end
