/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactGamma
public import Mathlib

/-!
# The scenario prevents a further contact

Contacts are few (ii), "The scenario prevents a further contact".

On `Ḡ ∩ {κ_m < ∞}`, if the shifted pair `θ_{κ_m} X̄` lies in `Γ_{D(κ_m)}`, then `κ_{m+1} = ∞`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ}

/-- Rational times suffice for a right-continuous path: a property of the values at all
rational times holds at all times. -/
theorem forall_of_rat {V : Type*} {f : ℝ≥0 → V} (hrc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s)
    {P : V → Prop} (h : ∀ q : ℚ, 0 ≤ q → P (f (ratNN q))) (s : ℝ≥0) : P (f s) := by
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hrc s)
  obtain ⟨q, hq1, hq2⟩ := exists_ratNN_btwn (show s < u' from hu')
  have hq0 : 0 ≤ q := by
    by_contra hneg
    push Not at hneg
    have : ratNN q = 0 := by unfold ratNN; exact Real.toNNReal_of_nonpos (by exact_mod_cast hneg.le)
    rw [this] at hq1
    exact absurd hq1 (not_lt.2 bot_le)
  have := hsub ⟨hq1.le, hq2⟩
  rw [mem_ofPred_eq] at this
  rw [← this]; exact h q hq0

/-- Rational times in `[0, 1)` plus the endpoint `1` suffice. -/
theorem forall_Icc_of_rat {V : Type*} {f : ℝ≥0 → V} (hrc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s)
    {P : V → Prop} (h : ∀ q : ℚ, 0 ≤ q → q ≤ 1 → P (f (ratNN q))) (h1 : P (f 1)) (s : ℝ≥0)
    (hs : s ≤ 1) : P (f s) := by
  rcases hs.eq_or_lt with rfl | hlt
  · exact h1
  · obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hrc s)
    obtain ⟨q, hq1, hq2⟩ := exists_ratNN_btwn (lt_min (show s < u' from hu') hlt)
    have hq0 : 0 ≤ q := by
      by_contra hneg
      push Not at hneg
      have : ratNN q = 0 := by
        unfold ratNN; exact Real.toNNReal_of_nonpos (by exact_mod_cast hneg.le)
      rw [this] at hq1
      exact absurd hq1 (not_lt.2 bot_le)
    have hq3 : q ≤ 1 := by
      have : ratNN q ≤ 1 := (hq2.trans_le (min_le_right _ _)).le
      unfold ratNN at this
      have h' : ((q : ℚ) : ℝ) ≤ 1 := by simpa using (Real.toNNReal_le_iff_le_coe).1 this
      exact_mod_cast h'
    have := hsub ⟨hq1.le, hq2.trans_le (min_le_left _ _)⟩
    rw [mem_ofPred_eq] at this
    rw [← this]; exact h q hq0 hq3

theorem fstP_theta_drvPair {Ω : Type} {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)} (ω : Ω)
    (κ s : ℝ≥0) :
    fstP (theta κ (drvPair Ñ ω)) s = drvX Ñ 0 ω (κ + s) - drvX Ñ 0 ω κ := by
  funext i
  simp only [fstP, theta, drvPair, Pi.sub_apply]
  rw [Fin.append_left, Fin.append_left]

theorem sndP_theta_drvPair {Ω : Type} {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)} (ω : Ω)
    (κ s : ℝ≥0) :
    sndP (theta κ (drvPair Ñ ω)) s = drvX Ñ 1 ω (κ + s) - drvX Ñ 1 ω κ := by
  funext i
  simp only [sndP, theta, drvPair, Pi.sub_apply]
  rw [Fin.append_right, Fin.append_right]

section

variable {Ω : Type} [MeasurableSpace Ω] {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

omit [MeasurableSpace Ω] in
theorem drvData {ω : Ω} (hG : ω ∈ drvGood Ñ) (a b : Fin d → ℤ) :
    TwoParticleData a b (drvX Ñ 0 ω) (drvX Ñ 1 ω) (drvTwo Ñ a b ω) :=
  ⟨drivers_isDrivingPath 0 ω, drivers_isDrivingPath 1 ω,
    fun r hr hr' => drivers_no_common_jump hG r ⟨hr, hr'⟩, isTwoParticle_drvTwo a b ω⟩

omit [MeasurableSpace Ω] in
theorem kap_succ_eq_top_of_scenario [NeZero d] (a b : Fin d → ℤ) (hab : a ≠ b) (m : ℕ) {ω : Ω}
    (hG : ω ∈ drvGood Ñ) (hκ : kap Ñ a b m ω ≠ ⊤)
    (hΓ : theta (stopReal (kap Ñ a b m) ω) (drvPair Ñ ω) ∈
      contactGamma (drvD Ñ a b ω (stopReal (kap Ñ a b m) ω))) :
    kap Ñ a b (m + 1) ω = ⊤ := by
  set κ := stopReal (kap Ñ a b m) ω with hκdef
  set y₀ := drvD Ñ a b ω κ with hy₀
  set v₀ := (escDir y₀).vec with hv₀
  have hdat := drvData hG a b
  have hpos : 0 < ‖y₀‖ := drvD_kap_pos a b hab m hG hκ
  have hle : ‖y₀‖ ≤ 1 := drvD_kap_mem a b m hκ
  have hy0 : y₀ ≠ 0 := norm_pos_iff.1 hpos
  have h2 : 2 ≤ ‖y₀ + v₀‖ := two_le_norm_add_escDir hy0 hle
  have hy0' : y₀ + v₀ ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2; norm_num at h2
  obtain ⟨g1, g2, g3, g4⟩ := hΓ
  rw [fstP_theta_drvPair] at g1
  rw [sndP_theta_drvPair] at g2
  simp only [fstP_theta_drvPair, sndP_theta_drvPair] at g3 g4
  set x₁ := drvX Ñ 0 ω with hx₁
  set x₂ := drvX Ñ 1 ω with hx₂
  set y := drvTwo Ñ a b ω with hy
  have hrc₁ := hdat.hx₁.step.rc
  have hrc₂ := hdat.hx₂.step.rc
  have hshift : ∀ (g : ℝ≥0 → Fin d → ℤ), (∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s) →
      ∀ c s, ∀ᶠ u in 𝓝[≥] s, g (c + u) = g (c + s) := by
    intro g hg c s
    have ht : Tendsto (fun u : ℝ≥0 => c + u) (𝓝[≥] s) (𝓝[≥] (c + s)) :=
      (continuousWithinAt_const.add continuousWithinAt_id).tendsto_nhdsWithin
        (fun u (hu : s ≤ u) => (show c + s ≤ c + u by gcongr))
    exact ht.eventually (hg (c + s))
  -- x₁ constant, x₂ ∈ {0, v₀}
  have hc1 : ∀ s, s ≤ 1 → x₁ (κ + s) - x₁ κ = 0 := fun s hs =>
    forall_Icc_of_rat (f := fun u => x₁ (κ + u) - x₁ κ)
      (fun s => (hshift x₁ hrc₁ κ s).mono fun u hu => by simp only [hu])
      (P := fun z => z = 0) (fun q h0 h1 => (g3 q h0 h1).1) g1 s hs
  have hc2 : ∀ s, s ≤ 1 → x₂ (κ + s) - x₂ κ = 0 ∨ x₂ (κ + s) - x₂ κ = v₀ := fun s hs =>
    forall_Icc_of_rat (f := fun u => x₂ (κ + u) - x₂ κ)
      (fun s => (hshift x₂ hrc₂ κ s).mono fun u hu => by simp only [hu])
      (P := fun z => z = 0 ∨ z = v₀) (fun q h0 h1 => (g3 q h0 h1).2) (Or.inr g2) s hs
  have hesc : ∀ u : ℝ≥0, 2 ≤ ‖(y₀ + v₀) + (((x₂ (κ + (1 + u)) - x₂ κ) -
      (x₁ (κ + (1 + u)) - x₁ κ)) - ((x₂ (κ + 1) - x₂ κ) - (x₁ (κ + 1) - x₁ κ)))‖ := by
    intro u
    refine forall_of_rat (f := fun u => ((x₂ (κ + (1 + u)) - x₂ κ) -
      (x₁ (κ + (1 + u)) - x₁ κ)) - ((x₂ (κ + 1) - x₂ κ) - (x₁ (κ + 1) - x₁ κ)))
      (fun s => ?_) (P := fun z => 2 ≤ ‖(y₀ + v₀) + z‖) (fun q h0 => g4 q h0) u
    filter_upwards [hshift x₁ hrc₁ (κ + 1) s, hshift x₂ hrc₂ (κ + 1) s] with w e1 e2
    simp only [← add_assoc] at e1 e2 ⊢
    rw [e1, e2]
  have hD : y κ - (a + x₁ κ) = y₀ := by
    rw [hy₀]; unfold drvD; rw [sub_sub]
  have hx1 : ∀ s, κ ≤ s → s ≤ κ + 1 → x₁ s = x₁ κ := by
    intro s hs1 hs2
    have := hc1 (s - κ) (tsub_le_iff_left.2 hs2)
    rw [add_tsub_cancel_of_le hs1] at this
    exact sub_eq_zero.1 this
  have hx2 : ∀ s, κ ≤ s → s ≤ κ + 1 → x₂ s - x₂ κ = 0 ∨ x₂ s - x₂ κ = v₀ := by
    intro s hs1 hs2
    have := hc2 (s - κ) (tsub_le_iff_left.2 hs2)
    rwa [add_tsub_cancel_of_le hs1] at this
  have hp1 := hdat.phase1 hab hD hy0 hy0' hx1 hx2
  have hDκ1 : y (κ + 1) - (a + x₁ (κ + 1)) = y₀ + v₀ := by
    rw [hp1 (κ + 1) le_self_add le_rfl, g2]
  have hesc2 : ∀ s, κ + 1 ≤ s →
      2 ≤ ‖(y₀ + v₀) + ((x₂ s - x₁ s) - (x₂ (κ + 1) - x₁ (κ + 1)))‖ := by
    intro s hs
    have := hesc (s - (κ + 1))
    have e : κ + (1 + (s - (κ + 1))) = s := by
      rw [← add_assoc, add_tsub_cancel_of_le hs]
    rw [e] at this
    convert this using 2
    abel
  have hp2 := hdat.phase2 hab hDκ1 hesc2
  by_contra hne
  have hD' := drvD_kap_mem a b (m + 1) hne
  have hge := stopReal_kap_succ a b m hne
  have hs := hp2 _ hge
  have hdn : drvD Ñ a b ω (stopReal (kap Ñ a b (m + 1)) ω) =
      (y₀ + v₀) + ((x₂ (stopReal (kap Ñ a b (m + 1)) ω) - x₁ (stopReal (kap Ñ a b (m + 1)) ω)) -
        (x₂ (κ + 1) - x₁ (κ + 1))) := by
    rw [← hs]; unfold drvD; rw [sub_sub]
  rw [hdn] at hD'
  have := hesc2 _ hge
  linarith

end

end ElboimSly.Paper
