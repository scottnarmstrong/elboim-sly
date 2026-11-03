/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.CountSigma
public import ElboimSly.Foundations.SRW.ShiftWalk
public import ElboimSly.Foundations.SRW.Admissible
public import ElboimSly.Foundations.SRW.GoodAe
public import Mathlib

/-!
# The increments of the walk are measurable for the count `σ`-algebras

Count calculus (e).

For `0 ≤ a ≤ s ≤ b` the increment `X(s) - X(a)` is measurable for `𝒩^G_{D × (a,b]}`
(`modNull` of `rectSigma`), and also for `b = ∞`. Hence the natural filtration of the canonical walk
is contained in `𝒩^G_{D × (0,t]}` and `σ(θ_t X) ⊆ 𝒩^G_{D × (t,∞)}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)}
  {P : Measure Ω}

/-- The increment `X(s) - X(a)` is measurable for `𝒩^G_U` as soon as the rectangle
`D × (a,s]` lies in `U`. -/
theorem measurable_walk_sub_modNull (hN : Measurable N) {a s : ℝ} (ha : 0 ≤ a) (has : a ≤ s)
    {U : Set (Dir d × ℝ)} (hU : univ ×ˢ Ioc a s ⊆ U) :
    Measurable[@modNull Ω mΩ (goodEvent d N) (rectSigma N U)]
      (fun ω => walk d (N ω) s - walk d (N ω) a) := by
  have hf : Measurable (fun ω => walk d (N ω) s - walk d (N ω) a) :=
    ((measurable_walk d s).comp hN).sub ((measurable_walk d a).comp hN)
  have hI : IsRectInterval (Ioc a s) :=
    ⟨Set.ordConnected_Ioc, Metric.isBounded_Ioc a s, fun x hx => lt_of_le_of_lt ha hx.1⟩
  have hc : ∀ v : Dir d, Measurable[rectSigma N U]
      (fun ω => natOf (N ω (({v} : Set (Dir d)) ×ˢ Ioc a s))) := fun v =>
    measurable_natOf.comp (measurable_rect_count N U v hI
      (fun x hx => hU ⟨mem_univ _, (mem_prod.1 hx).2⟩))
  have hF : Measurable[rectSigma N U]
      (fun ω (v : Dir d) => natOf (N ω (({v} : Set (Dir d)) ×ˢ Ioc a s))) := by
    let : MeasurableSpace Ω := rectSigma N U
    exact measurable_pi_iff.2 hc
  have hdisc : ∀ z : Fin d → ℤ, MeasurableSet {n : Dir d → ℕ | ∑ v, (n v : ℤ) • v.vec = z} :=
    fun z => (Set.to_countable _).measurableSet
  let : MeasurableSpace Ω := @modNull Ω mΩ (goodEvent d N) (rectSigma N U)
  refine measurable_to_countable' fun z => ?_
  refine ⟨hf (measurableSet_singleton z), (fun ω (v : Dir d) =>
    natOf (N ω (({v} : Set (Dir d)) ×ˢ Ioc a s))) ⁻¹'
      {n : Dir d → ℕ | ∑ v, (n v : ℤ) • v.vec = z}, hF (hdisc z), ?_⟩
  ext ω
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := walk_sub_eq h2 ha has
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq] at h1 ⊢
    rw [← this]; exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := walk_sub_eq h2 ha has
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq] at h1 ⊢
    rw [this]; exact h1

/-- Count calculus (e): the natural filtration of the canonical walk is contained
in `𝒩^G_{D × (0,t]}`. -/
theorem natFil_canonical_le (hN : Measurable N) (t : ℝ≥0) :
    natFil (canonical d N) t ≤
      @modNull Ω mΩ (goodEvent d N) (rectSigma N (univ ×ˢ Ioc 0 (t : ℝ))) := by
  refine iSup₂_le fun s hs => ?_
  have h := measurable_walk_sub_modNull (d := d) (N := N) hN (le_refl (0 : ℝ)) s.2
    (U := univ ×ˢ Ioc 0 (t : ℝ)) (prod_mono subset_rfl (Ioc_subset_Ioc_right (by exact_mod_cast hs)))
  have e : (fun ω => canonical d N ω s) = fun ω => walk d (N ω) s - walk d (N ω) 0 := by
    funext ω; simp [canonical, walk_zero]
  rw [e]
  exact h.comap_le

/-- Count calculus (e): `σ(θ_t X) ⊆ 𝒩^G_{D × (t,∞)}`. -/
theorem comap_theta_canonical_le (hN : Measurable N) (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω => theta t (canonical d N ω)) inferInstance ≤
      @modNull Ω mΩ (goodEvent d N) (rectSigma N (univ ×ˢ Ioi (t : ℝ))) := by
  have hm : Measurable[@modNull Ω mΩ (goodEvent d N) (rectSigma N (univ ×ˢ Ioi (t : ℝ)))]
      (fun ω => theta t (canonical d N ω)) := by
    let : MeasurableSpace Ω :=
      @modNull Ω mΩ (goodEvent d N) (rectSigma N (univ ×ˢ Ioi (t : ℝ)))
    refine measurable_pi_iff.2 fun s => ?_
    have h := measurable_walk_sub_modNull (mΩ := mΩ) (d := d) (N := N) hN t.2 (a := (t : ℝ))
      (s := (t : ℝ) + s) (by linarith [s.2])
      (U := univ ×ˢ Ioi (t : ℝ)) (prod_mono subset_rfl (fun _ hx => hx.1))
    have e : (fun ω => theta t (canonical d N ω) s) =
        fun ω => walk d (N ω) ((t : ℝ) + s) - walk d (N ω) t := by
      funext ω; simp [theta, canonical]
    rw [e]
    exact h
  exact hm.comap_le

/-- Count calculus (e), upper bound `b < ∞`: the increment over `(a,s]` is
`𝒩^G_{D × (a,b]}`-measurable for `s ≤ b`. -/
theorem measurable_walk_sub_Ioc (hN : Measurable N) {a s b : ℝ} (ha : 0 ≤ a) (has : a ≤ s)
    (hsb : s ≤ b) :
    Measurable[@modNull Ω mΩ (goodEvent d N) (rectSigma N (univ ×ˢ Ioc a b))]
      (fun ω => walk d (N ω) s - walk d (N ω) a) :=
  measurable_walk_sub_modNull hN ha has (prod_mono subset_rfl (Ioc_subset_Ioc_right hsb))

/-- Count calculus (e), `b = ∞`. -/
theorem measurable_walk_sub_Ioi (hN : Measurable N) {a s : ℝ} (ha : 0 ≤ a) (has : a ≤ s) :
    Measurable[@modNull Ω mΩ (goodEvent d N) (rectSigma N (univ ×ˢ Ioi a))]
      (fun ω => walk d (N ω) s - walk d (N ω) a) :=
  measurable_walk_sub_modNull hN ha has (prod_mono subset_rfl (fun _x hx => hx.1))

end SRW
end ElboimSly
