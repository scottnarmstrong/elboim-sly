/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.LawInvariance
public import ElboimSly.Foundations.Interchange.LatticeGroup
import Mathlib

/-!
# Stationary increments of the cyclic walk (deterministic part)

Stationary increments of the cyclic walk, proof (before taking laws).

For a good configuration `ν`, `a ≥ 0` and `x ∈ ℤᵈ`, put `M_x ν := (translation by -x)_* (ρ_{-a})_* ν`.
Then `W^ν(a + s) - x = W^{M_x ν}(s)` on `{W^ν(a) = x}`, and `W^ν(a) = x` iff the
trajectory of `M_x ν` from `(-x, -a)` is at `0` at time `0`.
-/

@[expose] public section

open MeasureTheory ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem trajProc_eq_fwdTraj (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) (s : ℝ≥0) :
    trajProc ν x a s = fwdTraj hν x a (a + s) := by
  rw [trajProc_of_good hν]
  simp [fwdTraj, fwdReal]

theorem trajProc_restart (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) (t s : ℝ≥0) :
    trajProc ν (trajProc ν y b t) (b + t) s = trajProc ν y b (t + s) := by
  rw [trajProc_eq_fwdTraj hν, trajProc_eq_fwdTraj hν, trajProc_eq_fwdTraj hν]
  rw [← fwdTraj_restart hν y (a := b) (c := b + t) (by simp) (t := b + t + s) (by simp)]
  congr 1; push_cast; ring

/-- `M_x ν`: translate by `-x` after rotating the circle by `-a`. -/
noncomputable def statM (x : Fin d → ℤ) (a : ℝ≥0) (ν : Measure (RingSpace d β)) :
    Measure (RingSpace d β) :=
  latticeMeasure (LatticeAut.translate (-x)) (rotateMeasure (-(a : ℝ)) ν)

theorem trajProc_statM_neg (hν : Good ν) (x : Fin d → ℤ) (a : ℝ≥0) (s : ℝ≥0) :
    trajProc (statM x a ν) (-x) (-(a : ℝ)) s = trajProc ν 0 0 s + -x := by
  have h1 := trajProc_latticeMeasure (good_rotateMeasure (-(a : ℝ)) hν)
    (LatticeAut.translate (-x)) 0 (-(a : ℝ))
  have h2 := trajProc_rotateMeasure hν (-(a : ℝ)) 0 0
  rw [zero_add] at h2
  have e : (LatticeAut.translate (-x)).toEquiv 0 = -x := by simp [LatticeAut.translate]
  rw [e] at h1
  unfold statM
  rw [h1, h2]
  simp [LatticeAut.translate]

theorem trajProc_statM_zero (hν : Good ν) (x : Fin d → ℤ) (a : ℝ≥0)
    (hx : trajProc ν 0 0 a = x) (s : ℝ≥0) :
    trajProc (statM x a ν) 0 0 s = trajProc ν 0 0 (a + s) - trajProc ν 0 0 a := by
  have h1 := trajProc_latticeMeasure (good_rotateMeasure (-(a : ℝ)) hν)
    (LatticeAut.translate (-x)) x 0
  have h2 := trajProc_rotateMeasure hν (-(a : ℝ)) x (a : ℝ)
  rw [add_neg_cancel] at h2
  have e : (LatticeAut.translate (-x)).toEquiv x = 0 := by simp [LatticeAut.translate]
  rw [e] at h1
  have h3 := trajProc_restart hν 0 0 a s
  rw [hx, zero_add] at h3
  unfold statM
  rw [h1]
  beta_reduce
  rw [h2, h3, hx]
  simp [LatticeAut.translate, sub_eq_add_neg, add_comm]

/-- The events `{trajProc μ (-x) (-a) a = 0}` partition the good configurations. -/
theorem existsUnique_start (hμ : Good ν) (a : ℝ≥0) :
    ∃! x : Fin d → ℤ, trajProc ν (-x) (-(a : ℝ)) a = 0 := by
  have hab : -(a : ℝ) ≤ 0 := by simp
  set y0 := bwdTraj hμ 0 0 (-(a : ℝ)) with hy0
  have key : ∀ y, trajProc ν y (-(a : ℝ)) a = 0 ↔ y = y0 := by
    intro y
    rw [trajProc_eq_fwdTraj hμ, neg_add_cancel]
    constructor
    · intro h
      have hf := (fwdTraj_isPathOn hμ y (-(a : ℝ)) 0)
      have := bwdTraj_eq_of_isPathOn hμ (y := 0) (a := -(a : ℝ)) (b := 0) hab hf h
        (-(a : ℝ)) ⟨le_rfl, hab⟩
      rw [fwdTraj_self] at this
      exact this
    · rintro rfl
      have hb := (bwdTraj_isPathOn hμ 0 (-(a : ℝ)) 0)
      have := fwdTraj_eq_of_isPathOn hμ (x := y0) hab hb rfl 0 ⟨hab, le_rfl⟩
      rw [bwdTraj_self] at this
      exact this.symm
  refine ⟨-y0, (key _).mpr (by simp), fun x hx => ?_⟩
  have := (key (-x)).mp hx
  rw [← neg_neg x, this]

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (RingSpace d β)} {P : Measure Ω}

theorem law_statM (h : IsPoissonPointProcess N (ringIntensity d β) P) (x : Fin d → ℤ) (a : ℝ≥0) :
    P.map (fun ω => statM x a (N ω)) = P.map N := by
  have h1 := law_latticeMeasure (isPoissonPointProcess_rotate h (-(a : ℝ)))
    (LatticeAut.translate (-x))
  have h2 := law_rotateMeasure h (-(a : ℝ))
  exact h1.trans h2

/-- Stationary increments of the cyclic walk. The process `(W(a+s) - W(a))_{s≥0}` has the law of
`(W(s))_{s≥0}` on `(ℤᵈ)^{[0,∞)}` with the product σ-algebra. Here `W(t) = trajProc (N ω) 0 0 t`
is the forward trajectory from `(0,0)`, the cyclic walk on `t ≥ 0` (constant off `Good`). -/
theorem cyc_stationary (h : IsPoissonPointProcess N (ringIntensity d β) P) (a : ℝ≥0) :
    P.map (fun ω s => trajProc (N ω) 0 0 (a + s) - trajProc (N ω) 0 0 a) =
      P.map (fun ω s => trajProc (N ω) 0 0 s) := by
  have hN : Measurable N := h.1
  have hΦ : Measurable (fun μ : Measure (RingSpace d β) => fun s : ℝ≥0 => trajProc μ 0 0 s) :=
    measurable_trajProc 0 0
  have hX : Measurable (fun μ : Measure (RingSpace d β) => fun s : ℝ≥0 =>
      trajProc μ 0 0 (a + s) - trajProc μ 0 0 a) :=
    measurable_pi_iff.mpr fun s =>
      ((measurable_pi_apply (a + s)).comp hΦ).sub ((measurable_pi_apply a).comp hΦ)
  ext F hF
  have hXN : Measurable (fun ω s => trajProc (N ω) 0 0 (a + s) - trajProc (N ω) 0 0 a) :=
    hX.comp hN
  have hΦN : Measurable (fun ω s => trajProc (N ω) 0 0 s) := hΦ.comp hN
  rw [Measure.map_apply hXN hF, Measure.map_apply hΦN hF]
  set X := fun μ : Measure (RingSpace d β) => fun s : ℝ≥0 =>
    trajProc μ 0 0 (a + s) - trajProc μ 0 0 a with hXdef
  set Φ := fun μ : Measure (RingSpace d β) => fun s : ℝ≥0 => trajProc μ 0 0 s with hΦdef
  have hEx : ∀ x, MeasurableSet {μ : Measure (RingSpace d β) | trajProc μ 0 0 a = x} := fun x =>
    measurableSet_eq_fun ((measurable_pi_apply a).comp hΦ) measurable_const
  let G : (Fin d → ℤ) → Set (Measure (RingSpace d β)) := fun x =>
    {μ | trajProc μ (-x) (-(a : ℝ)) a = 0} ∩ Φ ⁻¹' F
  have hG : ∀ x, MeasurableSet (G x) := fun x =>
    (measurableSet_eq_fun ((measurable_pi_apply a).comp (measurable_trajProc (-x) (-(a : ℝ))))
      measurable_const).inter (hΦ hF)
  have hgood := ae_good h
  show P (N ⁻¹' (X ⁻¹' F)) = P (N ⁻¹' (Φ ⁻¹' F))
  -- Step A: decompose according to the value of `W(a)`.
  have hA : N ⁻¹' (X ⁻¹' F) = ⋃ x, N ⁻¹' (X ⁻¹' F ∩ {μ | trajProc μ 0 0 a = x}) := by
    ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun x =>
      N ⁻¹' (X ⁻¹' F ∩ {μ | trajProc μ 0 0 a = x})) := by
    intro x y hxy
    refine Set.disjoint_left.mpr fun ω h1 h2 => hxy ?_
    exact h1.2.symm.trans h2.2
  rw [hA, measure_iUnion hdisj (fun x => hN ((hX hF).inter (hEx x)))]
  -- Step B: each term equals `P (N ⁻¹' G x)`.
  have hB : ∀ x, P (N ⁻¹' (X ⁻¹' F ∩ {μ | trajProc μ 0 0 a = x})) = P (N ⁻¹' (G x)) := by
    intro x
    have hae : N ⁻¹' (X ⁻¹' F ∩ {μ | trajProc μ 0 0 a = x}) =ᵐ[P]
        (fun ω => statM x a (N ω)) ⁻¹' (G x) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hgood] with ω hω
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, G]
      rw [trajProc_statM_neg hω]
      constructor
      · rintro ⟨hF1, hx⟩
        have hk : (fun s => trajProc (statM x a (N ω)) 0 0 s) = X (N ω) := by
          funext s; exact trajProc_statM_zero hω x a hx s
        refine ⟨?_, ?_⟩
        · simp [hx]
        · show Φ (statM x a (N ω)) ∈ F
          rw [show Φ (statM x a (N ω)) = X (N ω) from hk]; exact hF1
      · rintro ⟨h1, h2⟩
        have hx : trajProc (N ω) 0 0 a = x := add_neg_eq_zero.mp h1
        have hk : (fun s => trajProc (statM x a (N ω)) 0 0 s) = X (N ω) := by
          funext s; exact trajProc_statM_zero hω x a hx s
        refine ⟨?_, hx⟩
        have : Φ (statM x a (N ω)) ∈ F := h2
        rwa [show Φ (statM x a (N ω)) = X (N ω) from hk] at this
    rw [measure_congr hae]
    have hmeas : Measurable (fun ω => statM x a (N ω)) := by
      unfold statM
      exact (Measure.measurable_map _ (ringMapEquiv _ _).measurable).comp
        ((Measure.measurable_map _ (ringMapEquiv _ _).measurable).comp hN)
    rw [← Measure.map_apply hmeas (hG x), law_statM h x a, Measure.map_apply hN (hG x)]
  simp_rw [hB]
  have hGood : MeasurableSet {μ : Measure (RingSpace d β) | Good μ} := measurableSet_good
  have hC : ∀ x, P (N ⁻¹' G x) = P (N ⁻¹' (G x ∩ {μ | Good μ})) := fun x =>
    measure_congr (Filter.eventuallyEqSet_iff.2 (by
      filter_upwards [hgood] with ω hω
      simp [hω]))
  simp_rw [hC]
  have hdisj2 : Pairwise (Function.onFun Disjoint fun x => N ⁻¹' (G x ∩ {μ | Good μ})) := by
    intro x y hxy
    refine Set.disjoint_left.mpr fun ω h1 h2 => hxy ?_
    have hω : Good (N ω) := h1.2
    obtain ⟨x0, _, hu⟩ := existsUnique_start hω a
    exact (hu x h1.1.1).trans (hu y h2.1.1).symm
  rw [← measure_iUnion hdisj2 (fun x => hN ((hG x).inter hGood))]
  have hU : (⋃ x, N ⁻¹' (G x ∩ {μ | Good μ})) = N ⁻¹' (Φ ⁻¹' F ∩ {μ | Good μ}) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, G]
    constructor
    · rintro ⟨x, ⟨_, h2⟩, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      obtain ⟨x, hx, _⟩ := existsUnique_start h3 a
      exact ⟨x, ⟨hx, h2⟩, h3⟩
  rw [hU]
  exact measure_congr (Filter.eventuallyEqSet_iff.2 (by
    filter_upwards [hgood] with ω hω
    simp [hω]))

end Law

end ElboimSly.Cyclic

end
