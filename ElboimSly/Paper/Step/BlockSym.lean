/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelTrunc
public import ElboimSly.Foundations.Interchange.LatticeGroup
public import Mathlib

/-!
# Lattice symmetries of the stopped regenerated path and of the block functional

Lattice symmetry of the regenerated walk, used in ES22 Lemma 7.6 (Step 1: (ii), (iii)).

For a lattice automorphism `g` fixing `0`, the law `ppLaw Pe N h` of the stopped regenerated path
is invariant under `w ↦ g ∘ w` (`ppLaw_gPath`). For sign changes (`latticeSign`) and coordinate
transpositions (`permute`), which are isometries of the sup norm, the truncated endpoint
`truncEnd` is equivariant, so its law is invariant (`truncEnd_signs_law`) and all of its
coordinates have the same second moment (`integral_truncEnd_sq_eq`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ}

/-- The action of a lattice automorphism on paths. -/
def gPath (g : LatticeAut d) (w : ℝ≥0 → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ := fun t => g.toEquiv (w t)

theorem measurable_gPath (g : LatticeAut d) : Measurable (gPath g) :=
  measurable_pi_iff.2 fun t => (measurable_of_countable g.toEquiv).comp (measurable_pi_apply t)

section PPP

variable {β : ℝ} [Fact (0 < β)] {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe}
  {N : Ωe → Measure (ℕ × RingSpace d β)}

/-- The law of the stopped regenerated path is invariant under every lattice automorphism fixing
`0` (lattice symmetry of the regenerated walk). -/
theorem ppLaw_gPath
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (g : LatticeAut d) (hg : g.toEquiv 0 = 0) (h : ℝ≥0) :
    (ppLaw Pe N h).map (gPath g) = ppLaw Pe N h := by
  have hae := aemeasurable_ppPath hN
  have key := step_symmetry_law hN g hg
  have e1 : (Pe.map (ppPath N)).map (gPath g) = Pe.map (ppPath N) := by
    rw [AEMeasurable.map_map_of_aemeasurable (measurable_gPath g).aemeasurable hae]
    exact key
  have hcomm : (gPath g ∘ SRW.stopPath h) = (SRW.stopPath h ∘ gPath g) := by
    funext w t; simp [gPath, SRW.stopPath]
  unfold ppLaw
  rw [Measure.map_map (measurable_gPath g) (SRW.measurable_stopPath h), hcomm,
    ← Measure.map_map (SRW.measurable_stopPath h) (measurable_gPath g), e1]

end PPP

/-- A sign change `x ↦ ε x`, `ε_k = ±1`, as a lattice automorphism. -/
def latticeSign (ε : Fin d → ℤ) (hε : ∀ k, ε k = 1 ∨ ε k = -1) : LatticeAut d where
  toEquiv :=
    { toFun := fun x => ε * x
      invFun := fun x => ε * x
      left_inv := fun x => by
        funext k; rcases hε k with h | h <;> simp [h]
      right_inv := fun x => by
        funext k; rcases hε k with h | h <;> simp [h] }
  adj u v := by
    unfold LatticeAdj
    refine Iff.of_eq (congrArg (· = 1) (Finset.sum_congr rfl fun k _ => ?_))
    simp only [Equiv.coe_fn_mk, Pi.mul_apply]
    rw [← mul_sub, abs_mul]
    rcases hε k with h | h <;> simp [h]

theorem latticeSign_apply (ε : Fin d → ℤ) (hε : ∀ k, ε k = 1 ∨ ε k = -1) (x : Fin d → ℤ) :
    (latticeSign ε hε).toEquiv x = ε * x := rfl

theorem norm_sign_mul (ε : Fin d → ℤ) (hε : ∀ k, ε k = 1 ∨ ε k = -1) (x : Fin d → ℤ) :
    ‖ε * x‖ = ‖x‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    have := norm_le_pi_norm x k
    rcases hε k with h | h <;> simpa [h] using this
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    have := norm_le_pi_norm (ε * x) k
    rcases hε k with h | h <;> simpa [h] using this

theorem norm_perm_apply (σ : Equiv.Perm (Fin d)) (x : Fin d → ℤ) :
    ‖(LatticeAut.permute σ).toEquiv x‖ = ‖x‖ := by
  have hx : (LatticeAut.permute σ).toEquiv x = fun i => x (σ i) := by
    funext i; simp [LatticeAut.permute]
  rw [hx]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => norm_le_pi_norm x (σ k)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    have := norm_le_pi_norm (fun i => x (σ i)) (σ.symm k)
    simpa using this

/-- Equivariance of `truncEnd` under a norm-preserving automorphism fixing `0`. -/
theorem truncEnd_gPath (g : LatticeAut d) (hg : g.toEquiv 0 = 0)
    (hiso : ∀ x, ‖g.toEquiv x‖ = ‖x‖) (h : ℝ≥0) (K : ℝ) (w : ℝ≥0 → Fin d → ℤ) :
    truncEnd h K (gPath g w) = g.toEquiv (truncEnd h K w) := by
  have hmem : gPath g w ∈ farSet K h ↔ w ∈ farSet K h := by
    constructor <;> intro hm <;> obtain ⟨q, hq, hk⟩ := mem_iUnion₂.1 hm <;>
      exact mem_iUnion₂.2 ⟨q, hq, by simpa [gPath, hiso] using hk⟩
  by_cases hw : w ∈ farSet K h
  · simp [truncEnd, hw, hmem.2 hw, hg]
  · simp [truncEnd, hw, hmem, gPath]

/-- The block functional `w ↦ T^{-1/2} · 𝟙{sup_{s ≤ T} ‖w(s)‖ < K} w(T)`, as a real vector. -/
noncomputable def blockY (T : ℝ≥0) (K : ℝ) (w : ℝ≥0 → Fin d → ℤ) : Fin d → ℝ :=
  (Real.sqrt T)⁻¹ • fun c => ((truncEnd T K w c : ℤ) : ℝ)

theorem measurable_blockY (T : ℝ≥0) (K : ℝ) : Measurable (blockY (d := d) T K) := by
  have h1 : Measurable fun w : ℝ≥0 → Fin d → ℤ => fun c => ((truncEnd T K w c : ℤ) : ℝ) :=
    measurable_pi_iff.2 fun c => (measurable_of_countable (Int.cast : ℤ → ℝ)).comp
      ((measurable_pi_apply c).comp (measurable_truncEnd T K))
  exact h1.const_smul (Real.sqrt T)⁻¹

theorem norm_blockY_le {T : ℝ≥0} {K : ℝ} (hK : 0 ≤ K) (w : ℝ≥0 → Fin d → ℤ) :
    ‖blockY T K w‖ ≤ K / Real.sqrt T := by
  unfold blockY
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_intCast_pi,
    inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (norm_truncEnd_le hK w) (Real.sqrt_nonneg _)

/-- A sign change commutes with the block functional. -/
theorem blockY_signs (T : ℝ≥0) (K : ℝ) (ε : Fin d → ℤ) (hε : ∀ k, ε k = 1 ∨ ε k = -1)
    (w : ℝ≥0 → Fin d → ℤ) :
    blockY T K (gPath (latticeSign ε hε) w) = (fun k => ((ε k : ℤ) : ℝ)) * blockY T K w := by
  have h := truncEnd_gPath (latticeSign ε hε) (by funext k; simp [latticeSign_apply])
    (fun x => norm_sign_mul ε hε x) T K w
  unfold blockY
  rw [h, latticeSign_apply]
  funext k
  simp [mul_left_comm]

section PPP

variable {β : ℝ} [Fact (0 < β)] {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe}
  {N : Ωe → Measure (ℕ × RingSpace d β)}

/-- **Condition (ii) of the coupling step of Lemma 7.6, re-tuned**: the law of the block functional is invariant under every
sign change. -/
theorem blockY_signs_law
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (T : ℝ≥0) (K : ℝ) (ε : Fin d → ℝ) (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    ((ppLaw Pe N T).map (blockY T K)).map (fun x => ε * x) = (ppLaw Pe N T).map (blockY T K) := by
  set ε' : Fin d → ℤ := fun k => if ε k = 1 then 1 else -1 with hε'
  have hε'1 : ∀ k, ε' k = 1 ∨ ε' k = -1 := fun k => by
    by_cases h : ε k = 1 <;> simp [hε', h]
  have hεe : ε = fun k => ((ε' k : ℤ) : ℝ) := by
    funext k
    rcases hε k with h | h <;> simp [hε', h]
  have hm : Measurable fun x : Fin d → ℝ => ε * x := by fun_prop
  rw [Measure.map_map hm (measurable_blockY T K)]
  have e : (fun x : Fin d → ℝ => ε * x) ∘ blockY T K = blockY T K ∘ gPath (latticeSign ε' hε'1) := by
    funext w
    simp only [Function.comp_apply, blockY_signs, hεe]
  rw [e, ← Measure.map_map (measurable_blockY T K) (measurable_gPath _),
    ppLaw_gPath hN _ (by funext k; simp [latticeSign_apply])]

/-- **Condition (iii) of the coupling step of Lemma 7.6, re-tuned**: all coordinates of the block functional have the same
second moment. -/
theorem integral_blockY_sq_eq
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (T : ℝ≥0) (K : ℝ) (i k : Fin d) :
    ∫ w, (blockY T K w i) ^ 2 ∂ppLaw Pe N T = ∫ w, (blockY T K w k) ^ 2 ∂ppLaw Pe N T := by
  classical
  set σ : Equiv.Perm (Fin d) := Equiv.swap i k with hσ
  have hg0 : (LatticeAut.permute σ).toEquiv 0 = 0 := by
    funext j; simp [LatticeAut.permute]
  have hF : Measurable fun w : ℝ≥0 → Fin d → ℤ => (blockY T K w i) ^ 2 :=
    ((measurable_pi_apply i).comp (measurable_blockY T K)).pow_const 2
  have h1 : ∫ w, (blockY T K w i) ^ 2 ∂ppLaw Pe N T =
      ∫ w, (blockY T K (gPath (LatticeAut.permute σ) w) i) ^ 2 ∂ppLaw Pe N T := by
    conv_lhs => rw [← ppLaw_gPath hN (LatticeAut.permute σ) hg0 T]
    exact integral_map (measurable_gPath _).aemeasurable hF.aestronglyMeasurable
  rw [h1]
  congr 1
  funext w
  have h := truncEnd_gPath (LatticeAut.permute σ) hg0 (fun x => norm_perm_apply σ x) T K w
  unfold blockY
  rw [h]
  simp [LatticeAut.permute, hσ]

end PPP

end ElboimSly.Paper.Step
