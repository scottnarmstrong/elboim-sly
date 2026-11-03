/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Refl1
public import ElboimSly.Foundations.Cyclic.CycRegenRecordTrunc
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: the explored region of `ρ^{reg}_t` is equivariant

ES22 Proposition 5.2 Step 2, "covariance of trajectories(a) applied to each piece": for `ν` good,
the region of `Trunc_t(ρ^{reg}(h_*ν))` is the image under `h` (acting on the edge coordinate) of
the region of `Trunc_t(ρ^{reg}(ν))`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Interchange
  ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The action of `h` on `ℕ × S_β` (on the edge coordinate). -/
def psiE (k : ℕ) (β : ℝ) [Fact (0 < β)] : (ℕ × RingSpace (k + 2) β) ≃ᵐ (ℕ × RingSpace (k + 2) β) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℕ)
    (ringMapEquiv (edgeEquiv (reflAut k)) (MeasurableEquiv.refl (AddCircle β)))

theorem psiE_apply (x : ℕ × RingSpace (k + 2) β) :
    psiE k β x = (x.1, ringMapEquiv (edgeEquiv (reflAut k)) (MeasurableEquiv.refl _) x.2) := rfl

theorem psiE_invol (x : ℕ × RingSpace (k + 2) β) : psiE k β (psiE k β x) = x := by
  obtain ⟨a, e, θ⟩ := x
  simp [psiE_apply, ringMapEquiv_apply, edgeEquiv_refl_invol]

/-- `R = (e, θ) ↦ (h e, θ)` on the ring space. -/
abbrev rR (k : ℕ) (β : ℝ) [Fact (0 < β)] : RingSpace (k + 2) β ≃ᵐ RingSpace (k + 2) β :=
  ringMapEquiv (edgeEquiv (reflAut k)) (MeasurableEquiv.refl (AddCircle β))

theorem rR_apply (p : RingSpace (k + 2) β) : rR k β p = (edgeEquiv (reflAut k) p.1, p.2) := rfl

/-- `cycRegion` of a reflected path is the preimage of the region under `R`. -/
theorem cycRegion_refl (f : ℝ → Fin (k + 2) → ℤ) (a b : ℝ) :
    cycRegion β (fun s => (reflAut k).toEquiv (f s)) a b = rR k β ⁻¹' cycRegion β f a b := by
  ext ⟨e, θ⟩
  simp only [mem_preimage, rR_apply]
  constructor
  · rintro ⟨t, h1, h2, h3, z, hz, hm⟩
    refine ⟨t, h1, h2, h3, (reflAut k).toEquiv z, ?_, ?_⟩
    · filter_upwards [hz] with u hu hau
      rw [← hu hau, reflAut_invol]
    · exact (edgeEquiv_mem (reflAut k) e z).2 hm
  · rintro ⟨t, h1, h2, h3, z, hz, hm⟩
    refine ⟨t, h1, h2, h3, (reflAut k).toEquiv z, ?_, ?_⟩
    · filter_upwards [hz] with u hu hau
      rw [hu hau]
    · have := (edgeEquiv_mem (reflAut k) e ((reflAut k).toEquiv z)).1
      rw [reflAut_invol] at this
      exact this hm

end ElboimSly.Paper.Escape
