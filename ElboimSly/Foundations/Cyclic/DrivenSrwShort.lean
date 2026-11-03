/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.DrivenCf
public import ElboimSly.Foundations.Cyclic.DrivenWd
public import ElboimSly.Foundations.Cyclic.DrivenDef
import Mathlib

/-!
# The driven walk is the driving walk up to time `β`

The cyclic walk is an SRW up to time β (a), first claim: a.s. `treg^X ≥ β` and `W^X(s) = X(s)` for
`s ∈ [0, β]`. The second claim (construction (iii) of the regenerated walk) is not here.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ} {x : ℝ≥0 → Fin d → ℤ} {β : ℝ≥0}

theorem le_nat_mul {k : ℕ} (hk : 1 ≤ k) : β ≤ k * β :=
  le_mul_of_one_le_left zero_le (by exact_mod_cast hk)

/-- Pathwise form of the cyclic walk is an SRW up to time β (a) for `W^X`: for a coincidence-free driving path,
`treg^x ≥ β` and `w^x = x` on `[0, β]`. -/
theorem drivenWalk_eq_self_of_cycCF (hx : x ∈ CycCF β) (hβ : 0 < β) :
    (β : ℝ≥0∞) ≤ drivenTreg β x ∧ ∀ s ≤ β, drivenWalk β x s = x s := by
  obtain ⟨hdr, -, hno⟩ := hx
  refine ⟨?_, ?_⟩
  · refine le_iInf fun k => ?_
    have hk := k.2.1
    exact_mod_cast le_nat_mul hk
  · have hβx : β ∉ CDisc x := by simpa using hno 1 le_rfl
    have hD : ∀ t, 0 < t → t ≤ β →
        DrivenD1 β x t ∧ DrivenD2 β x x t ∧ DrivenD3 β x x t := by
      intro t ht htβ
      have hnf : ∀ k, ¬ ForcedAt β x t k := by
        rintro k ⟨⟨hk1, hkt⟩, hJ, -⟩
        have : t - k * β = 0 := by
          apply tsub_eq_zero_of_le
          calc t ≤ β := htβ
            _ ≤ k * β := le_nat_mul hk1
        exact absurd (this ▸ hJ).1 (lt_irrefl _)
      refine ⟨fun k hk => absurd hk (hnf k), fun _ hxt => ?_, fun _ hxt => ?_⟩
      · have htlt : t < β := lt_of_le_of_ne htβ (fun h => hβx (h ▸ hxt))
        have hT : TakenAt β x x t := by
          rintro k ⟨hk1, hkt⟩
          exfalso
          have : β ≤ k * β := le_nat_mul hk1
          exact absurd (lt_of_lt_of_le htlt (this.trans hkt)) (lt_irrefl _)
        rw [ite_eq_left hT]; abel
      · exact (hdr.toIsRegPath.leftVal_eq_of_not_mem ht hxt).symm
    intro s hs
    exact (drivenWalk_unique hdr.toIsRegPath hβ (T := β) (p := x)
      (fun s _ => hdr.toIsRegPath.rc s) hdr.zero hD s hs).symm

/-- The cyclic walk is an SRW up to time β (a) for `W^X`: for the canonical SRW built from a Poisson point process,
almost surely `treg^X ≥ β` and `W^X(s) = X(s)` for all `s ∈ [0, β]`. -/
theorem ae_canonical_drivenWalk_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (β : ℝ≥0) (hβ : 0 < β) :
    ∀ᵐ ω ∂P, (β : ℝ≥0∞) ≤ drivenTreg β (canonical d N ω) ∧
      ∀ s ≤ β, drivenWalk β (canonical d N ω) s = canonical d N ω s := by
  filter_upwards [ae_canonical_mem_cycCF hN β hβ] with ω hω
  exact drivenWalk_eq_self_of_cycCF hω hβ

end ElboimSly.Cyclic

end
