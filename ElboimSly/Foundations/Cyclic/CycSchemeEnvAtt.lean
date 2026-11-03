/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvUpd
public import Mathlib

/-!
# The environment scheme (b), finite horizon: the stopping length is attained

The environment scheme (b), the case of a finite global horizon `s_∘`. The set of stopping
candidates of a walk meets every bounded interval in finitely many points (a candidate in `[0, T]`
sits at, or at a bounded deadline after, one of the finitely many jumps in `[0, T]`), so a finite
infimum is attained (`sInf_mem_candAbs`, `sInf_cand_mem`). Hence after a step that does not stop,
the new time is strictly below a finite stopping length (`lt_sInf_of_not_stops`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {sc : ℝ≥0∞} {ν : Measure (I × RingSpace d β)}

/-- The candidates of a path in a bounded interval form a finite set. -/
theorem candAbs_inter_Iic_finite (p : CPath (Fin d → ℤ)) (St : ℕ → Prop) (D : ℕ → ℝ≥0∞) (T : ℝ≥0) :
    (candAbs p St D ∩ Iic (T : ℝ≥0∞)).Finite := by
  have h1 : ((Finset.range (p.cnt T + 1) : Finset ℕ) : Set ℕ).Finite := Finset.finite_toSet _
  refine ((h1.image (fun a => p.jt a)).union (h1.image (fun a => p.jt a + D a))).subset ?_
  rintro c ⟨hc, hcT⟩
  rcases hc with ⟨a, ha1, hat, hSt, rfl⟩ | ⟨a, hat, rfl, hlt⟩
  · left
    refine ⟨a, ?_, rfl⟩
    simp only [Finset.coe_range, mem_Iio]
    have := (p.jt_le_iff a T).1 hcT
    omega
  · right
    refine ⟨a, ?_, rfl⟩
    simp only [Finset.coe_range, mem_Iio]
    have := (p.jt_le_iff a T).1 (le_self_add.trans hcT)
    omega

/-- A finite infimum of the candidates is attained. -/
theorem sInf_mem_candAbs (p : CPath (Fin d → ℤ)) (St : ℕ → Prop) (D : ℕ → ℝ≥0∞)
    (h : sInf (candAbs p St D) < ⊤) : sInf (candAbs p St D) ∈ candAbs p St D := by
  obtain ⟨c, hc, hclt⟩ := sInf_lt_iff.1 h
  have hcT : c ≠ ⊤ := hclt.ne
  have hfin := candAbs_inter_Iic_finite p St D c.toNNReal
  rw [ENNReal.coe_toNNReal hcT] at hfin
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image _ id hfin ⟨c, hc, mem_Iic.2 le_rfl⟩
  have hmeq : sInf (candAbs p St D) = m := by
    refine le_antisymm (sInf_le hm.1) (le_sInf fun x hx => ?_)
    by_cases hxc : x ≤ c
    · exact hmin x ⟨hx, mem_Iic.2 hxc⟩
    · exact (hmin c ⟨hc, mem_Iic.2 le_rfl⟩).trans (not_le.1 hxc).le
  rw [hmeq]
  exact hm.1

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem sInf_cand_mem (P : CycPlan I d β) (ν : Measure (I × RingSpace d β)) (k : ℕ)
    (h : sInf (cand P ν k) < ⊤) : sInf (cand P ν k) ∈ cand P ν k := by
  rw [cand_eq] at h ⊢
  exact sInf_mem_candAbs _ _ _ h

variable {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}

/-- After a step that does not stop, the new time is strictly below a finite stopping length. -/
theorem lt_sInf_of_not_stops (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hns : ¬ CycScheme.stops P sc (ρ, false) o) (hfin : sInf (cand P ν k) < ⊤) :
    ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) < sInf (cand P ν k) :=
  cand_lt_of_not_stops hν h hg hns _ (sInf_cand_mem P ν k hfin)

end CycSchemeEnv
end ElboimSly.Cyclic

end
