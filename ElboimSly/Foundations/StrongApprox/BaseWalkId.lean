/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseAe
public import Mathlib

/-!
# The walk at integer times: `eq:sa-walk-int` and `eq:sa-int-diff`

ES22 (8.3): base coupling with precision n^10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

section Deterministic

variable {d : ℕ} {ν : Measure (Dir d × ℝ)}

/-- Coordinates of the canonical walk on the good event. -/
theorem walk_coord (hν : ν ∈ goodSet d) (t : ℝ) (i : Fin d) :
    walk d ν t i = (natOf (cnt ν (i, true) t) : ℤ) - (natOf (cnt ν (i, false) t) : ℤ) := by
  rw [walk_of_good hν]
  simp only [Finset.sum_apply, Pi.smul_apply, Dir.vec, smul_eq_mul, Pi.single_apply,
    Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro b _ hb; simp [hb.symm]
  · simp

/-- The count of the first `j` cells. -/
theorem natOf_cnt_nat (hν : ν ∈ goodSet d) (v : Dir d) (κ : ℕ → ℕ)
    (j : ℕ) (hcell : ∀ m : ℕ, m < j → ν (cellSet d (v, (m : ℤ) + 1)) = (κ m : ℝ≥0∞)) :
    natOf (cnt ν v j) = ∑ m ∈ Finset.range j, κ m := by
  induction j with
  | zero => simp [cnt_zero, natOf]
  | succ j ih =>
    have h := natOf_cnt_add hν v (s := (j : ℝ)) (t := ((j + 1 : ℕ) : ℝ)) (by positivity)
      (by push_cast; linarith)
    have hc : ν (({v} : Set (Dir d)) ×ˢ Ioc (j : ℝ) ((j + 1 : ℕ) : ℝ)) = (κ j : ℝ≥0∞) := by
      rw [← hcell j (Nat.lt_succ_self j)]
      unfold cellSet
      congr 2; simp
    rw [h, ih (fun m hm => hcell m (Nat.lt_succ_of_lt hm)), hc, Finset.sum_range_succ]
    simp [natOf]

end Deterministic

section Identity

variable {d N : ℕ} {μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))} [IsProbabilityMeasure μN]

/-- The partial sums `S^v_j = ∑_{l ≤ j} (ξ^v_l - 1 - z^v_l)`. -/
noncomputable def Sfun (a : SA d N) (v : Dir d) (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range j, if h : m < N then ((a v).1 ⟨m, h⟩ - 1 - (a v).2 ⟨m, h⟩) else 0

theorem blocks_jcell (ω : OmMain d N) (a : JIdx d N) :
    blocks d N ω (jcell d N a) = zk d N ω.1 a :=
  overrideAt_apply (jcell_injective d N) _ _ a

theorem Nproc_cell (ω : OmMain d N) (a : JIdx d N)
    (hY : ∀ i, ω.1.2 a i ∈ cellSet d (jcell d N a)) :
    Nproc d N ω (cellSet d (jcell d N a)) = (kapOf d N ω.1.1 a : ℝ≥0∞) := by
  have := cellProc_apply_cell (cellSet d) (measurableSet_cellSet d) (pairwise_disjoint_cellSet d)
    (fun k ω => Kc d N ω k) (fun k i ω => Yc d N ω k i) ω (jcell d N a) (fun i => by
      simp only [Yc, blocks_jcell, zk]; exact hY i)
  simpa [Nproc, Kc, blocks_jcell, zk] using this

/-- `eq:sa-walk-int` and `eq:sa-int-diff` (almost surely, on the main space). -/
theorem ae_walk_identity (hd : 1 ≤ d)
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    ∀ᵐ ω ∂PMain d N μN, Nproc d N ω ∈ goodSet d ∧ ∀ j : ℕ, j ≤ N → ∀ i : Fin d,
      ((walk d (Nproc d N ω) j i : ℤ) : ℝ) - √2 * ∑ m ∈ Finset.range j, Xfam d N ω m i =
        Sfun ω.1.1 (i, true) j - Sfun ω.1.1 (i, false) j := by
  have hxi : ∀ᵐ ω ∂PMain d N μN, ∀ p, xiOf d N ω.1.1 p = (kapOf d N ω.1.1 p : ℝ) := by
    have hmp : MeasurePreserving (fun ω : OmMain d N => ω.1.1) (PMain d N μN) (PA d N μN) :=
      measurePreserving_fst.comp measurePreserving_fst
    exact hmp.quasiMeasurePreserving.ae (ae_xi_eq_kap hμ1)
  filter_upwards [ae_good (base_ppp_main hd hμ1), ae_Y_mem, hxi] with ω hg hY hxiω
  refine ⟨hg, fun j hj i => ?_⟩
  have hcnt : ∀ b : Bool, natOf (cnt (Nproc d N ω) (i, b) j) =
      ∑ m ∈ Finset.range j, if h : m < N then kapOf d N ω.1.1 ((i, b), ⟨m, h⟩) else 0 := by
    intro b
    refine natOf_cnt_nat hg (i, b) _ j fun m hm => ?_
    have hmN : m < N := lt_of_lt_of_le hm hj
    simp only [hmN, dite_true]
    exact Nproc_cell ω ((i, b), ⟨m, hmN⟩) (hY _)
  rw [walk_coord hg, hcnt true, hcnt false]
  unfold Sfun
  push_cast
  rw [Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m < N := lt_of_lt_of_le (Finset.mem_range.1 hm) hj
  simp only [hmN, dite_true]
  have hX : Xfam d N ω m = zdiff d N ω.1.1 ⟨m, hmN⟩ :=
    overrideAt_apply (j := fun m : Fin N => (m : ℕ)) Fin.val_injective _ _ ⟨m, hmN⟩
  rw [hX]
  have h1 := hxiω ((i, true), ⟨m, hmN⟩)
  have h2 := hxiω ((i, false), ⟨m, hmN⟩)
  simp only [xiOf] at h1 h2
  rw [← h1, ← h2]
  simp only [zdiff, zOf]
  have : (√2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Identity

end StrongApprox
end ElboimSly
