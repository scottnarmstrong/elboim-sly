/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Setting
public import Mathlib

/-!
# The stopping times depend on `ω` only through the data at `ω`

If two `Step78Data` have the same parameters and agree at `ω` (same second walk and same `V`), then
`ζ_i(ω)` and `ζ'_i(ω)` agree. Used to compare the data of the original space with its pullback to
the extension of the probability space.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*}

/-- `D` and `D'` have the same parameters and agree at the sample point `ω`. -/
structure Step78Data.AgreeAt (D D' : Step78Data d Ω) (ω : Ω) : Prop where
  β : D'.β = D.β
  T : D'.T = D.T
  n : D'.n = D.n
  ρ : D'.ρ = D.ρ
  u : D'.u = D.u
  w : ∀ t, D'.w t ω = D.w t ω
  V : D'.V ω = D.V ω

namespace Step78Data

variable {D D' : Step78Data d Ω} {ω : Ω}

theorem path_congr (h : AgreeAt D D' ω) : D'.path ω = D.path ω := by
  unfold Step78Data.path
  have : (fun s => D'.w s ω) = fun s => D.w s ω := funext h.w
  rw [this]

theorem relaxed_congr (h : AgreeAt D D' ω) : D'.relaxed ω = D.relaxed ω := by
  unfold Step78Data.relaxed stepRelaxedSetOf
  have : (fun s => D'.w s ω) = fun s => D.w s ω := funext h.w
  rw [h.β, this]

theorem farSet_congr (h : AgreeAt D D' ω) : D'.farSet ω = D.farSet ω := by
  unfold Step78Data.farSet
  rw [relaxed_congr h, path_congr h, h.V, h.ρ]

theorem nearSet1_congr (h : AgreeAt D D' ω) : D'.nearSet1 ω = D.nearSet1 ω := by
  unfold Step78Data.nearSet1
  rw [path_congr h, h.V]

theorem nearSet2_congr (h : AgreeAt D D' ω) : D'.nearSet2 ω = D.nearSet2 ω := by
  unfold Step78Data.nearSet2
  rw [path_congr h, h.V, h.n]

theorem gap_congr (h : AgreeAt D D' ω) : D'.gap = D.gap := by
  unfold Step78Data.gap
  rw [h.n]

theorem treg_congr (h : AgreeAt D D' ω) : D'.treg ω = D.treg ω := by
  simp only [Step78Data.treg, h.β, h.u, h.w]

theorem thit_congr (h : AgreeAt D D' ω) {R R' : Ω → WithTop ℝ≥0} (hR : R' ω = R ω) :
    D'.thit R' ω = D.thit R ω := by
  simp only [Step78Data.thit, stepThitStop, ElboimSly.SRW.stopReal, h.β, h.w, hR]
  try rfl

theorem firstGe_congr {U U' : Ω → Set ℝ} {R R' : Ω → WithTop ℝ≥0} (hU : U' ω = U ω)
    (hR : R' ω = R ω) : step78FirstGe U' R' ω = step78FirstGe U R ω := by
  unfold step78FirstGe
  rw [hU, hR]

theorem nextZeta_congr (h : AgreeAt D D' ω) {R R' : Ω → WithTop ℝ≥0} (hR : R' ω = R ω) :
    D'.nextZeta R' ω = D.nextZeta R ω := by
  unfold Step78Data.nextZeta
  rw [h.T, firstGe_congr (farSet_congr h) hR]

theorem zetaPP_congr (h : AgreeAt D D' ω) {Z Z' : Ω → WithTop ℝ≥0} (hZ : Z' ω = Z ω) :
    D'.zetaPP Z' ω = D.zetaPP Z ω := by
  unfold Step78Data.zetaPP
  rw [thit_congr h hZ, treg_congr h, firstGe_congr (nearSet1_congr h) hZ,
    firstGe_congr (U := D.nearSet2) (R := fun ω => Z ω + (D.gap : WithTop ℝ≥0))
      (nearSet2_congr h) (by simp only [hZ, gap_congr h])]

theorem zetaP'_congr (h : AgreeAt D D' ω) {Z Z' : Ω → WithTop ℝ≥0} (hZ : Z' ω = Z ω) :
    D'.zetaP' Z' ω = D.zetaP' Z ω := by
  unfold Step78Data.zetaP'
  rw [hZ, zetaPP_congr h hZ, h.T]

/-- `ζ'_i(ω)` and `ζ_i(ω)` depend only on the data at `ω`. -/
theorem zp_zeta_congr (h : AgreeAt D D' ω) (i : ℕ) :
    D'.zp i ω = D.zp i ω ∧ D'.zeta i ω = D.zeta i ω := by
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
    have hz : D'.zeta (i + 1) ω = D.zeta (i + 1) ω := nextZeta_congr h ih.1
    exact ⟨zetaP'_congr h hz, hz⟩

/-- The pullback of the data along a map of sample spaces. -/
def comap (D : Step78Data d Ω) {Ω' : Type*} (f : Ω' → Ω) : Step78Data d Ω' where
  β := D.β
  T := D.T
  n := D.n
  ρ := D.ρ
  u := D.u
  w t ω' := D.w t (f ω')
  V ω' := D.V (f ω')

/-- `ζ'_i` and `ζ_i` commute with pullback. -/
theorem comap_zp_zeta (D : Step78Data d Ω) {Ω' : Type*} (f : Ω' → Ω) (i : ℕ) :
    (D.comap f).zp i = (fun ω' => D.zp i (f ω')) ∧
      (D.comap f).zeta i = (fun ω' => D.zeta i (f ω')) := by
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
    have hz : (D.comap f).zeta (i + 1) = fun ω' => D.zeta (i + 1) (f ω') := by
      show (D.comap f).nextZeta ((D.comap f).zp i) = _
      rw [ih.1]
      rfl
    refine ⟨?_, hz⟩
    show (D.comap f).zetaP' ((D.comap f).zeta (i + 1)) = _
    rw [hz]
    rfl

end Step78Data

end ElboimSly.Paper.Step

end
