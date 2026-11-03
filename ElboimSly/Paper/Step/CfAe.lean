/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.CfJump
public import ElboimSly.Paper.Step.DrivenLaw
public import Mathlib

/-!
# `θ_a Y` is coincidence-free almost surely, for every SRW `Y`

The driven regenerated walk (e), for an arbitrary SRW (not only the canonical one).

`ae_stepShift_mem_stepCF_of_isSRW`: if `Y` is an SRW with all paths driving paths, then
`θ_a Y ∈ CF_β` almost surely. The non-measurable set `CF_β` is replaced by the measurable set
`stepBadCF` of `CPath`s (`Step/CfJump`), which describes it on driving paths.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- A regular path as a `CPath` of infinite length. -/
def regCPath (x : ℝ≥0 → Fin d → ℤ) (hx : IsRegPath x) : CPath (Fin d → ℤ) where
  len := ⊤
  fn := x
  rc := hx.rc
  fin := hx.fin
  const _ _ h _ := absurd h (by simp)

theorem mem_cycCF_iff_not_badCF {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ} (hx : IsDrivingPath x) :
    x ∈ CycCF (d := d) (β := b) ↔ regCPath x hx.toIsRegPath ∉ stepBadCF b := by
  have hD := mem_CDisc_iff_jt (regCPath x hx.toIsRegPath)
  constructor
  · rintro ⟨-, h1, h2⟩ hbad
    rcases hbad with hbad | hbad
    · simp only [mem_iUnion, mem_ofPred_eq] at hbad
      obtain ⟨i, j, k, hk, hlt, heq⟩ := hbad
      have hne : (regCPath x hx.toIsRegPath).jt (i + 1) ≠ ⊤ := hlt.ne
      set s := ((regCPath x hx.toIsRegPath).jt (i + 1)).toNNReal with hs
      have hse : (regCPath x hx.toIsRegPath).jt (i + 1) = (s : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal hne).symm
      have hsd : s ∈ CDisc x := (hD s).2 ⟨i, hse⟩
      have hsd' : s + (k : ℝ≥0) * b ∈ CDisc x := (hD _).2 ⟨j, by
        rw [heq, hse]; push_cast; rfl⟩
      exact h1 s hsd _ hsd' k hk rfl
    · simp only [mem_iUnion, mem_ofPred_eq] at hbad
      obtain ⟨i, k, hk, heq⟩ := hbad
      exact h2 k hk ((hD _).2 ⟨i, heq⟩)
  · intro hnb
    refine ⟨hx, fun s hs s' hs' k hk heq => hnb ?_, fun k hk hmem => hnb ?_⟩
    · obtain ⟨i, hi⟩ := (hD s).1 hs
      obtain ⟨j, hj⟩ := (hD s').1 hs'
      left
      simp only [mem_iUnion, mem_ofPred_eq]
      refine ⟨i, j, k, hk, by rw [hi]; exact ENNReal.coe_lt_top, ?_⟩
      rw [hj, hi, heq]; push_cast; rfl
    · obtain ⟨i, hi⟩ := (hD _).1 hmem
      right
      simp only [mem_iUnion, mem_ofPred_eq]
      exact ⟨i, k, hk, hi⟩

/-- The regular-path subtype. -/
abbrev RegPaths (d : ℕ) : Type := {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}

/-- The bad set, as a subset of regular paths shifted by `a`. -/
def badShift (d : ℕ) (a b : ℝ≥0) : Set (RegPaths d) :=
  {x | regCPath (shiftPath x.1 a) (isRegPath_shiftPath x.2 a) ∈ stepBadCF b}

theorem measurableSet_badShift (a b : ℝ≥0) : MeasurableSet (badShift d a b) := by
  have hm : Measurable fun x : RegPaths d =>
      regCPath (shiftPath x.1 a) (isRegPath_shiftPath x.2 a) := by
    rw [CPath.measurable_iff]
    refine ⟨measurable_const, fun s => ?_⟩
    show Measurable fun x : RegPaths d => shiftPath x.1 a s
    have h1 : Measurable fun x : RegPaths d => x.1 (a + s) :=
      (measurable_pi_apply (a + s)).comp measurable_subtype_coe
    have h2 : Measurable fun x : RegPaths d => x.1 a :=
      (measurable_pi_apply a).comp measurable_subtype_coe
    exact h1.sub h2
  exact hm (measurableSet_stepBadCF b)

/-- **the driven regenerated walk (e) for an arbitrary SRW**: `θ_a Y ∈ CF_β` almost surely. -/
theorem ae_stepShift_mem_stepCF_of_isSRW {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → PathSpace d} (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    (a : ℝ≥0) : ∀ᵐ ω ∂P, stepShift a (Y ω) ∈ StepCF (d := d) β := by
  obtain ⟨hYm, -, Ω', _, P', N', hN', hlaw⟩ := hY
  have hb : 0 < β.toNNReal := toNNReal_pos'
  set G : Ω → RegPaths d := fun ω => ⟨Y ω, (hYp ω).toIsRegPath⟩ with hG
  set G' : Ω' → RegPaths d := fun ω => ⟨canonical d N' ω, walkPath_isRegPath (N' ω)⟩ with hG'
  have hGm : Measurable G := hYm.subtype_mk
  have hG'm : Measurable G' := (measurable_canonical hN'.measurable).subtype_mk
  have hBm := measurableSet_badShift (d := d) a β.toNNReal
  obtain ⟨Γ, hΓ, hΓeq⟩ := (MeasurableSpace.measurableSet_comap).1 hBm
  have e1 : P (G ⁻¹' badShift d a β.toNNReal) = P' (G' ⁻¹' badShift d a β.toNNReal) := by
    rw [← hΓeq]
    have h1 : G ⁻¹' (Subtype.val ⁻¹' Γ) = Y ⁻¹' Γ := rfl
    have h2 : G' ⁻¹' (Subtype.val ⁻¹' Γ) = canonical d N' ⁻¹' Γ := rfl
    rw [h1, h2, ← Measure.map_apply hYm hΓ,
      ← Measure.map_apply (measurable_canonical hN'.measurable) hΓ, hlaw]
  have h0 : P' (G' ⁻¹' badShift d a β.toNNReal) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [ae_shiftPath_mem_cycCF hN' β.toNNReal hb a] with ω hω hbad
    exact ((mem_cycCF_iff_not_badCF hω.1).1 hω) hbad
  have h1 : P (G ⁻¹' badShift d a β.toNNReal) = 0 := e1.trans h0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with ω hω
  exact (mem_cycCF_iff_not_badCF (b := β.toNNReal) (stepShift_mem (hYp ω) a)).2 hω

end ElboimSly.Paper.Step
