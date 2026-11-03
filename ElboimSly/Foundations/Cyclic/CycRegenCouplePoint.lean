/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenCoupleSlices
public import Mathlib

/-!
# ES22 Lemma 2.1 (c)--(e): the deterministic wiring at a time `t`

ES22 Lemma 2.1 (c)--(e), proof ("Case `L = 0`", "Case `L > 0`"). Let `ν`
be a good environment on `ℕ × S_β`, `ν'` another one, `t ≥ 0`, `R_t` the region of the truncated
record `cycRec^{𝒫_reg}(t)`, `Ñ = ν|_{S∖R_t} + ν'|_{R_t}` a good environment, and
`M = Sh_Z Ñ` for `Z = (k_t, W(t), L_t)`. Then `slices M = seqCons ((φ_{(x,L)})_* Ñ^{k_t}) (ν^·) k_t`
and the deterministic parts (c), (e) of the written proof hold for `W' = regenWalk (slices M)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open CycSchemeEnv

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The shift parameter `Z = (k_t, W(t), L_t)` of a good environment at time `t`. -/
noncomputable def regZ0 (ν : Measure (ℕ × RingSpace d β)) (t : ℝ≥0) : ShiftPar d :=
  (ElboimSly.regenCount (slices ν) (t : ℝ), ElboimSly.regenWalk (slices ν) (t : ℝ),
    (regLast ν t : ℝ))

/-- The region `R_t` of the truncated record `cycRec^{𝒫_reg}(t)`. -/
def regRegion (ν : Measure (ℕ × RingSpace d β)) (t : ℝ≥0) : Set (ℕ × RingSpace d β) :=
  (CycRec.trunc t ((regPlan d β).envFinal ν)).region β

theorem measurableSet_regRegion (ν : Measure (ℕ × RingSpace d β)) (t : ℝ≥0) :
    MeasurableSet (regRegion ν t) := measurableSet_region_trunc _

variable {ν ν' : Measure (ℕ × RingSpace d β)}

theorem cycSlice_tilde_gt (hν : CycGood ν) (t : ℝ≥0) {j : ℕ}
    (hj : ElboimSly.regenCount (slices ν) (t : ℝ) < j) :
    cycSlice j (tildeEnv ν ν' (regRegion ν t)) = cycSlice j ν :=
  cycSlice_tildeEnv_of_empty j ν ν' (measurableSet_regRegion ν t)
    (preimage_region_trunc_gt hν t hj)

/-- The current piece's region `ℛ_{(0,L]}(w)`. -/
noncomputable def regCurRegion (ν : Measure (ℕ × RingSpace d β)) (t : ℝ≥0) : Set (RingSpace d β) :=
  cycRegion β (fun s => ElboimSly.cycWalk
    (cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ)) ν) 0 0 s) 0 (regLast ν t : ℝ)

theorem measurableSet_regCurRegion (hν : CycGood ν) (t : ℝ≥0) :
    MeasurableSet (regCurRegion ν t) := by
  have := (measurableSet_regRegion ν t).preimage
    (measurable_prodMk_left (x := ElboimSly.regenCount (slices ν) (t : ℝ)))
  rwa [show Prod.mk (ElboimSly.regenCount (slices ν) (t : ℝ)) ⁻¹' regRegion ν t =
    regCurRegion ν t from preimage_region_trunc_last hν t] at this

theorem cycSlice_tilde_last_compl (hν : CycGood ν) (t : ℝ≥0) :
    (cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ)) (tildeEnv ν ν' (regRegion ν t))).restrict
        (regCurRegion ν t)ᶜ =
      (cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ)) ν).restrict (regCurRegion ν t)ᶜ :=
  cycSlice_tildeEnv_compl _ ν ν' (measurableSet_regRegion ν t) (measurableSet_regCurRegion hν t)
    (preimage_region_trunc_last hν t)

theorem slices_regShift (hν : CycGood ν) (t : ℝ≥0)
    (hlf : tildeEnv ν ν' (regRegion ν t) ∈ lfSet (cycIntensity ℕ d β)) :
    slices (cycShift (regZ0 ν t) (tildeEnv ν ν' (regRegion ν t))) =
      seqCons ((cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ))
        (tildeEnv ν ν' (regRegion ν t))).map
          (hitPhi (ElboimSly.regenWalk (slices ν) (t : ℝ)) (regLast ν t : ℝ)))
        (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ)) :=
  slices_cycShift (regZ0 ν t) _ hlf (slices ν) fun _j hj => cycSlice_tilde_gt hν t hj

variable (hν : CycGood ν) (t : ℝ≥0)
  (hÑ : CycGood (tildeEnv ν ν' (regRegion ν t)))
  (hlf : tildeEnv ν ν' (regRegion ν t) ∈ lfSet (cycIntensity ℕ d β))

include hν hÑ in
/-- The slices of `M = Sh_Z Ñ` are good. -/
theorem good_slices_regShift (hlf : tildeEnv ν ν' (regRegion ν t) ∈ lfSet (cycIntensity ℕ d β)) :
    ∀ j, Good (slices (cycShift (regZ0 ν t) (tildeEnv ν ν' (regRegion ν t))) j) := by
  rw [slices_regShift hν t hlf]
  exact good_seqCons hν (good_map_hitPhi (hÑ _) _ _) _

include hν hÑ in
/-- **ES22 Lemma 2.1 (c)**, pathwise: `W(t + s) - W(t) = W'(s)` for `t + s ≤ t_hit(t)`,
where `W' = regenWalk (slices M)`. -/
theorem regen_agree_M (hlf : tildeEnv ν ν' (regRegion ν t) ∈ lfSet (cycIntensity ℕ d β))
    {s : ℝ≥0} (hs : ENNReal.ofReal ((t : ℝ) + s) ≤ ElboimSly.cycThit (slices ν) (t : ℝ)) :
    ElboimSly.regenWalk (slices (cycShift (regZ0 ν t) (tildeEnv ν ν' (regRegion ν t)))) (s : ℝ) =
      ElboimSly.regenWalk (slices ν) ((t : ℝ) + s) - ElboimSly.regenWalk (slices ν) (t : ℝ) := by
  rw [slices_regShift hν t hlf]
  set k := ElboimSly.regenCount (slices ν) (t : ℝ) with hk
  have hLd : (regLast ν t : ℝ) = (t : ℝ) - ElboimSly.regenStart (slices ν) (t : ℝ) :=
    regLast_coe t
  have hgk : ∀ j, Good (slices ν j) := hν
  rcases (show (0 : ℝ≥0) ≤ regLast ν t from zero_le).lt_or_eq with hL | hL
  · exact (regen_agree_pos hgk hLd hL (hÑ k) (by
      have := cycSlice_tilde_last_compl (ν' := ν') hν t
      exact this) hs).2
  · -- `L = 0`
    have hL0 : (regLast ν t : ℝ) = 0 := by rw [← hL]; simp
    have hα : (t : ℝ) = ElboimSly.regenStart (slices ν) (t : ℝ) := by linarith
    have hC : regCurRegion ν t = ∅ := by
      unfold regCurRegion
      rw [hL0]
      ext p
      simp only [cycRegion, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨u, h1, h2, -⟩
      linarith
    have hslice : cycSlice k (tildeEnv ν ν' (regRegion ν t)) = cycSlice k ν := by
      have h := cycSlice_tilde_last_compl (ν' := ν') hν t
      rw [hC, compl_empty, Measure.restrict_univ, Measure.restrict_univ] at h
      exact h
    have hz : ElboimSly.regenWalk (slices ν) (t : ℝ) = 0 := by
      unfold ElboimSly.regenWalk
      rw [← hk, ← hα, sub_self]
      exact cycWalk_zero (hgk k) 0 0
    rw [hslice]
    have hgk' : Good (cycSlice k ν) := hgk k
    have hpath : ∀ u : ℝ≥0, ElboimSly.cycWalk ((cycSlice k ν).map
        (hitPhi (ElboimSly.regenWalk (slices ν) (t : ℝ)) (regLast ν t : ℝ))) 0 0 (u : ℝ) =
        ElboimSly.cycWalk (slices ν k) 0 0 (u : ℝ) := by
      intro u
      have h1 := cycWalk_map_hitPhi hgk'
        (ElboimSly.regenWalk (slices ν) (t : ℝ)) (regLast ν t : ℝ) (s := (u : ℝ)) u.2
      refine h1.trans ?_
      rw [hz, hL0]
      show ElboimSly.cycWalk (cycSlice k ν) 0 0 (u : ℝ) - 0 = _
      simp
    exact regen_agree_zero hgk hα (good_map_hitPhi hgk' _ _) hpath s

include hν hÑ in
/-- **ES22 Lemma 2.1 (c)**, second claim: if `α(t) < t`, the first piece of `W'` does
not close before `t_hit(t) - t`. -/
theorem regen_first_open_M (hlf : tildeEnv ν ν' (regRegion ν t) ∈ lfSet (cycIntensity ℕ d β))
    (hL : 0 < regLast ν t) {s : ℝ≥0}
    (hs : ENNReal.ofReal ((t : ℝ) + s) ≤ ElboimSly.cycThit (slices ν) (t : ℝ)) :
    (s : ℝ≥0∞) < ElboimSly.cycTreg (slices (cycShift (regZ0 ν t)
      (tildeEnv ν ν' (regRegion ν t))) 0) := by
  rw [slices_regShift hν t hlf]
  have hgk : ∀ j, Good (slices ν j) := hν
  have h := (regen_agree_pos hgk (regLast_coe t) hL (hÑ _)
    (cycSlice_tilde_last_compl (ν' := ν') hν t) hs).1
  have hμ := good_map_hitPhi (hÑ (ElboimSly.regenCount (slices ν) (t : ℝ)))
    (ElboimSly.regenWalk (slices ν) (t : ℝ)) (regLast ν t : ℝ)
  have hw : walkMap ((cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ))
        (tildeEnv ν ν' (regRegion ν t))).map
      (hitPhi (ElboimSly.regenWalk (slices ν) (t : ℝ)) (regLast ν t : ℝ))) =
      fun u : ℝ≥0 => ElboimSly.cycWalk ((cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ))
        (tildeEnv ν ν' (regRegion ν t))).map
      (hitPhi (ElboimSly.regenWalk (slices ν) (t : ℝ)) (regLast ν t : ℝ))) 0 0 (u : ℝ) :=
    funext fun u => walkMap_eq_cycWalk hμ u
  rw [hw, pathTreg_cycWalk] at h
  exact h

include hν hÑ in
/-- **ES22 Lemma 2.1 (e)**, pathwise: `t_hit(t)` through `W' = regenWalk (slices M)`. -/
theorem regen_thit_eq_M (hlf : tildeEnv ν ν' (regRegion ν t) ∈ lfSet (cycIntensity ℕ d β)) :
    ElboimSly.cycThit (slices ν) (t : ℝ) =
      ⨅ s ∈ {s : ℝ | (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
        ElboimSly.regenStart (slices ν) (t : ℝ) < s' ∧ s' < t ∧
        ‖ElboimSly.regenWalk (slices ν) (t : ℝ) +
          ElboimSly.regenWalk (slices (cycShift (regZ0 ν t) (tildeEnv ν ν' (regRegion ν t))))
            (s - t) - ElboimSly.regenWalk (slices ν) s'‖ ≤ 1},
        ENNReal.ofReal s := by
  rw [slices_regShift hν t hlf]
  exact regen_thit_eq (fun j => hν j) (regLast_coe t) (hÑ _)
    (cycSlice_tilde_last_compl (ν' := ν') hν t)

end ElboimSly.Cyclic

end
