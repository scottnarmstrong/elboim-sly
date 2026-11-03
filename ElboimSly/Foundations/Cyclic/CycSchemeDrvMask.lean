/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvUse
public import Mathlib

/-!
# The driving scheme (a): the masked probe of step `j` is the raw probe

The driving scheme (a), masking. By induction on `k`, the driving explored region
`𝒵'_k(η')` contains in copy `j'` only points with driving time at most `drvUse` of the current
environment record at the index `j'` (`drvScheme_Z_bound`). The raw probe lives in driving times
`(drvT, drvT + h]`, where `drvT = drvUse (idx)`, so it is `∞` on `𝒵'_k(η')`: `drvScheme_Rt`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
  {J : Type*} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) (P : CycPlan I d β) (sc : ℝ≥0∞)
  (U : Type*) [MeasurableSpace U] (hj : ∀ k, Measurable (jx k))

theorem drvPsi_succ_init (k : ℕ) (η : Hist U (DrvS d J) (k + 1)) :
    (drvPsi jx j0 P sc U (k + 1) η).init = drvPsi jx j0 P sc U k η.init := by
  show ((drvPsi jx j0 P sc U k η.init).snoc _).init = _
  exact Hist.init_snoc _ _

theorem stateAt_drvPsi_succ (k : ℕ) (η : Hist U (DrvS d J) (k + 1)) :
    CycScheme.stateAt P sc (k + 1) (drvPsi jx j0 P sc U (k + 1) η) =
      CycScheme.upd P sc (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η.init))
        (drvPsiOut (jx := jx) (β := β) j0 P sc
          (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η.init)) η.last) := by
  show CycScheme.upd P sc (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U (k + 1) η).init)
    (drvPsi jx j0 P sc U (k + 1) η).last = _
  rw [drvPsi_succ_init]
  congr 1
  show ((drvPsi jx j0 P sc U k η.init).snoc _).last = _
  exact Hist.last_snoc _ _

/-- The driving explored region only contains times already used. -/
theorem drvScheme_Z_bound :
    ∀ (k : ℕ) (η : Hist U (DrvS d J) k) (x : DrvS d J),
      x ∈ (drvScheme j0 P sc U hj).Z k η →
        x.2 ≤ (drvUse jx (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η)).1 x.1.2 : ℝ)
  | 0, _, x, hx => by simp [ExplScheme.Z] at hx
  | k + 1, η, x, hx => by
    classical
    set st := CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η.init) with hst
    have hW := CycScheme.wf_stateAt P sc k (drvPsi jx j0 P sc U k η.init)
    rw [stateAt_drvPsi_succ]
    rcases hx with hx | ⟨hxn, hxR⟩
    · have := drvScheme_Z_bound k η.init x hx
      refine this.trans ?_
      exact_mod_cast CycScheme.drvUse_upd_ge (jx := jx) P sc j0 hW _ x.1.2
    · -- a new point
      change drvProbeR (β := β) jx j0 P sc st x ≤ min η.last.1 (CycScheme.hOf P sc st) at hxR
      by_cases hc : st.2 = false ∧ x.1.2 = drvIdx jx j0 st ∧ 0 < x.2 - drvT jx P st ∧
          x.2 - drvT jx P st ≤ (CycScheme.hOf P sc st : ℝ) ∧
          drvPhi (β := β) jx P st x ∉ st.1.region β
      · unfold drvProbeR at hxR
        rw [ite_eq_left hc] at hxR
        obtain ⟨hb, hidx, hpos, hle, -⟩ := hc
        have hs : x.2 - drvT jx P st ≤ (CycScheme.sStar P sc st
            (drvPsiOut (jx := jx) (β := β) j0 P sc st η.last) : ℝ) := by
          unfold CycScheme.sStar drvPsiOut
          simp only
          have h1 : ENNReal.ofReal (x.2 - drvT jx P st) ≤ min η.last.1 (CycScheme.hOf P sc st) :=
            hxR
          have h2 : min η.last.1 (CycScheme.hOf P sc st : ℝ≥0∞) ≠ ⊤ :=
            ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
          have := ENNReal.toReal_mono h2 h1
          rw [ENNReal.toReal_ofReal hpos.le] at this
          exact this
        have := CycScheme.drvUse_upd_idx (jx := jx) P sc j0 hW hb
          (drvPsiOut (jx := jx) (β := β) j0 P sc st η.last)
        rw [hidx]
        linarith
      · unfold drvProbeR at hxR
        rw [ite_eq_right hc] at hxR
        exact absurd hxR (by
          have : ¬ (⊤ : ℝ≥0∞) ≤ min η.last.1 (CycScheme.hOf P sc st) := by
            intro h
            have := (le_min_iff.1 h).2
            exact absurd this (by simp)
          exact this)

/-- The driving scheme (a): the raw probe vanishes (is `∞`) on the explored region. -/
theorem drvScheme_R_top (k : ℕ) (η : Hist U (DrvS d J) k) (x : DrvS d J)
    (hx : x ∈ (drvScheme j0 P sc U hj).Z k η) :
    (drvScheme j0 P sc U hj).R k η x = ⊤ := by
  classical
  have hb := drvScheme_Z_bound j0 P sc U hj k η x hx
  have hW := CycScheme.wf_stateAt P sc k (drvPsi jx j0 P sc U k η)
  change drvProbeR (β := β) jx j0 P sc _ x = ⊤
  unfold drvProbeR
  rw [ite_eq_right]
  rintro ⟨-, hidx, hpos, -, -⟩
  rw [CycScheme.drvT_eq_drvUse (jx := jx) P j0 hW, ← hidx] at hpos
  linarith

/-- The driving scheme (a): the masked probe of step `j` is the raw probe. -/
theorem drvScheme_Rt (k : ℕ) (η : Hist U (DrvS d J) k) :
    (drvScheme j0 P sc U hj).Rt k η = (drvScheme j0 P sc U hj).R k η := by
  funext x
  by_cases hx : x ∈ (drvScheme j0 P sc U hj).Z k η
  · rw [ExplScheme.Rt_of_mem _ hx, drvScheme_R_top j0 P sc U hj k η x hx]
  · exact ExplScheme.Rt_of_notMem _ hx

end ElboimSly.Cyclic

end
