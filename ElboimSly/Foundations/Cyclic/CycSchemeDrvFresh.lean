/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvRules
public import Mathlib

/-!
# The driving scheme (c): the revealed point and the known rings of a driven step

The driving scheme (c), (ii). Port of the facts of `CycSchemeEnvCore`/`CycSchemeEnvNewV`
about the front of a step to the invariant `GAt`:

* `GAt.finite_clocks`, `hFr_ne_zero'`, `ringSet_front_of_hFr'`: the infimum `h_fr` is attained by a
  known ring at the front, and is positive;
* `leastEdge_min`: the `edgeEnc`-least edge;
* `dirac_data`: if the revealed driving measure `V'` is nonzero, it is a Dirac mass at the driving
  point `qpt v t` of an atom of `Ñ` with an unexplored image, and the environment outcome
  `ψ(o')` is the Dirac mass at the image;
* `psiOut_univ_ne_zero_iff`: `ψ(o')` is nonzero iff `V'` is.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] {J : Type} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) {P : CycPlan I d β} {sc : ℝ≥0∞}
  {Ñ : Measure (DrvS d J)} {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o' : Outcome (DrvS d J)}

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem GAt.finite_clocks {rl : PathRule I d} (h : GAt P rl k r ρ) :
    {θ : AddCircle β | ∃ x ∈ ρ.ringSet β, x.2.2 = θ}.Finite := by
  rw [h.rec_eq]
  refine finite_clock_ringSet _ (fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [CycRec.snoc, Fin.snoc_last]
    show ((gpth P rl k).1.cut (r : ℝ≥0∞)).len ≠ ⊤
    rw [CPath.cut_len]; exact ENNReal.coe_ne_top
  · simp only [CycRec.snoc, Fin.snoc_castSucc]
    rw [P.ideal_apply]
    have := h.allFin j j.2
    exact this.ne

omit [Countable I] [MeasurableSingletonClass I] in
theorem hFr_ne_zero' {rl : PathRule I d} (h : GAt P rl k r ρ) :
    CycScheme.hFr β ρ (CycScheme.cur P (ρ, false)) ≠ 0 := by
  rcases CycScheme.hFr_attained ρ (CycScheme.cur P (ρ, false)) h.finite_clocks with
    htop | ⟨x, hx, h1, h2, h3⟩
  · rw [htop]; exact ENNReal.top_ne_zero
  · rw [h3]
    have hpos := (CycScheme.circS_mem_Ioc (CycScheme.cur P (ρ, false)) (x.1, x.2.1) x.2.2).1
    exact (ENNReal.ofReal_pos.2 hpos).ne'

omit [Countable I] [MeasurableSingletonClass I] in
theorem ringSet_front_of_hFr' {rl : PathRule I d} (h : GAt P rl k r ρ) {s : ℝ≥0} (hs0 : 0 < s)
    (hsh : s ≤ CycScheme.hOf P sc (ρ, false))
    (hs : (s : ℝ≥0∞) = CycScheme.hFr β ρ (CycScheme.cur P (ρ, false))) :
    ∃ e0, Edge.Mem (CycScheme.cur P (ρ, false)).pos e0 ∧
      CycSchemeEnv.fp P ρ e0 s ∈ ρ.ringSet β := by
  have hsβ : (s : ℝ) ∈ Ioc 0 β :=
    ⟨by exact_mod_cast hs0, (by exact_mod_cast hsh : (s : ℝ) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (CycScheme.hOf_le_beta P sc _)⟩
  rcases CycScheme.hFr_attained ρ (CycScheme.cur P (ρ, false)) h.finite_clocks with
    htop | ⟨x, hx, h1, h2, h3⟩
  · rw [← hs] at htop; exact absurd htop ENNReal.coe_ne_top
  · refine ⟨x.2.1, h2, ?_⟩
    have hc : circS (CycScheme.cur P (ρ, false)).frontT (CycScheme.cur P (ρ, false)).frontS
        (x.1, x.2.1) x.2.2 = s := by
      have hpos := (CycScheme.circS_mem_Ioc (CycScheme.cur P (ρ, false)) (x.1, x.2.1) x.2.2).1
      have h4 : (s : ℝ≥0∞) = ENNReal.ofReal (circS (CycScheme.cur P (ρ, false)).frontT
          (CycScheme.cur P (ρ, false)).frontS (x.1, x.2.1) x.2.2) := hs.trans h3
      have h5 := congrArg ENNReal.toReal h4
      rw [ENNReal.toReal_ofReal hpos.le] at h5
      simpa using h5.symm
    have hx2 : x.2.2 = (CycScheme.cur P (ρ, false)).data.clock β
        ((CycScheme.cur P (ρ, false)).time + s) := by
      have h6 := circX_sinv (CycScheme.cur P (ρ, false)).frontT
        (CycScheme.cur P (ρ, false)).frontS
        (CycScheme.cur P (ρ, false)).frontS_cases (x.1, x.2.1) x.2.2
      rw [hc] at h6
      exact h6.symm.trans (CycEntry.circX_front (CycScheme.cur P (ρ, false)) (x.1, x.2.1) s)
    have : CycSchemeEnv.fp P ρ x.2.1 s = x := by
      unfold CycSchemeEnv.fp CycScheme.frontPt
      exact Prod.ext h1.symm (Prod.ext rfl hx2.symm)
    rw [this]; exact hx

theorem leastEdge_min {Q : Edge d → Prop} {e : Edge d} (h : leastEdge Q = some e) :
    Q e ∧ ∀ e', Q e' → edgeEnc e ≤ edgeEnc e' := by
  classical
  unfold leastEdge at h
  by_cases hex : ∃ e, Q e ∧ ∀ e', Q e' → edgeEnc e ≤ edgeEnc e'
  · rw [dite_eq_left hex] at h
    have := Option.some.inj h
    rw [← this]
    exact hex.choose_spec
  · rw [dite_eq_right hex] at h
    exact absurd h (by simp)

theorem edgeOther_spec {w : Fin d → ℤ} {e : Edge d} (h : Edge.Mem w e) :
    e.1 = s(w, edgeOther w e) := by
  have hw : w ∈ e.1 := h
  unfold edgeOther
  rw [dite_eq_left hw]
  exact (Sym2.other_spec hw).symm

omit [Countable I] [MeasurableSingletonClass I] in
/-- The data of a nonzero revealed measure: a Dirac mass at an atom of `Ñ` with unexplored image. -/
theorem dirac_data (hj : ∀ k, Measurable (jx k)) (h : GAt P (drl P jx Ñ) k r ρ)
    (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') (hz : o'.2 Set.univ ≠ 0) :
    ∃ (v : Dir d) (t : ℝ≥0), 0 < t ∧ t ≤ CycScheme.hOf P sc (ρ, false) ∧
      CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t ∉ ρ.region β ∧
      o'.1 = t ∧ AtomAt P jx Ñ k r v t ∧
      (drvPsiOut (jx := jx) (β := β) j0 P sc (ρ, false) o').2 =
        Measure.dirac (CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t) := by
  obtain ⟨q, hq, hRq⟩ := hg.dirac hz
  have hne : drvProbeR (β := β) jx j0 P sc (ρ, false) q ≠ ⊤ := by
    rw [hRq]; exact ne_top_of_le_ne_top ENNReal.coe_ne_top hg.le_h
  obtain ⟨v, t, rfl, ht0, hth, hfresh⟩ := exists_of_probeR_ne_top j0 h q hne
  have hR := probeR_qpt j0 h v ht0 hth (sc := sc)
  rw [ite_eq_right hfresh] at hR
  have hto : o'.1 = t := by rw [← hRq, hR]
  refine ⟨v, t, ht0, hth, hfresh, hto, ?_, ?_⟩
  · have h1 := V_apply_of_le j0 hg (y := qpt P jx Ñ k r v t) (by rw [hR, hto])
    rw [hq, Measure.dirac_apply_of_mem (Set.mem_singleton _)] at h1
    intro h0
    exact one_ne_zero (h1.trans h0)
  · have hF : qpt P jx Ñ k r v t ∈ drvF j0 P sc (ρ, false) (jx := jx) := by
      have hT := drvT_gAt h
      have hy : (qpt P jx Ñ k r v t).2 - drvT jx P (ρ, false) = (t : ℝ) := by
        rw [hT]; simp only [qpt]; push_cast; ring
      refine ⟨rfl, by rw [drvIdx_of_gAt j0 h]; rfl, ?_, ?_⟩
      · rw [hy]; exact_mod_cast ht0
      · rw [hy]; exact_mod_cast hth
    rw [psiOut_snd_dirac j0 hj hg hq hF, phi_qpt h]

omit [Countable I] [MeasurableSingletonClass I] in
theorem psiOut_univ_ne_zero_iff (hj : ∀ k, Measurable (jx k)) (h : GAt P (drl P jx Ñ) k r ρ)
    (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') :
    (drvPsiOut (jx := jx) (β := β) j0 P sc (ρ, false) o').2 Set.univ ≠ 0 ↔
      o'.2 Set.univ ≠ 0 := by
  constructor
  · intro hne hz
    exact hne (by rw [psiOut_snd_zero j0 hg hz]; simp)
  · intro hz
    obtain ⟨v, t, -, -, -, -, -, hd⟩ := dirac_data j0 hj h hg hz
    rw [hd]; simp

end CycSchemeGen
end ElboimSly.Cyclic

end
