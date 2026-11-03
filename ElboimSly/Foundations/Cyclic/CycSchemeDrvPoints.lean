/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvRegion
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvUse
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvPsi
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvCore
public import Mathlib

/-!
# The driving scheme (c): the driving outcome of a step

The driving scheme (c), (i), (ii). For a record with `GAt P (drl P jx Ñ) k r ρ`
(`drl` is the driven path rule for the canonical walks of the driving configuration `Ñ`) and a
good driving outcome `o'` (`DrvGood`: the output of sequential first-point exploration (d), (f) for the
driving scheme) we determine the environment outcome `o = ψ(o')`:

* `probeR_qpt`: the raw probe at the driving point `qpt v t` of direction `v` and local time `t`;
* `early_drv`: an atom of `Ñ` of copy `j_k` at a local time `t < s*` with a fresh image is
  impossible (`N'(D'_j(t)) = 0`);
* `fresh_conv_drv`: if `o` is not zero it is a Dirac mass at the image of an atom of `Ñ`;
* `zero_drv`: if `o` is zero then `ρ' = h`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] {J : Type} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]

/-- The driven path rule built from the canonical walks of the driving configuration `Ñ`. -/
noncomputable abbrev drl (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J)
    (Ñ : Measure (DrvS d J)) : PathRule I d :=
  drule P jx (fun j => srwPath Ñ j)

/-- The driving index `j_k` of walk `k` (after the first `k` driven world-lines). -/
noncomputable abbrev gj (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J)
    (Ñ : Measure (DrvS d J)) (k : ℕ) : J :=
  jx k (P.ideal (drl P jx Ñ) k)

/-- The driving offset `a_k` of walk `k`. -/
noncomputable abbrev ga (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J)
    (Ñ : Measure (DrvS d J)) (k : ℕ) : ℝ≥0 :=
  drvOffset jx (P.ideal (drl P jx Ñ) k) (gj P jx Ñ k)

variable {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) {P : CycPlan I d β} {sc : ℝ≥0∞}
  {Ñ : Measure (DrvS d J)} {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}

/-- The driving point of direction `v` at local time `t` of walk `k` at local time `r`. -/
noncomputable def qpt (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J)
    (Ñ : Measure (DrvS d J)) (k : ℕ) (r : ℝ≥0) (v : Dir d) (t : ℝ≥0) : DrvS d J :=
  ((v, gj P jx Ñ k), ((ga P jx Ñ k + (r + t) : ℝ≥0) : ℝ))

/-- `Ñ` has an atom at the driving point `qpt v t`. -/
def AtomAt (P : CycPlan I d β) (jx : ∀ k : ℕ, CycRecN I d k → J) (Ñ : Measure (DrvS d J))
    (k : ℕ) (r : ℝ≥0) (v : Dir d) (t : ℝ≥0) : Prop :=
  Ñ {qpt P jx Ñ k r v t} ≠ 0

omit [Countable I] [MeasurableSingletonClass I] [Countable J] [MeasurableSingletonClass J] in
theorem drvT_gAt (h : GAt P (drl P jx Ñ) k r ρ) :
    drvT jx P (ρ, false) = (ga P jx Ñ k : ℝ) + r := by
  unfold drvT
  rw [drvOff_of_gAt h, h.time]

omit [Countable I] [MeasurableSingletonClass I] [Countable J] [MeasurableSingletonClass J] in
theorem drvPhi_gAt (h : GAt P (drl P jx Ñ) k r ρ) (q : DrvS d J) :
    drvPhi (β := β) jx P (ρ, false) q =
      ((gdat P (drl P jx Ñ) k).copy, (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) q.1.1,
        (gdat P (drl P jx Ñ) k).clock β (q.2 - (ga P jx Ñ k : ℝ)).toNNReal)) := by
  unfold drvPhi
  rw [drvOff_of_gAt h, h.data, h.pos]

omit [Countable I] [MeasurableSingletonClass I] [Countable J] [MeasurableSingletonClass J] in
theorem fp_eq' (h : GAt P (drl P jx Ñ) k r ρ) (e : Edge d) (t : ℝ≥0) :
    CycSchemeEnv.fp P ρ e t = ((gdat P (drl P jx Ñ) k).copy,
      (e, (gdat P (drl P jx Ñ) k).clock β (r + t))) := by
  unfold CycSchemeEnv.fp CycScheme.frontPt
  rw [h.data, h.time]

omit [Countable I] [MeasurableSingletonClass I] [Countable J] [MeasurableSingletonClass J] in
theorem phi_qpt (h : GAt P (drl P jx Ñ) k r ρ) (v : Dir d) (t : ℝ≥0) :
    drvPhi (β := β) jx P (ρ, false) (qpt P jx Ñ k r v t) =
      CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t := by
  rw [drvPhi_gAt h, fp_eq' h]
  have : ((((ga P jx Ñ k + (r + t) : ℝ≥0) : ℝ)) - (ga P jx Ñ k : ℝ)).toNNReal = r + t := by
    have e : ((((ga P jx Ñ k + (r + t) : ℝ≥0) : ℝ)) - (ga P jx Ñ k : ℝ)) = ((r + t : ℝ≥0) : ℝ) := by
      push_cast; ring
    rw [e, Real.toNNReal_coe]
  simp only [qpt, this]

open scoped Classical in
omit [Countable I] [MeasurableSingletonClass I] [Countable J] [MeasurableSingletonClass J] in
theorem probeR_qpt (h : GAt P (drl P jx Ñ) k r ρ) (v : Dir d) {t : ℝ≥0} (ht0 : 0 < t)
    (hth : t ≤ CycScheme.hOf P sc (ρ, false)) :
    drvProbeR (β := β) jx j0 P sc (ρ, false) (qpt P jx Ñ k r v t) =
      if CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t ∈ ρ.region β
        then ⊤ else (t : ℝ≥0∞) := by
  have hT := drvT_gAt h
  have hy : (qpt P jx Ñ k r v t).2 - drvT jx P (ρ, false) = (t : ℝ) := by
    rw [hT]; simp only [qpt]; push_cast; ring
  unfold drvProbeR
  rw [phi_qpt h, hy]
  by_cases hm : CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t ∈ ρ.region β
  · rw [ite_eq_left hm, ite_eq_right]
    rintro ⟨-, -, -, -, hn⟩
    exact hn hm
  · rw [ite_eq_right hm, ite_eq_left]
    · exact ENNReal.ofReal_coe_nnreal
    · exact ⟨rfl, by rw [drvIdx_of_gAt j0 h]; rfl, by exact_mod_cast ht0,
        by exact_mod_cast hth, hm⟩

omit [Countable I] [MeasurableSingletonClass I] [Countable J] [MeasurableSingletonClass J] in
theorem exists_of_probeR_ne_top (h : GAt P (drl P jx Ñ) k r ρ) (q : DrvS d J)
    (hne : drvProbeR (β := β) jx j0 P sc (ρ, false) q ≠ ⊤) :
    ∃ (v : Dir d) (t : ℝ≥0), q = qpt P jx Ñ k r v t ∧ 0 < t ∧ t ≤ CycScheme.hOf P sc (ρ, false) ∧
      CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t ∉ ρ.region β := by
  have hT := drvT_gAt h
  unfold drvProbeR at hne
  by_cases hc : (ρ, false).2 = false ∧ q.1.2 = drvIdx jx j0 (ρ, false) ∧
      0 < q.2 - drvT jx P (ρ, false) ∧ q.2 - drvT jx P (ρ, false) ≤
        (CycScheme.hOf P sc (ρ, false) : ℝ) ∧ drvPhi (β := β) jx P (ρ, false) q ∉
          (ρ, false).1.region β
  swap
  · rw [ite_eq_right hc] at hne; exact absurd rfl hne
  obtain ⟨-, h2, h3, h4, h5⟩ := hc
  rw [drvIdx_of_gAt j0 h] at h2
  set t : ℝ≥0 := (q.2 - drvT jx P (ρ, false)).toNNReal with ht
  have htc : (t : ℝ) = q.2 - drvT jx P (ρ, false) := Real.coe_toNNReal _ h3.le
  have hq : q = qpt P jx Ñ k r q.1.1 t := by
    refine Prod.ext (Prod.ext rfl h2) ?_
    simp only [qpt]
    push_cast
    rw [htc, hT]; ring
  refine ⟨q.1.1, t, hq, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_pos, htc]; exact h3
  · rw [← NNReal.coe_le_coe, htc]; exact h4
  · rw [← phi_qpt h, ← hq]; exact h5

/-- What the exploration theorem provides about the outcome of a step of the driving scheme
(sequential first-point exploration (d), (f)), in terms of the raw probe. -/
structure DrvGood (jx : ∀ k : ℕ, CycRecN I d k → J) (j0 : J) (P : CycPlan I d β) (sc : ℝ≥0∞)
    (Ñ : Measure (DrvS d J)) (st : CycScheme.State I d) (o' : Outcome (DrvS d J)) : Prop where
  V_eq : o'.2 = Ñ.restrict {y | drvProbeR (β := β) jx j0 P sc st y ≤ o'.1}
  le_h : o'.1 ≤ (CycScheme.hOf P sc st : ℝ≥0∞)
  front : o'.2 {y | drvProbeR (β := β) jx j0 P sc st y ≠ o'.1} = 0
  dirac : o'.2 Set.univ ≠ 0 → ∃ x, o'.2 = Measure.dirac x ∧
    drvProbeR (β := β) jx j0 P sc st x = o'.1
  zero : o'.2 Set.univ = 0 → o'.1 = (CycScheme.hOf P sc st : ℝ≥0∞)
  tau_eq : tau (drvIntensity d J) o'.2 = o'.2

variable {o' : Outcome (DrvS d J)}

omit [Countable I] [MeasurableSingletonClass I] in
theorem V_apply_of_le (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') {y : DrvS d J}
    (hy : drvProbeR (β := β) jx j0 P sc (ρ, false) y ≤ o'.1) : o'.2 {y} = Ñ {y} := by
  rw [hg.V_eq, Measure.restrict_apply (measurableSet_singleton _),
    Set.inter_eq_left.2 (Set.singleton_subset_iff.2 (show y ∈ {y | _ ≤ o'.1} from hy))]

omit [Countable I] [MeasurableSingletonClass I] in
/-- No atom of copy `j_k` before the entrance time with a fresh image: `N'(D'_j(t)) = 0`. -/
theorem early_drv (h : GAt P (drl P jx Ñ) k r ρ) (hg : DrvGood jx j0 P sc Ñ (ρ, false) o')
    (v : Dir d) {t : ℝ≥0} (ht0 : 0 < t) (hto : (t : ℝ≥0∞) < o'.1)
    (hat : AtomAt P jx Ñ k r v t) :
    CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t ∈ ρ.region β := by
  by_contra hfresh
  have hth : t ≤ CycScheme.hOf P sc (ρ, false) :=
    (ENNReal.coe_le_coe.1 (hto.le.trans hg.le_h))
  have hR := probeR_qpt j0 h v ht0 hth (sc := sc)
  rw [ite_eq_right hfresh] at hR
  have h1 : o'.2 {qpt P jx Ñ k r v t} = Ñ {qpt P jx Ñ k r v t} :=
    V_apply_of_le j0 hg (by rw [hR]; exact hto.le)
  have h2 : o'.2 {qpt P jx Ñ k r v t} = 0 := by
    refine measure_mono_null ?_ hg.front
    rintro _ rfl
    show drvProbeR (β := β) jx j0 P sc (ρ, false) _ ≠ o'.1
    rw [hR]; exact hto.ne
  exact hat (h1 ▸ h2)

omit [Countable I] [MeasurableSingletonClass I] in
theorem psiOut_snd_dirac (hj : ∀ k, Measurable (jx k))
    (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') {q : DrvS d J}
    (hq : o'.2 = Measure.dirac q) (hF : q ∈ drvF j0 P sc (ρ, false) (jx := jx)) :
    (drvPsiOut (jx := jx) (β := β) j0 P sc (ρ, false) o').2 =
      Measure.dirac (drvPhi (β := β) jx P (ρ, false) q) := by
  classical
  unfold drvPsiOut
  simp only
  rw [hg.tau_eq, hq, restrict_dirac, ite_eq_left hF]
  have hφ : Measurable (drvPhi (β := β) jx P (ρ, false) : DrvS d J → CycS I d β) :=
    measurable_drvPhi (P := P) hj (st := fun _ : DrvS d J => (ρ, false)) measurable_const
      measurable_id
  exact Measure.map_dirac' hφ q

omit [Countable I] [MeasurableSingletonClass I] in
theorem psiOut_snd_zero (hg : DrvGood jx j0 P sc Ñ (ρ, false) o') (hz : o'.2 Set.univ = 0) :
    (drvPsiOut (jx := jx) (β := β) j0 P sc (ρ, false) o').2 = 0 := by
  unfold drvPsiOut
  simp only
  rw [hg.tau_eq, Measure.measure_univ_eq_zero.1 hz]
  simp

end CycSchemeGen
end ElboimSly.Cyclic

end
