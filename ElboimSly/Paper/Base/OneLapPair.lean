/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.PairRecord
public import ElboimSly.Paper.Base.TwoParticleAdapt
public import ElboimSly.Paper.Base.Regular
public import ElboimSly.Foundations.Cyclic.CycLawTransfer
public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import ElboimSly.Foundations.Cyclic.CycDrivenLawMeas
public import ElboimSly.Foundations.Cyclic.CycDrivenLawBridge
public import Mathlib

/-!
# Cyclic walks within one lap: the law of a pair

Cyclic walks within one lap (b), (c), "Conclusion".

The law of the pair of final records of the plan `𝔭` (several walks explored one after another (b), in the form
`law_transfer`) is pushed forward by the measurable map `Φ_L` to paths on `[0, L]`.

* `pairOn L p q`: the pair of paths `(p, q)` as an element of `Π_L = ((ℤ^d)^2)^{[0, L]}`.
* `one_lap_b_aux`: the law of `(W_{a,r}, W_{b,r})` against that of the pair
  `(a + X₁, 𝔉_{a,b}(X₁, X₂))`, in terms of the `PairPlan` records.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The pair of paths `(p, q)` on `[0, L]`, as an element of `Π_L` with `k = 2`. -/
def pairOn (L : ℝ≥0) (p q : ℝ≥0 → Fin d → ℤ) : PathsOn d 2 L :=
  fun s => ![p s.1, q s.1]

/-- The pair of coordinate paths of a record, on `[0, L]`. -/
def recPairOn (L : ℝ≥0) (junk : CycEntry Unit d) (ρ : CycRec Unit d) : PathsOn d 2 L :=
  fun s i => (ρ.coord junk i.val).path.fn s.1

theorem measurable_recPairOn (L : ℝ≥0) (junk : CycEntry Unit d) :
    Measurable (recPairOn L junk) :=
  measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun i =>
    (CPath.measurable_eval s.1).comp (measurable_entry_path.comp
      (CycRec.measurable_coord junk i.val))

/-- The pair of driving paths as a path with values in `ℤ^d × ℤ^d`. -/
noncomputable def pairCPath (X Y : CPath (Fin d → ℤ)) : CPath (PairE d) :=
  pairPath X.fn Y.fn ⟨X.rc, X.fin⟩ ⟨Y.rc, Y.fin⟩

theorem measurable_pairCPath :
    Measurable fun p : CPath (Fin d → ℤ) × CPath (Fin d → ℤ) => pairCPath p.1 p.2 := by
  refine (CPath.measurable_iff _).2 ⟨measurable_const, fun s => ?_⟩
  exact ((CPath.measurable_eval s).comp measurable_fst).prodMk
    ((CPath.measurable_eval s).comp measurable_snd)

theorem pairOn_measurable {L : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {p q : Ω → ℝ≥0 → Fin d → ℤ}
    (hp : ∀ s, Measurable fun ω => p ω s) (hq : ∀ s, Measurable fun ω => q ω s) :
    Measurable fun ω => pairOn L (p ω) (q ω) := by
  refine measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact hp s.1
  · exact hq s.1

theorem srwPath_fn_zero {J : Type} [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    (Ñ : Measure ((Dir d × J) × ℝ)) (j : J) : (srwPath Ñ j).1.fn 0 = 0 :=
  (walkPath_isDriving _).zero

theorem measurable_trajProc_slice (a : Fin d → ℤ) (r : ℝ) (s : ℝ≥0) :
    Measurable fun N : Measure (Unit × RingSpace d β) => trajProc (cycSlice () N) a r s :=
  (measurable_pi_apply s).comp ((measurable_trajProc a r).comp (measurable_cycSlice ()))

theorem pairJx_measurable (k : ℕ) : Measurable (pairJx (d := d) k) := by
  unfold pairJx; exact measurable_const

/-- **cyclic walks within one lap (b)**: the law of the pair `(W^ν_{a,r}, W^ν_{b,r})` on `[0, L]`, `L < β`,
is that of `(a + X₁, 𝔉_{a,b}(X₁, X₂))`. -/
theorem one_lap_b {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Pe : Measure Ω}
    {Pd : Measure Ω'} {ν : Ω → Measure (RingSpace d β)}
    {Ñ : Ω' → Measure ((Dir d × Fin 2) × ℝ)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe)
    (hÑ : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) Pd)
    (a b : Fin d → ℤ) (r : ℝ) {L : ℝ≥0} (hL : (L : ℝ) < β) :
    Pe.map (fun ω => pairOn L (trajProc (ν ω) a r) (trajProc (ν ω) b r)) =
      Pd.map (fun ω => pairOn L (fun s => a + drvX Ñ 0 ω s)
        (twoParticle a b (drvX Ñ 0 ω) (drvX Ñ 1 ω))) := by
  classical
  set P := pairPlan d β a b r r L with hP
  have hK : 0 < P.K := by
    show (0 : ℕ∞) < 2
    norm_num
  let A : Measure (Unit × RingSpace d β) → PathsOn d 2 L := fun N =>
    pairOn L (trajProc (cycSlice () N) a r) (trajProc (cycSlice () N) b r)
  let B : Measure ((Dir d × Fin 2) × ℝ) → PathsOn d 2 L := fun Ñ =>
    pairOn L (fun s => a + (srwPath Ñ 0).1.fn s)
      (solQ a b (pairCPath (srwPath Ñ 0).1 (srwPath Ñ 1).1))
  have hA : Measurable A := pairOn_measurable (measurable_trajProc_slice a r)
    (measurable_trajProc_slice b r)
  have hB : Measurable B := by
    refine pairOn_measurable (fun s => ?_) (fun s => ?_)
    · exact (measurable_of_countable (fun x : Fin d → ℤ => a + x)).comp
        ((CPath.measurable_eval s).comp (measurable_srwPath 0))
    · exact (measurable_solQ a b s).comp (measurable_pairCPath.comp
        ((measurable_srwPath 0).prodMk (measurable_srwPath 1)))
  have hAe : ∀ N : Measure (Unit × RingSpace d β), CycGood N →
      recPairOn L P.junk (P.envFinal N) = A N := by
    intro N hN
    funext s i
    fin_cases i
    · show ((P.envFinal N).coord P.junk 0).path.fn s.1 = trajProc (cycSlice () N) a r s.1
      rw [envFinal_coord_zero a b r r L hN P.junk s.1, min_eq_left s.2.2]
      exact cycWalk_eq_trajProc (hN ()) a r s.1
    · show ((P.envFinal N).coord P.junk 1).path.fn s.1 = trajProc (cycSlice () N) b r s.1
      rw [envFinal_coord_one a b r r L hN P.junk s.1, min_eq_left s.2.2]
      exact cycWalk_eq_trajProc (hN ()) b r s.1
  have hBd : ∀ᵐ Ñ' ∂(Pd.map Ñ), recPairOn L P.junk
      (P.drivenFinal pairJx (fun j => srwPath Ñ' j)) = B Ñ' := by
    refine Filter.Eventually.of_forall fun Ñ' => ?_
    funext s i
    fin_cases i
    · show ((P.drivenFinal pairJx (fun j => srwPath Ñ' j)).coord P.junk 0).path.fn s.1 =
        a + (srwPath Ñ' 0).1.fn s.1
      rw [hP, drivenFinal_coord_zero a b r r L _ (srwPath_fn_zero Ñ' 0) hL P.junk s.1,
        min_eq_left s.2.2]
    · show ((P.drivenFinal pairJx (fun j => srwPath Ñ' j)).coord P.junk 1).path.fn s.1 =
        solQ a b (pairCPath (srwPath Ñ' 0).1 (srwPath Ñ' 1).1) s.1
      rw [hP, drivenFinal_coord_one a b r L _ (srwPath_fn_zero Ñ' 0) (srwPath_fn_zero Ñ' 1) hL
        P.junk s.1, min_eq_left s.2.2]
      exact congrFun (twoParticle_eq_solQ_pairPath a b _ _) _
  have hgood : ∀ᵐ ω ∂Pe, CycGood ((ν ω).map (Prod.mk ())) :=
    (ae_good hν).mono fun ω hω => cycGood_map_unit hω
  have key := law_transfer (jx := pairJx) (0 : Fin 2) P pairJx_measurable hK
    (isPPP_envUnit hν) hÑ hgood
    (measurable_recPairOn L P.junk) hA hB hAe hBd
  have eA : (fun ω => A ((ν ω).map (Prod.mk ()))) =
      fun ω => pairOn L (trajProc (ν ω) a r) (trajProc (ν ω) b r) := by
    funext ω
    simp only [A, cycSlice_map_unit]
  have eB : (fun ω => B (Ñ ω)) = fun ω => pairOn L (fun s => a + drvX Ñ 0 ω s)
      (twoParticle a b (drvX Ñ 0 ω) (drvX Ñ 1 ω)) := by
    funext ω
    simp only [B]
    funext s i
    fin_cases i
    · rfl
    · exact (congrFun (twoParticle_eq_solQ_pairPath a b _ _) _).symm
  rw [← eA, ← eB]
  exact key.symm

/-- **cyclic walks within one lap (c)**: if the windows `[r_a, r_a + L]` and `[r_b, r_b + L]` are disjoint
modulo `β`, the pair `(W^ν_{a,r_a}, W^ν_{b,r_b})` on `[0, L]` has the law of
`(a + X₁, b + X₂)`. -/
theorem one_lap_c {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Pe : Measure Ω}
    {Pd : Measure Ω'} {ν : Ω → Measure (RingSpace d β)}
    {Ñ : Ω' → Measure ((Dir d × Fin 2) × ℝ)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe)
    (hÑ : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) Pd)
    (a b : Fin d → ℤ) (ra rb : ℝ) {L : ℝ≥0} (h1 : ra + L < rb) (h2 : rb + L < ra + β) :
    Pe.map (fun ω => pairOn L (trajProc (ν ω) a ra) (trajProc (ν ω) b rb)) =
      Pd.map (fun ω => pairOn L (fun s => a + drvX Ñ 0 ω s) (fun s => b + drvX Ñ 1 ω s)) := by
  classical
  have hL : (L : ℝ) < β := by
    have := L.2
    linarith
  set P := pairPlan d β a b ra rb L with hP
  have hK : 0 < P.K := by
    show (0 : ℕ∞) < 2
    norm_num
  let A : Measure (Unit × RingSpace d β) → PathsOn d 2 L := fun N =>
    pairOn L (trajProc (cycSlice () N) a ra) (trajProc (cycSlice () N) b rb)
  let B : Measure ((Dir d × Fin 2) × ℝ) → PathsOn d 2 L := fun Ñ =>
    pairOn L (fun s => a + (srwPath Ñ 0).1.fn s) (fun s => b + (srwPath Ñ 1).1.fn s)
  have hA : Measurable A := pairOn_measurable (measurable_trajProc_slice a ra)
    (measurable_trajProc_slice b rb)
  have hB : Measurable B := by
    refine pairOn_measurable (fun s => ?_) (fun s => ?_)
    · exact (measurable_of_countable (fun x : Fin d → ℤ => a + x)).comp
        ((CPath.measurable_eval s).comp (measurable_srwPath 0))
    · exact (measurable_of_countable (fun x : Fin d → ℤ => b + x)).comp
        ((CPath.measurable_eval s).comp (measurable_srwPath 1))
  have hAe : ∀ N : Measure (Unit × RingSpace d β), CycGood N →
      recPairOn L P.junk (P.envFinal N) = A N := by
    intro N hN
    funext s i
    fin_cases i
    · show ((P.envFinal N).coord P.junk 0).path.fn s.1 = trajProc (cycSlice () N) a ra s.1
      rw [envFinal_coord_zero a b ra rb L hN P.junk s.1, min_eq_left s.2.2]
      exact cycWalk_eq_trajProc (hN ()) a ra s.1
    · show ((P.envFinal N).coord P.junk 1).path.fn s.1 = trajProc (cycSlice () N) b rb s.1
      rw [envFinal_coord_one a b ra rb L hN P.junk s.1, min_eq_left s.2.2]
      exact cycWalk_eq_trajProc (hN ()) b rb s.1
  have hBd : ∀ᵐ Ñ' ∂(Pd.map Ñ), recPairOn L P.junk
      (P.drivenFinal pairJx (fun j => srwPath Ñ' j)) = B Ñ' := by
    refine Filter.Eventually.of_forall fun Ñ' => ?_
    funext s i
    fin_cases i
    · show ((P.drivenFinal pairJx (fun j => srwPath Ñ' j)).coord P.junk 0).path.fn s.1 =
        a + (srwPath Ñ' 0).1.fn s.1
      rw [hP, drivenFinal_coord_zero a b ra rb L _ (srwPath_fn_zero Ñ' 0) hL P.junk s.1,
        min_eq_left s.2.2]
    · show ((P.drivenFinal pairJx (fun j => srwPath Ñ' j)).coord P.junk 1).path.fn s.1 =
        b + (srwPath Ñ' 1).1.fn s.1
      rw [hP, drivenFinal_coord_one_far a b ra rb L _ (srwPath_fn_zero Ñ' 0)
        (srwPath_fn_zero Ñ' 1) hL h1 h2 P.junk s.1, min_eq_left s.2.2]
  have hgood : ∀ᵐ ω ∂Pe, CycGood ((ν ω).map (Prod.mk ())) :=
    (ae_good hν).mono fun ω hω => cycGood_map_unit hω
  have key := law_transfer (jx := pairJx) (0 : Fin 2) P pairJx_measurable hK
    (isPPP_envUnit hν) hÑ hgood
    (measurable_recPairOn L P.junk) hA hB hAe hBd
  have eA : (fun ω => A ((ν ω).map (Prod.mk ()))) =
      fun ω => pairOn L (trajProc (ν ω) a ra) (trajProc (ν ω) b rb) := by
    funext ω
    simp only [A, cycSlice_map_unit]
  have eB : (fun ω => B (Ñ ω)) = fun ω => pairOn L (fun s => a + drvX Ñ 0 ω s)
      (fun s => b + drvX Ñ 1 ω s) := rfl
  rw [← eA, ← eB]
  exact key.symm

end ElboimSly.Paper

end
