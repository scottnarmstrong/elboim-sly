/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.OneLapPair
public import ElboimSly.Paper.Base.RegularC
public import ElboimSly.Paper.Base.ProximityMeas
public import ElboimSly.Paper.Base.ProximityMain
public import ElboimSly.Paper.Base.Decoupling
public import ElboimSly.Paper.Base.Es8Constants
public import ElboimSly.Paper.Base.Threshold
public import Mathlib

/-!
# One pair of walks from a common cyclic time: auxiliary facts

One pair of walks from a common cyclic time.

* `cycContactSet`: the set `𝔓^r_{a,b}` of the written proof, in real time.
* regularity and measurability of the pairs of paths on both sides of cyclic walks within one lap (b);
* `lebSet_twoPaths_subset`: on the good event of decoupling the second particle, the contact set of the
  pair `(a + X₁, 𝔉_{a,b}(X₁, X₂))` is contained in the proximity set of proximity times of an independent walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper.Base

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `𝔓^r_{a,b} = {s ∈ [0,T] : ∃ s' ∈ [0,T], ‖W_{b,r}(s) - W_{a,r}(s')‖ ≤ ρ}`, in real time. -/
def cycContactSet (ν : Measure (RingSpace d β)) (a b : Fin d → ℤ) (r T ρ : ℝ) : Set ℝ :=
  {s | s ∈ Icc 0 T ∧ ∃ s' ∈ Icc (0 : ℝ) T,
    ‖ElboimSly.cycWalk ν b r s - ElboimSly.cycWalk ν a r s'‖ ≤ ρ}

theorem isStepPath_trajProc {ν : Measure (RingSpace d β)} (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    IsStepPath (trajProc ν x a) := by
  rw [trajProc_of_good hν]
  obtain ⟨p, -, hp⟩ := isForwardPath_exists_cycPath (fwdTrajFn_spec hν x a).1
  rw [← hp]
  exact ⟨p.1.rc, p.1.fin⟩

theorem isRegularPaths_pairOn {L : ℝ≥0} {p q : ℝ≥0 → Fin d → ℤ} (hp : IsStepPath p)
    (hq : IsStepPath q) : IsRegularPaths L (pairOn L p q) := by
  intro i
  fin_cases i
  · exact isStepPath_stop hp L
  · exact isStepPath_stop hq L

theorem isStepPath_translate_drvX {Ω : Type} [MeasurableSpace Ω]
    {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)} (j : Fin 2) (a : Fin d → ℤ) (ω : Ω) :
    IsStepPath fun u => a + drvX Ñ j ω u := by
  have hs := (drivers_isDrivingPath (Ñ := Ñ) j ω).step
  refine ⟨fun s => ?_, fun S => ?_⟩
  · filter_upwards [hs.rc s] with u hu; simp only [hu]
  · exact (hs.fin S).subset fun r hr =>
      ⟨⟨hr.1.1, fun hc => hr.1.2 (hc.mono fun u hu => by simp only [hu])⟩, hr.2⟩

/-- The pair `(a + X₁, 𝔉_{a,b}(X₁, X₂))` on `[0, T]`. -/
noncomputable def twoPaths {Ω : Type} (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a b : Fin d → ℤ)
    (T : ℝ≥0) (ω : Ω) : PathsOn d 2 T :=
  pairOn T (fun s => a + drvX Ñ 0 ω s) (drvTwo Ñ a b ω)

theorem extT_twoPaths_zero {Ω : Type} {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)} (a b : Fin d → ℤ)
    (T : ℝ≥0) (ω : Ω) (u : ℝ≥0) :
    extT T (twoPaths Ñ a b T ω) 0 u = a + drvX Ñ 0 ω (min u T) := rfl

theorem extT_twoPaths_one {Ω : Type} {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)} (a b : Fin d → ℤ)
    (T : ℝ≥0) (ω : Ω) (u : ℝ≥0) :
    extT T (twoPaths Ñ a b T ω) 1 u = drvTwo Ñ a b ω (min u T) := rfl

theorem isRegularPaths_twoPaths {Ω : Type} {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}
    [MeasurableSpace Ω] (a b : Fin d → ℤ) (T : ℝ≥0) (ω : Ω) :
    IsRegularPaths T (twoPaths Ñ a b T ω) :=
  isRegularPaths_pairOn (isStepPath_translate_drvX 0 a ω) (isTwoParticle_drvTwo a b ω).step

theorem measurable_twoPaths {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}
    (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) (a b : Fin d → ℤ)
    (T : ℝ≥0) : Measurable (twoPaths Ñ a b T) := by
  refine pairOn_measurable (fun s => ?_) (fun s => ?_)
  · exact (measurable_of_countable (fun x : Fin d → ℤ => a + x)).comp
      ((measurable_pi_apply s).comp (measurable_drvX h 0))
  · exact (drvTwo_adapted h a b s).mono (natFil_le (measurable_drvPair h) s) le_rfl

theorem lebSet_twoPaths_subset {Ω : Type} [MeasurableSpace Ω]
    {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)} (a b : Fin d → ℤ) {T : ℝ≥0} (n k : ℕ) (ρ : ℝ)
    (hρ : (19 / 10 : ℝ) ^ n + ((2 * n ^ 5 * k : ℕ) : ℝ) ≤ ρ) {ω : Ω}
    (hω : ω ∉ decoupBad Ñ a b T n k) :
    lebSet T T ((19 / 10 : ℝ) ^ n) 0 1 (twoPaths Ñ a b T ω) ⊆ baseProxSet Ñ a b T T ρ ω := by
  rintro x ⟨hx0, hxT, y, hy0, hyT, hxy⟩
  have hxT' : x.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hxT
  have hyT' : y.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hyT
  rw [extT_twoPaths_one, extT_twoPaths_zero, min_eq_left hxT', min_eq_left hyT'] at hxy
  refine ⟨hx0, hxT, y.toNNReal, hyT', ?_⟩
  have hD : ‖drvTwo Ñ a b ω x.toNNReal - b - drvX Ñ 1 ω x.toNNReal‖ ≤
      ((2 * n ^ 5 * k : ℕ) : ℝ) := by
    by_contra hcon
    exact hω ⟨x.toNNReal, hxT', not_le.1 hcon⟩
  calc ‖b + drvX Ñ 1 ω x.toNNReal - (a + drvX Ñ 0 ω y.toNNReal)‖
      ≤ ‖b + drvX Ñ 1 ω x.toNNReal - drvTwo Ñ a b ω x.toNNReal‖ +
        ‖drvTwo Ñ a b ω x.toNNReal - (a + drvX Ñ 0 ω y.toNNReal)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((2 * n ^ 5 * k : ℕ) : ℝ) + (19 / 10 : ℝ) ^ n := by
        refine add_le_add ?_ hxy
        rw [norm_sub_rev, ← sub_sub]
        exact hD
    _ ≤ ρ := by linarith

end ElboimSly.Paper

end
