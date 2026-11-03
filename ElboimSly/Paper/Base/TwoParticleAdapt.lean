/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.TwoParticleSol
public import ElboimSly.Paper.Base.Drivers
public import ElboimSly.Foundations.Cyclic.CPathStop
public import Mathlib

/-!
# Adaptedness of the two-particle path

Contacts are few (i): `y = 𝔉_{a,b}(X₁, X₂)` is adapted to the natural filtration
`𝒢_t = σ(X̄(s) : s ≤ t)` of `X̄ = (X₁, X₂)`.

* `solQ_stop`: causality, `y` at time `t` only depends on the driving paths stopped at `t`.
* `twoParticle_adapted`: `ω ↦ y(ω)(t)` is `𝒢_t`-measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ}

theorem stepG_stop (a : Fin d → ℤ) (q : CPath (PairE d)) {t r : ℝ≥0} (hr : 0 < r) (hrt : r ≤ t)
    (w : Fin d → ℤ) : stepG a (q.stop t) r w = stepG a q r w := by
  rw [stepG_eq_V a _ hr, stepG_eq_V a _ hr]
  have e1 : (q.stop t).fn r = q.fn r := by simp [min_eq_left hrt]
  have e2 : (q.stop t).left r = q.left r := by
    refine (q.stop t).left_eq_of_eventually hr ?_
    filter_upwards [q.eventually_left hr, self_mem_nhdsWithin (a := r) (s := Iio r)] with u hu hu'
    rw [CPath.stop_fn, min_eq_left ((le_of_lt (mem_Iio.1 hu')).trans hrt), hu]
  rw [e1, e2]

/-- Causality: the state at time `t` only depends on the driving path up to `t`. -/
theorem solQ_stop (a b : Fin d → ℤ) (q : CPath (PairE d)) (t : ℝ≥0) :
    solQ a b (q.stop t) t = solQ a b q t := by
  set y' := solQ a b (q.stop t) with hy'
  set y := solQ a b q with hy
  have hs' : IsStepPath y' := isStepPath_solQ a b _
  have hs : IsStepPath y := isStepPath_solQ a b _
  have key : ∀ s, s ≤ t → y' s = y s := by
    refine real_induction (Q := fun s => s ≤ t → y' s = y s) ?_ ?_ ?_
    · intro _; rw [hy', hy, solQ_zero, solQ_zero]
    · intro r hr hev hrt
      have hev' : ∀ᶠ u in 𝓝[<] r, y' u = y u := by
        filter_upwards [hev, self_mem_nhdsWithin (a := r) (s := Iio r)] with u hu hu'
        exact hu ((le_of_lt (mem_Iio.1 hu')).trans hrt)
      have hll : Function.leftLim y' r = Function.leftLim y r := by
        refine IsStepPath.leftLim_eq hr ?_
        filter_upwards [hev', hs.eventually_left_leftLim hr] with u h1 h2
        rw [h1, h2]
      have r1 := (isTwoParticle_solQ a b (q.stop t)).rule r hr
      have r2 := (isTwoParticle_solQ a b q).rule r hr
      have g : twoStep a (fun s => ((q.stop t).fn s).1) (fun s => ((q.stop t).fn s).2) r
          (Function.leftLim y r) = twoStep a (fun s => (q.fn s).1) (fun s => (q.fn s).2) r
          (Function.leftLim y r) := stepG_stop a q hr hrt _
      calc y' r = _ := r1
        _ = _ := by rw [hll]; exact g
        _ = y r := r2.symm
    · intro r hr
      by_cases hrt : r ≤ t
      · have e := hr hrt
        filter_upwards [hs'.rc r, hs.rc r] with u h1 h2 _
        rw [h1, h2, e]
      · filter_upwards [self_mem_nhdsWithin (a := r) (s := Ici r)] with u hu hut
        exact absurd hut (not_le.2 (lt_of_lt_of_le (not_le.1 hrt) hu))
  exact key t le_rfl

/-- The pair of driving paths as a jump-list path of infinite length. -/
def pairPath (x₁ x₂ : ℝ≥0 → Fin d → ℤ) (h1 : IsStepPath x₁) (h2 : IsStepPath x₂) :
    CPath (PairE d) where
  len := ⊤
  fn s := (x₁ s, x₂ s)
  rc := (isStepPath_pair h1 h2).rc
  fin := (isStepPath_pair h1 h2).fin
  const := fun s s' h _ => by simp at h

theorem twoParticle_eq_solQ_pairPath (a b : Fin d → ℤ) {x₁ x₂ : ℝ≥0 → Fin d → ℤ}
    (h1 : IsStepPath x₁) (h2 : IsStepPath x₂) :
    twoParticle a b x₁ x₂ = solQ a b (pairPath x₁ x₂ h1 h2) :=
  twoParticle_eq_solQ a b h1 h2 _ fun _ => rfl

theorem measurable_pairVal_gen {Ω' : Type*} {m : MeasurableSpace Ω'}
    {Z : Ω' → Fin (d + d) → ℤ} (hZ : Measurable[m] Z) :
    Measurable[m] fun ω => ((fun i : Fin d => Z ω (Fin.castAdd d i)),
      (fun i : Fin d => Z ω (Fin.natAdd d i))) :=
  (measurable_pi_iff.2 fun _i => (measurable_pi_apply _).comp hZ).prodMk
    (measurable_pi_iff.2 fun _i => (measurable_pi_apply _).comp hZ)

section

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

/-- The pair `(X₁, X₂)` as a jump-list path. -/
noncomputable def drvPairPath (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (ω : Ω) :
    CPath (PairE d) :=
  pairPath (drvX Ñ 0 ω) (drvX Ñ 1 ω) (drivers_isDrivingPath 0 ω).step
    (drivers_isDrivingPath 1 ω).step

/-- Contacts are few: the path `y = 𝔉_{a,b}(X₁, X₂)`. -/
noncomputable def drvTwo (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a b : Fin d → ℤ) (ω : Ω) :
    ℝ≥0 → Fin d → ℤ :=
  twoParticle a b (drvX Ñ 0 ω) (drvX Ñ 1 ω)

omit [MeasurableSpace Ω] in
theorem drvTwo_eq (a b : Fin d → ℤ) (ω : Ω) :
    drvTwo Ñ a b ω = solQ a b (drvPairPath Ñ ω) :=
  twoParticle_eq_solQ_pairPath a b _ _

omit [MeasurableSpace Ω] in
theorem isTwoParticle_drvTwo (a b : Fin d → ℤ) (ω : Ω) :
    IsTwoParticle a b (drvX Ñ 0 ω) (drvX Ñ 1 ω) (drvTwo Ñ a b ω) :=
  isTwoParticle_twoParticle a b (drivers_isDrivingPath 0 ω).step
    (drivers_isDrivingPath 1 ω).step

/-- Contacts are few (i): `y(t)` is `𝒢_t`-measurable, where
`𝒢_t = σ(X̄(s) : s ≤ t)`. -/
theorem drvTwo_adapted (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (a b : Fin d → ℤ) (t : ℝ≥0) :
    Measurable[natFil (drvPair Ñ) t] fun ω => drvTwo Ñ a b ω t := by
  set f := (drivers_pair_admissible h).filtration with hf
  have hY : ∀ s, Measurable[f s] fun ω => (drvPairPath Ñ ω).fn s := by
    intro s
    have h0 : Measurable[natFil (drvPair Ñ) s] fun ω => drvPair Ñ ω s :=
      measurable_natFil (drvPair Ñ) le_rfl
    have := measurable_pairVal_gen h0
    have e : (fun ω => (drvPairPath Ñ ω).fn s) = fun ω => ((fun i : Fin d => drvPair Ñ ω s (Fin.castAdd d i)),
        (fun i : Fin d => drvPair Ñ ω s (Fin.natAdd d i))) := by
      funext ω
      refine Prod.ext ?_ ?_
      · funext i; exact (Fin.append_left _ _ i).symm
      · funext i; exact (Fin.append_right _ _ i).symm
    show Measurable[natFil (drvPair Ñ) s] _
    rw [e]; exact this
  have hT := isStoppingTime_const f t
  have hm := measurable_stoppedPath (f := f) (T := fun _ => ((t : ℝ≥0) : WithTop ℝ≥0))
    (drvPairPath Ñ) hY hT
  rw [IsStoppingTime.measurableSpace_const] at hm
  have h2 := (measurable_solQ a b t).comp hm
  have e : (fun ω => drvTwo Ñ a b ω t) = (fun q : CPath (PairE d) => solQ a b q t) ∘
      fun ω => (drvPairPath Ñ ω).stop (stopReal (fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)) ω) := by
    funext ω
    rw [drvTwo_eq]
    simp only [Function.comp, stopReal, WithTop.untopD_coe]
    exact (solQ_stop a b _ t).symm
  rw [e]; exact h2

end

end ElboimSly.Paper
