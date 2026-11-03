/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenLaw
public import ElboimSly.Foundations.Cyclic.DrivenSrwShort
public import ElboimSly.Foundations.Cyclic.CycRegenCut
public import ElboimSly.Foundations.Cyclic.CycRegenAe
public import ElboimSly.Foundations.Cyclic.CycRegenLaw
public import ElboimSly.Foundations.Cyclic.LawInvariance
public import ElboimSly.Foundations.Interchange.LatticeGroup
public import ElboimSly.Foundations.Cyclic.CycWalkTraj
public import Mathlib

/-!
# The cyclic walk is an SRW up to time β (b): the cyclic walk is an SRW up to time `β`, in law

The cyclic walk is an SRW up to time β (b), first claim. Let `W_{v,q}(s) = cycWalk ν v q s` be the cyclic
walk of a Poisson environment `ν` started at `v` at cyclic time `q`, and `X` the canonical SRW.
Then `Law((W_{v,q}(s) - v)_{s ∈ [0,β]}) = Law((X(s))_{s ∈ [0,β]})` on the paths `[0,β] → ℤᵈ` with
the product `σ`-algebra (`cyc_srw_short_law`). The proof is driven and environment walks agree in law
(`cyc_driven_law`), the cyclic walk is an SRW up to time β (a) (`ae_canonical_drivenWalk_eq`), the bound
`t_reg ≥ β` (`regPlan_tau_ge`), and invariance in law (translation and start time,
`law_trajProc_lattice`, `law_trajProc_shift`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The driving path of a point process, as a `CPath`. -/
noncomputable def drivePath (N₀ : Measure (Dir d × ℝ)) : CPath (Fin d → ℤ) :=
  (drivingCycPath (walkPath_isDriving N₀)).1

theorem measurable_drivePath : Measurable (drivePath (d := d)) :=
  (CPath.measurable_iff _).2 ⟨measurable_const, fun s => measurable_walk d (s : ℝ)⟩

/-- The restriction of a path to `[0, b]`. -/
def restrictIic (b : ℝ≥0) (f : ℝ≥0 → Fin d → ℤ) : Set.Iic b → Fin d → ℤ := fun s => f s

theorem measurable_restrictIic (b : ℝ≥0) : Measurable (restrictIic (d := d) b) :=
  measurable_pi_iff.2 fun s => measurable_pi_apply s.1

theorem cycStopped_of_le (ν : Measure (RingSpace d β)) {s : ℝ≥0} (hs : s ≤ β.toNNReal) :
    cycStopped ν s = ElboimSly.cycWalk ν 0 0 (s : ℝ) := by
  have h : (s : ℝ≥0∞) ≤ ElboimSly.cycTreg ν :=
    (ENNReal.coe_le_coe.2 hs).trans (regPlan_tau_ge ν)
  unfold cycStopped
  rw [min_eq_left h, ENNReal.toNNReal_coe]

theorem cycWalk_eq_trajProc {ν : Measure (RingSpace d β)} (hν : Good ν) (u : Fin d → ℤ) (q : ℝ)
    (s : ℝ≥0) : ElboimSly.cycWalk ν u q (s : ℝ) = trajProc ν u q s := by
  rw [cycWalk_of_nonneg hν u q (NNReal.coe_nonneg s), trajProc_of_good hν]
  simp [fwdTraj, fwdReal]

/-- A measurable representative of `ν ↦ (t_reg, W(· ∧ t_reg))`: the first world-line of the
environment final record of `𝒫₁`. -/
noncomputable def cycPairM (ν : Measure (RingSpace d β)) : ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) :=
  firstPiece (regionPlan d β).junk
    ((regionPlan d β).envFinalOr CycRec.empty (ν.map (Prod.mk ())))

theorem measurable_cycPairM : Measurable (cycPairM (d := d) (β := β)) :=
  (measurable_firstPiece _).comp (((regionPlan d β).measurable_envFinalOr _).comp
    (measurable_map_measure measurable_prodMk_left))

theorem cycPairM_eq {ν : Measure (RingSpace d β)} (hν : Good ν) : cycPairM ν = cycPair ν := by
  unfold cycPairM
  rw [(regionPlan d β).envFinalOr_of_good _ (cycGood_map_unit hν),
    firstPiece_envFinal (by rw [cycSlice_map_unit]; exact hν), cycSlice_map_unit]
  rfl

theorem measurable_drivenPair_drivePath {b : ℝ≥0} (hb : 0 < b) :
    Measurable fun N₀ : Measure (Dir d × ℝ) => drivenPair b (drivePath N₀).fn :=
  ((measurable_drivenTreg hb).comp measurable_drivePath).prodMk
    (measurable_pi_iff.2 fun s => (measurable_drivenStopped hb s).comp measurable_drivePath)

/-- `Law(W|_{[0,β]}) = Law(X|_{[0,β]})` for the cyclic walk from `(0, 0)`. -/
theorem law_short_core {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pe : Measure Ω} {Pd : Measure Ω'} {ν : Ω → Measure (RingSpace d β)}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe)
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) :
    Pe.map (fun ω => restrictIic β.toNNReal (fun s : ℝ≥0 => ElboimSly.cycWalk (ν ω) 0 0 (s : ℝ))) =
      Pd.map (fun ω => restrictIic β.toNNReal (canonical d N₀ ω)) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have hlaw := cyc_driven_law hν hN₀
  have hfd : Measurable fun ω => drivenPair β.toNNReal (canonical d N₀ ω) :=
    (measurable_drivenPair_drivePath hb).comp hN₀.measurable
  have hfe : Measurable fun ω => cycPairM (ν ω) := measurable_cycPairM.comp hν.measurable
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := Interchange.ae_good hν
  have h1 : Pe.map (fun ω => cycPair (ν ω)) = Pe.map (fun ω => cycPairM (ν ω)) := by
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    exact (cycPairM_eq hω).symm
  rw [h1] at hlaw
  have hR : Measurable fun p : ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) => restrictIic β.toNNReal p.2 :=
    (measurable_restrictIic _).comp measurable_snd
  have h2 := congrArg (fun m => m.map fun p : ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) =>
    restrictIic β.toNNReal p.2) hlaw
  rw [Measure.map_map hR hfd, Measure.map_map hR hfe] at h2
  have hE : ∀ᵐ ω ∂Pe, restrictIic β.toNNReal (fun s : ℝ≥0 => ElboimSly.cycWalk (ν ω) 0 0 (s : ℝ)) =
      (fun p : ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) => restrictIic β.toNNReal p.2) (cycPairM (ν ω)) := by
    filter_upwards [hgood] with ω hω
    funext s
    show ElboimSly.cycWalk (ν ω) 0 0 (s.1 : ℝ) = (cycPairM (ν ω)).2 s.1
    rw [cycPairM_eq hω]
    exact (cycStopped_of_le _ s.2).symm
  have hD : ∀ᵐ ω ∂Pd,
      (fun p : ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) => restrictIic β.toNNReal p.2)
        (drivenPair β.toNNReal (canonical d N₀ ω)) =
        restrictIic β.toNNReal (canonical d N₀ ω) := by
    filter_upwards [ae_canonical_drivenWalk_eq hN₀ β.toNNReal hb] with ω hω
    obtain ⟨ht, hx⟩ := hω
    funext s
    show drivenStopped β.toNNReal (canonical d N₀ ω) s.1 = canonical d N₀ ω s.1
    unfold drivenStopped
    rw [min_eq_left ((ENNReal.coe_le_coe.2 s.2).trans ht), ENNReal.toNNReal_coe]
    exact hx s.1 s.2
  exact (Measure.map_congr hE).trans (h2.symm.trans (Measure.map_congr hD))

/-- Invariance in law for the cyclic walk: the law of `(W_{v,q}(s) - v)_{s ∈ [0,b]}` does
not depend on `(v, q)`. -/
theorem law_cycWalk_invariant {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
    {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (b : ℝ≥0) (v : Fin d → ℤ) (q : ℝ) :
    Pe.map (fun ω => restrictIic b (fun s : ℝ≥0 => ElboimSly.cycWalk (ν ω) v q (s : ℝ) - v)) =
      Pe.map (fun ω => restrictIic b (fun s : ℝ≥0 => ElboimSly.cycWalk (ν ω) 0 0 (s : ℝ))) := by
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := Interchange.ae_good hν
  have hF : ∀ (x : Fin d → ℤ) (a : ℝ), Measurable fun ω (_ : Unit) => trajProc (ν ω) x a :=
    fun x a => measurable_pi_iff.2 fun _ => (measurable_trajProc x a).comp hν.measurable
  have hshift := law_trajProc_shift hν q (fun _ : Unit => v) (fun _ => 0)
  have hlat := law_trajProc_lattice hν (LatticeAut.translate v) (fun _ : Unit => 0) (fun _ => 0)
  let Ψ : (Unit → ℝ≥0 → Fin d → ℤ) → Set.Iic b → Fin d → ℤ := fun f s => f () s.1 - v
  have hΨ : Measurable Ψ := measurable_pi_iff.2 fun s => by
    show Measurable fun f : (Unit → ℝ≥0 → Fin d → ℤ) => f () s.1 - v
    exact (measurable_of_countable (fun x : Fin d → ℤ => x - v)).comp
      ((measurable_pi_apply s.1).comp (measurable_pi_apply ()))
  let Θ : (Unit → ℝ≥0 → Fin d → ℤ) → Unit → ℝ≥0 → Fin d → ℤ := fun f k s => f k s + v
  have hΘ : Measurable Θ := measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun s => by
    show Measurable fun f : (Unit → ℝ≥0 → Fin d → ℤ) => f k s + v
    exact (measurable_of_countable (fun x : Fin d → ℤ => x + v)).comp
      ((measurable_pi_apply s).comp (measurable_pi_apply k))
  have e1 : Pe.map (fun ω (_ : Unit) => trajProc (ν ω) v q) =
      Pe.map (fun ω (_ : Unit) => trajProc (ν ω) v 0) := by
    simpa using hshift
  have e2' : Pe.map (fun ω (_ : Unit) => trajProc (ν ω) v 0) =
      Pe.map (fun ω (_ : Unit) (s : ℝ≥0) => trajProc (ν ω) 0 0 s + v) := by
    simpa [LatticeAut.translate] using hlat
  have e2 : Pe.map (fun ω (_ : Unit) => trajProc (ν ω) v 0) =
      Pe.map (Θ ∘ fun ω (_ : Unit) => trajProc (ν ω) 0 0) := e2'
  have e3 := congrArg (fun m => m.map Ψ) (e1.trans e2)
  rw [Measure.map_map hΨ (hF v q), Measure.map_map hΨ ((hΘ.comp (hF 0 0)))] at e3
  have hL : ∀ᵐ ω ∂Pe, restrictIic b (fun s : ℝ≥0 => ElboimSly.cycWalk (ν ω) v q (s : ℝ) - v) =
      (Ψ ∘ fun ω (_ : Unit) => trajProc (ν ω) v q) ω := by
    filter_upwards [hgood] with ω hω
    funext s
    show ElboimSly.cycWalk (ν ω) v q (s.1 : ℝ) - v = trajProc (ν ω) v q s.1 - v
    rw [cycWalk_eq_trajProc hω]
  have hR : ∀ᵐ ω ∂Pe, (Ψ ∘ Θ ∘ fun ω (_ : Unit) => trajProc (ν ω) 0 0) ω =
      restrictIic b (fun s : ℝ≥0 => ElboimSly.cycWalk (ν ω) 0 0 (s : ℝ)) := by
    filter_upwards [hgood] with ω hω
    funext s
    show trajProc (ν ω) 0 0 s.1 + v - v = ElboimSly.cycWalk (ν ω) 0 0 (s.1 : ℝ)
    rw [cycWalk_eq_trajProc hω, add_sub_cancel_right]
  exact (Measure.map_congr hL).trans (e3.trans (Measure.map_congr hR))

/-- **the cyclic walk is an SRW up to time β (b)**, first claim: for all `v ∈ ℤᵈ` and `q ∈ ℝ`,
`Law((W_{v,q}(s) - v)_{s ∈ [0,β]}) = Law((X(s))_{s ∈ [0,β]})`. -/
theorem cyc_srw_short_law {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pe : Measure Ω} {Pd : Measure Ω'} {ν : Ω → Measure (RingSpace d β)}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe)
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) (v : Fin d → ℤ) (q : ℝ) :
    Pe.map (fun ω => restrictIic β.toNNReal
        (fun s : ℝ≥0 => ElboimSly.cycWalk (ν ω) v q (s : ℝ) - v)) =
      Pd.map (fun ω => restrictIic β.toNNReal (canonical d N₀ ω)) :=
  (law_cycWalk_invariant hν _ v q).trans (law_short_core hν hN₀)

end ElboimSly.Cyclic

end
