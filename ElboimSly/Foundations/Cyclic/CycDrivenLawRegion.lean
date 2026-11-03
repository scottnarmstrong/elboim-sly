/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenLawFirst
public import ElboimSly.Foundations.Cyclic.CycDrivenRegion
public import ElboimSly.Foundations.Cyclic.CycRegenEnv
public import ElboimSly.Foundations.Cyclic.CycRegenAe
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvSrw
public import Mathlib

/-!
# The first world-line of the final records of `𝒫₁`

Driven and environment walks agree in law (proof, first paragraph). For the plan `𝒫₁ = regionPlan` of
The driven walk is a driven world-line:

* `firstPiece_envFinal`: the first world-line of the environment final record is
  `(t_reg, W(· ∧ t_reg))` for a good environment (`cycStopped`);
* `firstPiece_drivenFinal`: the first world-line of the driven final record, driven by the
  coincidence-free paths `x = (X_j)`, is `(t_reg^x, w^x(· ∧ t_reg^x))` (`drivenStopped`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The stopped cyclic walk `W(s ∧ t_reg)`, with `W(s ∧ ∞) = W(s)`. -/
noncomputable def cycStopped (ν : Measure (RingSpace d β)) (s : ℝ≥0) : Fin d → ℤ :=
  ElboimSly.cycWalk ν 0 0 (((min (s : ℝ≥0∞) (ElboimSly.cycTreg ν)).toNNReal : ℝ≥0) : ℝ)

omit [Fact (0 < β)] in
theorem envMeasure_regionData' {I : Type*} [MeasurableSpace I] (ν : Measure (I × RingSpace d β))
    (ι : I) : envMeasure ν (regionData d ι) = cycSlice ι ν := by
  simp [envMeasure, regionData, CycData.fwd, CycData.copy]

omit [Fact (0 < β)] in
theorem envFn_regionData' {I : Type*} [MeasurableSpace I] (ν : Measure (I × RingSpace d β))
    (ι : I) (s : ℝ≥0) :
    envFn ν (regionData d ι) s = ElboimSly.cycWalk (cycSlice ι ν) 0 0 (s : ℝ) := by
  unfold envFn ElboimSly.cycWalk
  have h0 : (0 : ℝ) ≤ s := s.2
  simp only [h0, ↓reduceIte]
  rw [envMeasure_regionData', Real.toNNReal_coe]
  simp [regionData, CycData.start, CycData.sgn, CycData.phase, CycData.fwd]

/-- The first world-line of the environment final record of `𝒫₁` for a good environment. -/
theorem firstPiece_envFinal {N : Measure (Unit × RingSpace d β)} (hN : Good (cycSlice () N)) :
    firstPiece (regionPlan d β).junk ((regionPlan d β).envFinal N) =
      (ElboimSly.cycTreg (cycSlice () N), fun s => cycStopped (cycSlice () N) s) := by
  set P := regionPlan d β with hP
  have hlen := envPath_len (δ := regionData d ()) (ν := N) hN
  have hfn : (envPath N (regionData d ())).1.fn =
      fun s : ℝ≥0 => ElboimSly.cycWalk (cycSlice () N) 0 0 (s : ℝ) :=
    hlen.2.trans (funext fun s => envFn_regionData' N () s)
  have hstop : ∀ ρ : CycRecN Unit d 0, P.stopLen 0 ρ (envPath N (regionData d ())) =
      ElboimSly.cycTreg (cycSlice () N) := fun ρ => by
    show (closingPlan β 1 _ _).stopLen _ _ _ = _
    rw [closingPlan_stopLen, hfn]
    exact pathTreg_cycWalk _
  have hK : 0 < P.K := by
    show (0 : ℕ∞) < 1
    norm_num
  have h := P.coord_cycFinal_zero (fun k ρ => envPath N (P.start k ρ)) hK
  unfold firstPiece CycPlan.envFinal
  rw [h]
  refine Prod.ext ?_ ?_
  · show ((envPath N (regionData d ())).cut
      (P.stopLen 0 Fin.elim0 (envPath N (regionData d ())))).1.len = _
    rw [hstop Fin.elim0]
    simp [CycPath.cut]
  · funext s
    show ((envPath N (regionData d ())).cut
      (P.stopLen 0 Fin.elim0 (envPath N (regionData d ())))).1.fn s = _
    rw [hstop Fin.elim0]
    show ((envPath N (regionData d ())).1.cut _).fn s = _
    rw [CPath.cut_fn, hfn]
    rfl

/-- The first world-line of the driven final record of `𝒫₁`, driven by the sub-process `Ñ^{}`,
when its canonical walk is coincidence-free. -/
theorem firstPiece_drivenFinal {Ñ : Measure ((SRW.Dir d × Unit) × ℝ)}
    (hx : (srwPath Ñ ()).1.fn ∈ CycCF β.toNNReal) :
    firstPiece (regionPlan d β).junk ((regionPlan d β).drivenFinal (J := Unit)
        (fun _ _ => ()) (fun j => srwPath Ñ j)) =
      (drivenTreg β.toNNReal (srwPath Ñ ()).1.fn,
        fun s => drivenStopped β.toNNReal (srwPath Ñ ()).1.fn s) := by
  set P := regionPlan d β with hP
  have hK : 0 < P.K := by
    show (0 : ℕ∞) < 1
    norm_num
  have hoff : drvOffset (I := Unit) (d := d) (fun _ _ => ()) (Fin.elim0 : CycRecN Unit d 0) () = 0 := by
    simp [drvOffset]
  have hreg := cyc_driven_region hx (srwPath Ñ ()).1 rfl (Fin.elim0 : CycRecN Unit d 0)
  obtain ⟨hst, hag⟩ := hreg
  set p := drivenPath β (CycRec.region β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩))
    (CycRec.ringSet β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩)) (regionData d ())
    (srwPath Ñ ()).1 0 with hp
  have h := P.coord_cycFinal_zero (fun k ρ => drivenPath β (CycRec.region β (Sum.inl ⟨k, ρ⟩))
    (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩)) (P.start k ρ) ((srwPath Ñ ((fun _ _ => ()) k ρ)).1)
    (drvOffset (fun _ _ => ()) ρ ((fun _ _ => ()) k ρ))) hK
  unfold firstPiece CycPlan.drivenFinal
  rw [h]
  have hent : P.nextEntry (fun k ρ => drivenPath β (CycRec.region β (Sum.inl ⟨k, ρ⟩))
    (CycRec.ringSet β (Sum.inl ⟨k, ρ⟩)) (P.start k ρ) ((srwPath Ñ ((fun _ _ => ()) k ρ)).1)
    (drvOffset (fun _ _ => ()) ρ ((fun _ _ => ()) k ρ))) 0 Fin.elim0 =
      (regionData d (), p.cut (drivenTreg β.toNNReal (srwPath Ñ ()).1.fn)) := by
    have hpath : drivenPath β (CycRec.region β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩))
        (CycRec.ringSet β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩)) (regionData d ())
        ((srwPath Ñ ()).1)
        (drvOffset (fun _ _ => ()) (Fin.elim0 : CycRecN Unit d 0)
          ((fun _ _ => ()) 0 (Fin.elim0 : CycRecN Unit d 0))) = p := by
      rw [hp]; congr 1
    show (regionData d (), (drivenPath β (CycRec.region β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩))
        (CycRec.ringSet β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩)) (regionData d ())
        ((srwPath Ñ ()).1)
        (drvOffset (fun _ _ => ()) (Fin.elim0 : CycRecN Unit d 0)
          ((fun _ _ => ()) 0 (Fin.elim0 : CycRecN Unit d 0)))).cut
        (P.stopLen 0 (Fin.elim0 : CycRecN Unit d 0) (drivenPath β (CycRec.region β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩))
        (CycRec.ringSet β (Sum.inl ⟨0, (Fin.elim0 : CycRecN Unit d 0)⟩)) (regionData d ())
        ((srwPath Ñ ()).1)
        (drvOffset (fun _ _ => ()) (Fin.elim0 : CycRecN Unit d 0)
          ((fun _ _ => ()) 0 (Fin.elim0 : CycRecN Unit d 0)))))) = _
    rw [hpath, hst]
  rw [hent]
  refine Prod.ext ?_ ?_
  · simp [CycPath.cut, CycEntry.len]
  · funext s
    show (p.1.cut (drivenTreg β.toNNReal (srwPath Ñ ()).1.fn)).fn s = _
    rw [CPath.cut_fn]
    refine hag _ ?_
    have hs : (min (s : ℝ≥0∞) (drivenTreg β.toNNReal (srwPath Ñ ()).1.fn)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    rw [ENNReal.coe_toNNReal hs]
    exact min_le_right _ _

end ElboimSly.Cyclic

end
