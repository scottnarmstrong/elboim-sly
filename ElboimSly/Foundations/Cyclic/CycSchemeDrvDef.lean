/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeMeas3
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import ElboimSly.Foundations.SRW.Iid
public import Mathlib

/-!
# The driving scheme, data of the raw probe

The driving scheme.

The driving space is `(Dir d × J) × ℝ` with the intensity `clockIntensity (Dir d × J)`
(`# ⊗ Leb|_{(0,∞)}`); this is the carrier of independent families (`SRW.subProcess`), and is the
written proof's `𝒮' = J × 𝒟 × ℝ` up to the associativity of the product. `Dir d` is the written proof's `𝒟`.

For a state `st = (ρ, ε)` of the environment scheme with `ρ = (f_0, …, f_n)` (the last entry is the
current walk `k = n`), `drvIdx` is `j_k = 𝖩_k(f_0, …, f_{n-1})` and `drvOff` is the driving offset
`a_k`. The raw probe `drvProbeR` is the written proof's `R'_j`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-! ### The edge `{w, w + v}` -/

theorem latticeAdj_step (w : Fin d → ℤ) (v : Dir d) : LatticeAdj d w (w + v.vec) := by
  unfold LatticeAdj Dir.vec
  have : ∀ i, |w i - (w + (Pi.single v.1 (if v.2 then (1 : ℤ) else -1) : Fin d → ℤ)) i| =
      |(Pi.single v.1 (if v.2 then (1 : ℤ) else -1) : Fin d → ℤ) i| := by
    intro i; simp
  simp_rw [this]
  rw [Finset.sum_eq_single v.1]
  · simp only [Pi.single_eq_same]; split_ifs <;> simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

/-- The edge `{w, w + v}` of `Z^d`. -/
def stepEdge (w : Fin d → ℤ) (v : Dir d) : Edge d := Edge.mk' w (w + v.vec) (latticeAdj_step w v)

theorem mem_stepEdge (w : Fin d → ℤ) (v : Dir d) : Edge.Mem w (stepEdge w v) := by
  unfold Edge.Mem stepEdge Edge.mk'
  simp


/-! ### The driving data of a state -/

/-- The driving space `(Dir d × J) × ℝ`. -/
abbrev DrvS (d : ℕ) (J : Type*) : Type _ := (Dir d × J) × ℝ

/-- The driving intensity `# ⊗ Leb|_{(0,∞)}`. -/
noncomputable def drvIntensity (d : ℕ) (J : Type*) [MeasurableSpace J] : Measure (DrvS d J) :=
  clockIntensity (Dir d × J)

instance sigmaFinite_drvIntensity (d : ℕ) (J : Type*) [MeasurableSpace J] [Countable J]
    [MeasurableSingletonClass J] : SigmaFinite (drvIntensity d J) :=
  sigmaFinite_clockIntensity (Dir d × J)

section Drv

variable {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (j0 : J)

/-- `j_k = 𝖩_k` of the completed part of the record (`j0` for the junk states). -/
def drvIdx (st : CycScheme.State I d) : J :=
  match st.1 with
  | Sum.inl ⟨n + 1, f⟩ => jx n (fun m => f m.castSucc)
  | _ => j0

/-- The driving offset `a_k` of the current walk (`0` for the junk states). -/
noncomputable def drvOff (st : CycScheme.State I d) : ℝ≥0 :=
  match st.1 with
  | Sum.inl ⟨n + 1, f⟩ => drvOffset jx (fun m : Fin n => f m.castSucc) (jx n (fun m => f m.castSucc))
  | _ => 0

variable (P : CycPlan I d β) (sc : ℝ≥0∞)

/-- The driving time `a_k + r` at which the current walk stands. -/
noncomputable def drvT (st : CycScheme.State I d) : ℝ :=
  (drvOff jx st : ℝ) + ((CycScheme.cur P st).time : ℝ)

/-- The set `A = {(v, j_k) : v ∈ 𝒟}` of the segment probe (empty if ended). -/
noncomputable def drvA (st : CycScheme.State I d) : Finset (Dir d × J) :=
  open scoped Classical in
  if st.2 then ∅ else Finset.univ.image fun v : Dir d => (v, drvIdx jx j0 st)

/-- The environment point `φ(e, y) = (ι, {w, w + v}, c_δ(y - a_k))` attached to a driving point. -/
noncomputable def drvPhi (st : CycScheme.State I d) (p : DrvS d J) : CycS I d β :=
  ((CycScheme.cur P st).data.copy,
    (stepEdge (CycScheme.cur P st).pos p.1.1,
      (CycScheme.cur P st).data.clock β (p.2 - (drvOff jx st : ℝ)).toNNReal))

/-- The mask `Z^pull`: driving points whose environment image is already explored. -/
def drvMask (st : CycScheme.State I d) : Set ((Dir d × J) × ℝ) :=
  {p | drvPhi (β := β) jx P st p ∈ st.1.region β}

open scoped Classical in
/-- The raw probe `R'_j` of the driving scheme (The driving scheme). -/
noncomputable def drvProbeR (st : CycScheme.State I d) (p : DrvS d J) : ℝ≥0∞ :=
  if st.2 = false ∧ p.1.2 = drvIdx jx j0 st ∧ 0 < p.2 - drvT jx P st ∧
      p.2 - drvT jx P st ≤ (CycScheme.hOf P sc st : ℝ) ∧ drvPhi (β := β) jx P st p ∉ st.1.region β
  then ENNReal.ofReal (p.2 - drvT jx P st) else ⊤

end Drv

end ElboimSly.Cyclic

end
