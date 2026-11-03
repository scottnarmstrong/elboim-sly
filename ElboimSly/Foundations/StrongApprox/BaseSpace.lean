/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseLaws
public import ElboimSly.Foundations.StrongApprox.BaseCells
public import ElboimSly.Foundations.Brownian.Bridge
public import Mathlib

/-!
# The probability space of the base coupling

ES22 (8.3): base coupling with precision n^10 ("The probability space", (F1)-(F4)).

For `N ≥ 1` and a coupling `μN` of `Poisson(1)^{⊗N}` and `N(0,1)^{⊗N}`, the space is
`Ω' = ((SA × SB) × (SC × SX)) × SH` where
* `SA = Dir d → ℝ^N × ℝ^N` with `μN^{⊗Dir d}` (F1),
* `SB` carries the points `Y_{k,i}`, `k ∈ 𝒦_N`, (F2),
* `SC` carries the blocks `(K_k, (Y_{k,i})_i)`, `k ∈ 𝒦` (the factor (F3), taken over all of `𝒦`;
  only the blocks with `k ∉ 𝒦_N` are used),
* `SX × SH` carries `(X_m)` and `(η_β)` (F4).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

variable (d N : ℕ)

/-- The index set `𝒦_N = D × {1,…,N}` (with `l = m + 1`). -/
abbrev JIdx : Type := Dir d × Fin N

/-- The injection `(v, m) ↦ (v, m + 1)` of `𝒦_N` into `𝒦`. -/
def jcell : JIdx d N → CellIdx d := fun a => (a.1, ((a.2 : ℕ) : ℤ) + 1)

theorem jcell_injective : Function.Injective (jcell d N) := by
  rintro ⟨v, m⟩ ⟨v', m'⟩ h
  simp only [jcell, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have : (m : ℕ) = m' := by omega
  rw [Fin.ext this]

/-- The block space `ℕ × S^ℕ`. -/
abbrev BlockSp : Type := ℕ × (ℕ → Dir d × ℝ)

/-- `SA`: the factor (F1). -/
abbrev SA : Type := Dir d → (Fin N → ℝ) × (Fin N → ℝ)
/-- `SB`: the factor (F2). -/
abbrev SB : Type := JIdx d N → ℕ → Dir d × ℝ
/-- `SC`: the factor (F3). -/
abbrev SC : Type := CellIdx d → BlockSp d
/-- `SX`: the Gaussian vectors `X_m`. -/
abbrev SX : Type := ℕ → Fin d → ℝ
/-- `SH`: the Gaussian bridge variables `η_β`. -/
abbrev SH : Type := Brownian.BridgeIdx d → ℝ

/-- The main part of the sample space. -/
abbrev OmMain : Type := ((SA d N × SB d N) × (SC d × SX d))
/-- The whole sample space. -/
abbrev OmBase : Type := OmMain d N × SH d

/-- The law of `SA`. -/
noncomputable def PA (μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))) : Measure (SA d N) :=
  Measure.pi fun _ : Dir d => μN

/-- The law of `SB`. -/
noncomputable def PBpts : Measure (SB d N) :=
  Measure.pi fun a : JIdx d N => Measure.infinitePi fun _ : ℕ => cellLaw d (jcell d N a)

/-- The law of `SC`. -/
noncomputable def PC : Measure (SC d) :=
  Measure.infinitePi fun k : CellIdx d => blockMeasure (cellLaw d k) (cellMass d k)

/-- The law of `SX`. -/
noncomputable def PX : Measure (SX d) :=
  Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin d => gaussianReal 0 1

/-- The law of `SH`. -/
noncomputable def PH : Measure (SH d) :=
  Measure.infinitePi fun _ : Brownian.BridgeIdx d => gaussianReal 0 1

/-- The law of the main part. -/
noncomputable def PMain (μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))) : Measure (OmMain d N) :=
  ((PA d N μN).prod (PBpts d N)).prod ((PC d).prod (PX d))

/-- The law of the whole space. -/
noncomputable def PBase (μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))) : Measure (OmBase d N) :=
  (PMain d N μN).prod (PH d)

instance (μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))) [IsProbabilityMeasure μN] :
    IsProbabilityMeasure (PA d N μN) := by unfold PA; infer_instance

instance : IsProbabilityMeasure (PBpts d N) := by unfold PBpts; infer_instance
instance : IsProbabilityMeasure (PC d) := by unfold PC; infer_instance
instance : IsProbabilityMeasure (PX d) := by unfold PX; infer_instance
instance : IsProbabilityMeasure (PH d) := by unfold PH; infer_instance

instance (μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))) [IsProbabilityMeasure μN] :
    IsProbabilityMeasure (PMain d N μN) := by unfold PMain; infer_instance

instance (μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))) [IsProbabilityMeasure μN] :
    IsProbabilityMeasure (PBase d N μN) := by unfold PBase; infer_instance

/-- The integer count `K = ⌊max ξ 0⌋` read off the coupling coordinate. -/
noncomputable def kapOf (a : SA d N) (p : JIdx d N) : ℕ := ⌊max ((a p.1).1 p.2) 0⌋₊

/-- The coupling coordinates `ξ^v_l`. -/
def xiOf (a : SA d N) (p : JIdx d N) : ℝ := (a p.1).1 p.2

/-- The coupling coordinates `z^v_l`. -/
def zOf (a : SA d N) (p : JIdx d N) : ℝ := (a p.1).2 p.2

/-- The vectors `Z_l = ((z^{e_i}_l - z^{-e_i}_l)/√2)_i`, for `l = m + 1`. -/
noncomputable def zdiff (a : SA d N) (m : Fin N) (i : Fin d) : ℝ :=
  (zOf d N a ((i, true), m) - zOf d N a ((i, false), m)) / √2

/-- The block seen by the cell `(v, m+1)`, `m < N`: `(⌊ξ⌋, (Y_{k,i})_i)`. -/
noncomputable def zk (p : SA d N × SB d N) (a : JIdx d N) : BlockSp d :=
  (kapOf d N p.1 a, p.2 a)

/-- The blocks of the base coupling: the blocks of `SC`, with those of `𝒦_N` overridden. -/
noncomputable def blocks (ω : OmMain d N) : CellIdx d → BlockSp d :=
  overrideAt (jcell d N) (zk d N ω.1) ω.2.1

/-- `K_k`. -/
noncomputable def Kc (ω : OmMain d N) (k : CellIdx d) : ℕ := (blocks d N ω k).1

/-- `Y_{k,i}`. -/
noncomputable def Yc (ω : OmMain d N) (k : CellIdx d) (i : ℕ) : Dir d × ℝ := (blocks d N ω k).2 i

/-- The process `N'`. -/
noncomputable def Nproc (ω : OmMain d N) : Measure (Dir d × ℝ) :=
  cellProc (cellSet d) (fun k ω => Kc d N ω k) (fun k i ω => Yc d N ω k i) ω

/-- The Gaussian increments `X_m`: `Z_{m+1}` for `m < N`, the coordinates of `SX` otherwise. -/
noncomputable def Xfam (ω : OmMain d N) : ℕ → Fin d → ℝ :=
  overrideAt (fun m : Fin N => (m : ℕ)) (zdiff d N ω.1.1) ω.2.2

/-! ### Measurability -/

variable {d N}

theorem measurable_kapOf : Measurable (kapOf d N) := by
  refine measurable_pi_iff.2 fun p => ?_
  have : Measurable fun a : SA d N => (a p.1).1 p.2 :=
    (measurable_pi_apply p.2).comp (measurable_fst.comp (measurable_pi_apply p.1))
  exact (Nat.measurable_floor).comp (this.max measurable_const)

theorem measurable_zdiff : Measurable (zdiff d N) := by
  refine measurable_pi_iff.2 fun m => measurable_pi_iff.2 fun i => ?_
  have h : ∀ v, Measurable fun a : SA d N => zOf d N a (v, m) := fun v =>
    (measurable_pi_apply m).comp (measurable_snd.comp (measurable_pi_apply v))
  show Measurable fun a : SA d N => (zOf d N a ((i, true), m) - zOf d N a ((i, false), m)) / √2
  exact ((h (i, true)).sub (h (i, false))).div_const _

theorem measurable_zk : Measurable (zk d N) := by
  refine measurable_pi_iff.2 fun a => ?_
  exact ((measurable_pi_apply a).comp (measurable_kapOf.comp measurable_fst)).prodMk
    ((measurable_pi_apply a).comp measurable_snd)

theorem measurable_blocks : Measurable (blocks d N) := by
  have := (measurable_overrideAt (X := BlockSp d) (J := JIdx d N) (jcell_injective d N))
  exact this.comp ((measurable_zk.comp (measurable_fst.comp measurable_id)).prodMk
    (measurable_fst.comp measurable_snd))

theorem measurable_Xfam : Measurable (Xfam d N) := by
  have := (measurable_overrideAt (X := Fin d → ℝ) (J := Fin N)
    (j := fun m : Fin N => (m : ℕ)) Fin.val_injective)
  exact this.comp (((measurable_zdiff.comp (measurable_fst.comp measurable_fst))).prodMk
    (measurable_snd.comp measurable_snd))

end StrongApprox
end ElboimSly
