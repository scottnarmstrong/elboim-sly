/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.DriversPair
public import ElboimSly.Paper.Base.DriversPath
public import ElboimSly.Foundations.SRW.Stopping
public import Mathlib

/-!
# The pair of driving walks

The pair of driving walks (supplement, ES22 §8).

Let `Ñ` be a PPP on `(D × {0, 1}) × ℝ` with intensity `# ⊗ Leb|_{(0,∞)}` (the copies `{1, 2}` of
the written proof are indexed by `Fin 2`), `N^j` its restrictions, `X_j` the canonical SRWs built
from `N^j`, and `X̄ = (X₀, X₁)` with values in `ℤ^{d+d}`.

* `drivers_indep`, `drivers_isSRW`: `X₀, X₁` are independent SRWs. (i)
* `drivers_pair_isSRW`, `drivers_pair_ae_eq`: `X̄` is an SRW in dimension `d + d`, a.s. equal to
  the canonical SRW built from `Ñ` relabelled to `D_{2d}`; its natural filtration `𝒢_t` is
  admissible, so the results for general SRWs (stopping times, strong Markov, freezing) apply
  to `X̄` with `(𝒢_t)`.  (i)
* `drivers_admissible`: `ℱ^{(j)}_t = σ(X_{1-j}) ∨ σ(X_j(s) : s ≤ t)` is admissible for `X_j`. (ii)
* `drivers_ae_good`, `drivers_isDrivingPath`, `drivers_no_common_jump`,
  `drivers_ncard_jumps_le`: (iii).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Paper.Base

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The canonical SRW `X_j` built from the `j`-th restriction `N^j` of `Ñ`. -/
noncomputable def drvX (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (j : Fin 2) : Ω → PathSpace d :=
  canonical d (subProcess Ñ j)

/-- `X̄ = (X₀, X₁)` as a process with values in `ℤ^{d+d}`. -/
noncomputable def drvPair (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) : Ω → PathSpace (d + d) :=
  fun ω t => Fin.append (drvX Ñ 0 ω t) (drvX Ñ 1 ω t)

/-- `Ñ` viewed as a point process on `D_{2d} × ℝ`. -/
noncomputable def drvPoint (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) : Ω → Measure (Dir (d + d) × ℝ) :=
  fun ω => relabel univ (dirMap d) (Ñ ω)

/-- The filtration `ℱ^{(j)}_t = σ(X_{1-j}) ∨ σ(X_j(s) : s ≤ t)`. -/
@[instance_reducible] noncomputable def drvFil (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (j : Fin 2) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (drvX Ñ (1 - j)) inferInstance ⊔ natFil (drvX Ñ j) t

/-- The event `Ḡ`: the good events of `N⁰`, `N¹` and `Ñ` (on `D_{2d}`). -/
def drvGood (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) : Set Ω :=
  {ω | subProcess Ñ 0 ω ∈ goodSet d ∧ subProcess Ñ 1 ω ∈ goodSet d ∧
    drvPoint Ñ ω ∈ goodSet (d + d)}

variable {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

theorem drvPoint_ppp (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) :
    IsPoissonPointProcess (drvPoint Ñ) (clockIntensity (Dir (d + d))) P := by
  refine relabel_ppp h MeasurableSet.univ ?_ ?_
  · intro a _ b _ hab; exact (dirMap_bijective d).1 hab
  · intro b; obtain ⟨a, ha⟩ := (dirMap_bijective d).2 b; exact ⟨a, mem_univ _, ha⟩

/-- (i): `X₀, X₁` are independent. -/
theorem drivers_indep (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) :
    iIndepFun (fun j => drvX Ñ j) P :=
  iIndepFun_canonical_subProcess h

/-- (i): each `X_j` is an SRW. -/
theorem drivers_isSRW (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (j : Fin 2) : IsSRW P (drvX Ñ j) :=
  isSRW_subProcess h j

/-- (iii): `P(Ḡ) = 1`. -/
theorem drivers_ae_good (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) :
    ∀ᵐ ω ∂P, ω ∈ drvGood Ñ := by
  filter_upwards [ae_good (subProcess_ppp h 0), ae_good (subProcess_ppp h 1),
    ae_good (drvPoint_ppp h)] with ω h0 h1 h2 using ⟨h0, h1, h2⟩

omit [MeasurableSpace Ω] in
/-- (i): on `Ḡ`, `X̄` is the canonical SRW in dimension `d + d` built from `Ñ`. -/
theorem drivers_pair_eq (ω : Ω) (hω : ω ∈ drvGood Ñ) :
    drvPair Ñ ω = canonical (d + d) (drvPoint Ñ) ω := by
  funext t
  exact (walk_relabel_pair (Ñ ω) hω.2.2 hω.1 hω.2.1 (t : ℝ)).symm

/-- (i): `X̄ = (X₀, X₁)` is almost surely the canonical SRW in dimension `d + d` built from `Ñ`
(viewed as a PPP on `D_{2d} × ℝ`). -/
theorem drivers_pair_ae_eq (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) :
    ∀ᵐ ω ∂P, drvPair Ñ ω = canonical (d + d) (drvPoint Ñ) ω :=
  (drivers_ae_good h).mono fun ω hω => drivers_pair_eq ω hω

theorem measurable_drvX (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (j : Fin 2) : Measurable (drvX Ñ j) :=
  (drivers_isSRW h j).1

theorem measurable_drvPair (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) :
    Measurable (drvPair Ñ) := by
  refine measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun i => ?_
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · have h0 : Measurable fun ω => drvX Ñ 0 ω t k :=
      (measurable_pi_apply k).comp ((measurable_pi_apply t).comp (measurable_drvX h 0))
    convert h0 using 1
    funext ω
    exact Fin.append_left _ _ k
  · have h1 : Measurable fun ω => drvX Ñ 1 ω t k :=
      (measurable_pi_apply k).comp ((measurable_pi_apply t).comp (measurable_drvX h 1))
    convert h1 using 1
    funext ω
    exact Fin.append_right _ _ k

/-- (i): `X̄` is an SRW in dimension `d + d`. -/
theorem drivers_pair_isSRW (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) :
    IsSRW P (drvPair Ñ) := by
  refine ⟨measurable_drvPair h, fun ω => ?_, Ω, inferInstance, P, drvPoint Ñ, drvPoint_ppp h, ?_⟩
  · -- regular paths
    intro t
    obtain ⟨δ0, hδ0, h0⟩ := isRegularPath_canonical (subProcess Ñ 0) ω t
    obtain ⟨δ1, hδ1, h1⟩ := isRegularPath_canonical (subProcess Ñ 1) ω t
    refine ⟨min δ0 δ1, lt_min hδ0 hδ1, fun s hs1 hs2 => ?_⟩
    show Fin.append (drvX Ñ 0 ω s) (drvX Ñ 1 ω s) = Fin.append (drvX Ñ 0 ω t) (drvX Ñ 1 ω t)
    have e0 : drvX Ñ 0 ω s = drvX Ñ 0 ω t :=
      h0 s hs1 (lt_of_lt_of_le hs2 (by gcongr; exact min_le_left δ0 δ1))
    have e1 : drvX Ñ 1 ω s = drvX Ñ 1 ω t :=
      h1 s hs1 (lt_of_lt_of_le hs2 (by gcongr; exact min_le_right δ0 δ1))
    rw [e0, e1]
  · exact Measure.map_congr (drivers_pair_ae_eq h)

/-- (i): the natural filtration `𝒢_t = σ(X̄(s) : s ≤ t)` is admissible for `X̄`. -/
theorem drivers_pair_admissible (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P) :
    IsAdmissible P (drvPair Ñ) (natFil (drvPair Ñ)) :=
  (drivers_pair_isSRW h).isAdmissible_natFil

/-- (ii): `ℱ^{(j)}_t = σ(X_{1-j}) ∨ σ(X_j(s) : s ≤ t)` is admissible for `X_j`. -/
theorem drivers_admissible (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (j : Fin 2) : IsAdmissible P (drvX Ñ j) (drvFil Ñ j) := by
  have hne : (1 - j) ≠ j := by fin_cases j <;> decide
  exact (drivers_isSRW h j).isAdmissible_sup (measurable_drvX h (1 - j))
    ((drivers_indep h).indepFun hne)

omit [MeasurableSpace Ω] in
/-- (iii): the paths of `X_j` always lie in `Path⁰_d`. -/
theorem drivers_isDrivingPath (j : Fin 2) (ω : Ω) : IsDrivingPath (drvX Ñ j ω) :=
  isDrivingPath_canonical _ ω

omit [MeasurableSpace Ω] in
/-- (iii): on `Ḡ`, `X₀` and `X₁` have no common jump time. -/
theorem drivers_no_common_jump {ω : Ω} (hω : ω ∈ drvGood Ñ) (r : ℝ≥0) :
    ¬ (r ∈ CDisc (drvX Ñ 0 ω) ∧ r ∈ CDisc (drvX Ñ 1 ω)) := by
  rintro ⟨h0, h1⟩
  have j0 := (isJump_of_mem_CDisc _ h0).one_le_tot
  have j1 := (isJump_of_mem_CDisc _ h1).one_le_tot
  have hpos : (0 : ℝ) < r := by exact_mod_cast h0.1
  have hle := good_tot_singleton_le_one hω.2.2 hpos
  have hsum := tot_relabel_pair (Ñ ω) {(r : ℝ)} (measurableSet_singleton _)
  change tot (drvPoint Ñ ω) {(r : ℝ)} = _ at hsum
  rw [hsum] at hle
  have h2 : (1 : ℝ≥0∞) + 1 ≤ 1 := (add_le_add j0 j1).trans hle
  norm_num at h2

omit [MeasurableSpace Ω] in
/-- (iii): the number of jump times of `X_j` in a bounded set `I ⊆ (0, ∞)` is at most
`N^j(D × I)`. -/
theorem drivers_ncard_jumps_le (j : Fin 2) (ω : Ω) {T : ℝ≥0} {I : Set ℝ≥0} (hI : I ⊆ Iic T) :
    (((CDisc (drvX Ñ j ω)) ∩ I).ncard : ℝ≥0∞) ≤
      tot (subProcess Ñ j ω) (((↑) : ℝ≥0 → ℝ) '' I) :=
  ncard_jumps_le_tot _ hI

end ElboimSly.Paper
