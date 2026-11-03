/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.ExitPath
public import ElboimSly.Foundations.Brownian.PathDense
public import Mathlib

/-!
# Measurability of exit times and of the iterated embedding

Measurability of the embedding (b)--(d) (Part II).

For a real process `Z` on a measurable space `Ω'` all of whose paths lie in `C₀` and whose
coordinates are measurable (`IsProcess Z`), and measurable moduli `ρ i : Ω' → ℝ`, the exit times,
exit positions and clocks of the iterated embedding of `(ρ i ω)_i` in `Z(ω)` are measurable
functions of `ω`, and the iterated paths again form a process.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A real process with all paths in `C₀` and measurable coordinates. -/
def IsProcess (Z : ℝ≥0 → Ω → ℝ) : Prop := (∀ ω, IsC0 fun t => Z t ω) ∧ ∀ t, Measurable (Z t)

lemma IsProcess.measurable_uncurry {Z : ℝ≥0 → Ω → ℝ} (hZ : IsProcess Z) :
    Measurable (Function.uncurry Z) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => (hZ.1 ω).1) hZ.2

open ElboimSly.Brownian in
lemma exists_le_abs_iff_iSup {w : ℝ≥0 → ℝ} (hw : Continuous w) (t : ℝ≥0) (ρ : ℝ) :
    (∃ s ≤ t, ρ ≤ |w s|) ↔
      (ρ : EReal) ≤ ⨆ s ∈ denseSub (Set.Icc 0 t), ((|w s| : ℝ) : EReal) := by
  have hg : Continuous fun s => |w s| := continuous_abs.comp hw
  rw [← iSup_eq_denseSub (f := fun s => |w s|) Set.ordConnected_Icc hg]
  constructor
  · rintro ⟨s, hs, h⟩
    exact (EReal.coe_le_coe_iff.2 h).trans (le_biSup (fun s => ((|w s| : ℝ) : EReal))
      (show s ∈ Set.Icc 0 t from ⟨bot_le, hs⟩))
  · intro h
    obtain ⟨t0, ht0, hmax⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMaxOn
      ⟨0, le_rfl, bot_le⟩ hg.continuousOn
    refine ⟨t0, ht0.2, ?_⟩
    have : ⨆ s ∈ Set.Icc (0 : ℝ≥0) t, ((|w s| : ℝ) : EReal) ≤ ((|w t0| : ℝ) : EReal) :=
      iSup₂_le fun s hs => EReal.coe_le_coe_iff.2 (hmax hs)
    exact EReal.coe_le_coe_iff.1 (h.trans this)

omit mΩ in
lemma measurableSet_exists_le_abs {m : MeasurableSpace Ω} {Z : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Z t ω) {t : ℝ≥0} (hZm : ∀ s ≤ t, Measurable[m] (Z s))
    {ρ : Ω → ℝ} (hρ : Measurable[m] ρ) :
    MeasurableSet[m] {ω | ∃ s ≤ t, ρ ω ≤ |Z s ω|} := by
  have e : {ω | ∃ s ≤ t, ρ ω ≤ |Z s ω|} = {ω | (ρ ω : EReal) ≤
      ⨆ s ∈ ElboimSly.Brownian.denseSub (Set.Icc 0 t), ((|Z s ω| : ℝ) : EReal)} := by
    ext ω
    exact exists_le_abs_iff_iSup (hc ω) t (ρ ω)
  rw [e]
  refine measurableSet_le (measurable_coe_real_ereal.comp hρ) ?_
  refine Measurable.biSup _ (ElboimSly.Brownian.denseSub_countable _) fun s hs => ?_
  have hst : s ≤ t := (ElboimSly.Brownian.denseSub_subset _ hs).2
  exact measurable_coe_real_ereal.comp (hZm s hst).abs

lemma shiftAt_apply (τ : ℝ≥0∞) (w : ℝ≥0 → ℝ) (s : ℝ≥0) :
    shiftAt τ w s = if τ = ⊤ then w s else w (τ.toNNReal + s) - w τ.toNNReal := by
  unfold shiftAt
  split_ifs <;> rfl

/-- The exit time of the path of `Z(ω)` from the interval of radius `ρ ω`. -/
noncomputable def procExit (ρ : Ω → ℝ) (Z : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  exitTime (ρ ω) (fun t => Z t ω)

/-- The process shifted by the random time `τ`. -/
noncomputable def procShift (τ : Ω → ℝ≥0∞) (Z : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => shiftAt (τ ω) (fun t => Z t ω) s

/-- The position `Z(τ)`, `0` on `{τ = ∞}`. -/
noncomputable def procEnd (τ : Ω → ℝ≥0∞) (Z : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  endVal (τ ω) (fun t => Z t ω)

lemma measurable_procExit {Z : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ} (hZ : IsProcess Z)
    (hρ : Measurable ρ) : Measurable (procExit ρ Z) := by
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe t =>
    have : procExit ρ Z ⁻¹' Set.Iic (t : ℝ≥0∞) = {ω | ∃ s ≤ t, ρ ω ≤ |Z s ω|} := by
      ext ω
      exact exitTime_le_iff (hZ.1 ω).1 t
    rw [this]
    exact measurableSet_exists_le_abs (fun ω => (hZ.1 ω).1) (fun s _ => hZ.2 s) hρ

lemma measurable_procEnd {Z : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞} (hZ : IsProcess Z)
    (hτ : Measurable τ) : Measurable (procEnd τ Z) := by
  have h1 : Measurable fun ω => Z (τ ω).toNNReal ω :=
    hZ.measurable_uncurry.comp ((hτ.ennreal_toNNReal).prodMk measurable_id)
  have : procEnd τ Z = fun ω => if τ ω = ⊤ then 0 else Z (τ ω).toNNReal ω := by
    funext ω; simp [procEnd, endVal]
  rw [this]
  exact Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const h1

lemma IsProcess.shift {Z : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞} (hZ : IsProcess Z)
    (hτ : Measurable τ) : IsProcess (procShift τ Z) := by
  refine ⟨fun ω => isC0_shiftAt (hZ.1 ω) (τ ω), fun s => ?_⟩
  have h1 : Measurable fun ω => Z ((τ ω).toNNReal + s) ω :=
    hZ.measurable_uncurry.comp (((hτ.ennreal_toNNReal).add_const s).prodMk measurable_id)
  have h2 : Measurable fun ω => Z (τ ω).toNNReal ω :=
    hZ.measurable_uncurry.comp ((hτ.ennreal_toNNReal).prodMk measurable_id)
  have : procShift τ Z s = fun ω => if τ ω = ⊤ then Z s ω else
      Z ((τ ω).toNNReal + s) ω - Z (τ ω).toNNReal ω := by
    funext ω; exact shiftAt_apply _ _ _
  rw [this]
  exact Measurable.ite (hτ (measurableSet_singleton ⊤)) (hZ.2 s) (h1.sub h2)

/-- The `i`-th iterated embedding path of the moduli `(ρs k ω)_k` in `Z(ω)`, as a process. -/
noncomputable def embProc (ρs : ℕ → Ω → ℝ) (Z : ℝ≥0 → Ω → ℝ) (i : ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => embPath (fun k => ρs k ω) (fun t => Z t ω) i s

omit mΩ in
lemma embProc_succ (ρs : ℕ → Ω → ℝ) (Z : ℝ≥0 → Ω → ℝ) (i : ℕ) :
    embProc ρs Z (i + 1) = procShift (procExit (ρs i) (embProc ρs Z i)) (embProc ρs Z i) := rfl

lemma isProcess_embProc {Z : ℝ≥0 → Ω → ℝ} {ρs : ℕ → Ω → ℝ} (hZ : IsProcess Z)
    (hρ : ∀ k, Measurable (ρs k)) (i : ℕ) : IsProcess (embProc ρs Z i) := by
  induction i with
  | zero => exact hZ
  | succ i ih =>
    rw [embProc_succ]
    exact ih.shift (measurable_procExit ih (hρ i))

lemma measurable_embTau {Z : ℝ≥0 → Ω → ℝ} {ρs : ℕ → Ω → ℝ} (hZ : IsProcess Z)
    (hρ : ∀ k, Measurable (ρs k)) (i : ℕ) :
    Measurable fun ω => embTau (fun k => ρs k ω) (fun t => Z t ω) i :=
  measurable_procExit (isProcess_embProc hZ hρ i) (hρ i)

lemma measurable_embX {Z : ℝ≥0 → Ω → ℝ} {ρs : ℕ → Ω → ℝ} (hZ : IsProcess Z)
    (hρ : ∀ k, Measurable (ρs k)) (i : ℕ) :
    Measurable fun ω => embX (fun k => ρs k ω) (fun t => Z t ω) i :=
  measurable_procEnd (isProcess_embProc hZ hρ i) (measurable_embTau hZ hρ i)

end ElboimSly.StrongApprox
