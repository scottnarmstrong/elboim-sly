/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMarkovRec
public import ElboimSly.Foundations.Cyclic.CycWalkFiltration
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycEvents
public import Mathlib

/-!
# The filtration `𝒢₀ ∨ ℱ^W_t` is the joint exploration filtration of `𝒫_W`

Markov property of the environment at walk stopping times, proof ("Hence, with the given `𝒢₀`, `ℱ^{𝒫_W}_s = 𝒢₀ ∨ σ(W(r) : r ≤ s)
∨ 𝒩 = ℱ_s`").

* `markovW N ω s`: the cyclic walk of `markovNgood N ω` (`N` with fixed values off `{N ∈ Good}`);
* `cycMarkovFilt`: the filtration `t ↦ 𝒢₀ ⊔ cycWalkFiltration Pr (markovNgood N) t`;
* `cycMarkovFilt_eq`: it equals `cycMultiFilt (onePlan d β)` for the environment `liftU ∘ N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]

/-- The cyclic walk `W(s) = W^{N}_{0,0}(s)` of `N` (given fixed values off `{N ∈ Good}`). -/
noncomputable def markovW (N : Ω → Measure (RingSpace d β)) (ω : Ω) (s : ℝ) : Fin d → ℤ :=
  ElboimSly.cycWalk (markovNgood N ω) 0 0 s

theorem measurable_markovW {N : Ω → Measure (RingSpace d β)} (hN : Measurable N) {s : ℝ}
    (hs : 0 ≤ s) : Measurable fun ω => markovW N ω s := by
  have h1 : Measurable fun ω => (⟨markovNgood N ω, good_markovNgood N ω⟩ : GoodSet d β) :=
    Measurable.subtype_mk (measurable_markovNgood hN)
  exact (measurable_cycWalk 0 0 hs).comp h1

/-- The record `ω ↦ ρ^{𝒫_W}(liftU (markovNgood N ω))`. -/
theorem trunc_envFinal_markov (N : Ω → Measure (RingSpace d β)) (ω : Ω) (t : ℝ≥0) :
    CycRec.trunc t (CycPlan.envFinal (onePlan d β) (liftU (markovNgood N ω))) =
      Sum.inl ⟨1, fun _ => markovEntry (liftU (markovNgood N ω)) t⟩ :=
  trunc_envFinal_onePlan _ _

theorem markovEntry_fn_markovW (N : Ω → Measure (RingSpace d β)) (ω : Ω) (t r : ℝ≥0) :
    (markovEntry (liftU (markovNgood N ω)) t).path.fn r = markovW N ω ((min r t : ℝ≥0) : ℝ) := by
  rw [markovEntry_fn, envPath_fn_liftU (good_markovNgood N ω)]
  rfl

theorem coord_markovRec (N : Ω → Measure (RingSpace d β)) (ω : Ω) (t : ℝ≥0) :
    CycRec.coord (CycPlan.junk (onePlan d β))
      (Sum.inl ⟨1, fun _ => markovEntry (liftU (markovNgood N ω)) t⟩ : CycRec Unit d) 0 =
        markovEntry (liftU (markovNgood N ω)) t := by
  simp [CycRec.coord, CycRec.nth]

theorem measurable_sigmaMk_one {d : ℕ} :
    Measurable (Sigma.mk (β := fun k => CycRecN Unit d k) 1) :=
  fun _ hB => (MeasurableSpace.measurableSet_iInf.mp hB) 1

theorem coord_markovRec_gen (ν : Measure (Unit × RingSpace d β)) (t : ℝ≥0) :
    CycRec.coord (CycPlan.junk (onePlan d β))
      (Sum.inl ⟨1, fun _ => markovEntry ν t⟩ : CycRec Unit d) 0 = markovEntry ν t := by
  simp [CycRec.coord, CycRec.nth]

/-- The record is measurable as soon as the walk values up to time `t` are. -/
theorem measurable_markovRec {Ω' : Type*} [MeasurableSpace Ω'] (N : Ω' → Measure (RingSpace d β))
    (t : ℝ≥0) (hW : ∀ s : ℝ≥0, s ≤ t → Measurable fun ω => markovW N ω (s : ℝ)) :
    Measurable fun ω => (Sum.inl ⟨1, fun _ => markovEntry (liftU (markovNgood N ω)) t⟩ :
      CycRec Unit d) := by
  have hpath : Measurable fun ω => ((markovEntry (liftU (markovNgood N ω)) t).2.1 : CPath (Fin d → ℤ)) := by
    rw [CPath.measurable_iff]
    refine ⟨?_, fun r => ?_⟩
    · have : (fun ω => ((markovEntry (liftU (markovNgood N ω)) t).2.1 : CPath (Fin d → ℤ)).len) =
        fun _ => (t : ℝ≥0∞) := funext fun ω => markovEntry_len _ _
      rw [this]; exact measurable_const
    · have : (fun ω => ((markovEntry (liftU (markovNgood N ω)) t).2.1 : CPath (Fin d → ℤ)).fn r) =
        fun ω => markovW N ω ((min r t : ℝ≥0) : ℝ) :=
        funext fun ω => markovEntry_fn_markovW N ω t r
      rw [this]; exact hW _ (min_le_right _ _)
  have hE : Measurable fun ω => markovEntry (liftU (markovNgood N ω)) t :=
    measurable_const.prodMk (Measurable.subtype_mk hpath)
  exact measurable_inl.comp (measurable_sigmaMk_one.comp (measurable_pi_iff.2 fun _ => hE))

/-- `σ(W(s) : s ≤ t) = σ(Trunc_t ∘ ρ^{𝒫_W})`. -/
theorem iSup_comap_markovW_eq {N : Ω → Measure (RingSpace d β)} (t : ℝ≥0) :
    (⨆ s : ℝ≥0, ⨆ _ : s ≤ t, MeasurableSpace.comap
        (fun ω => ElboimSly.cycWalk (markovNgood N ω) 0 0 (s : ℝ)) inferInstance) =
      MeasurableSpace.comap (fun ω => CycRec.trunc t
        (CycPlan.envFinal (onePlan d β) (cycNgood (fun ω => liftU (N ω)) ω))) inferInstance := by
  have hcg : ∀ ω, cycNgood (fun ω => liftU (N ω)) ω = liftU (markovNgood N ω) := fun ω =>
    (liftU_markovNgood N ω).symm
  simp_rw [hcg, trunc_envFinal_markov]
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    have hg : Measurable fun ρ : CycRec Unit d =>
        (CycRec.coord (CycPlan.junk (onePlan d β)) ρ 0).2.1.fn s :=
      (CPath.measurable_eval s).comp (measurable_subtype_coe.comp (measurable_snd.comp
        (CycRec.measurable_coord (CycPlan.junk (onePlan d β)) 0)))
    have heq : (fun ω => ElboimSly.cycWalk (markovNgood N ω) 0 0 (s : ℝ)) =
        (fun ρ : CycRec Unit d => (CycRec.coord (CycPlan.junk (onePlan d β)) ρ 0).2.1.fn s) ∘
          (fun ω => (Sum.inl ⟨1, fun _ => markovEntry (liftU (markovNgood N ω)) t⟩ :
            CycRec Unit d)) := by
      funext ω
      simp only [Function.comp, coord_markovRec]
      have := markovEntry_fn_markovW N ω t s
      rw [min_eq_left hs] at this
      exact this.symm
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hg.comap_le
  · refine Measurable.comap_le ?_
    refine @measurable_markovRec d β _ Ω (⨆ s : ℝ≥0, ⨆ _ : s ≤ t, MeasurableSpace.comap
        (fun ω => ElboimSly.cycWalk (markovNgood N ω) 0 0 (s : ℝ)) inferInstance) N t ?_
    intro s hs
    exact Measurable.of_comap_le (le_iSup₂_of_le s hs le_rfl)

/-- The filtration `ℱ_t = 𝒢₀ ∨ ℱ^W_t` of Markov property of the environment at walk stopping times, for the walk of `N` (given fixed values
off `{N ∈ Good}`). -/
noncomputable def cycMarkovFilt (h𝒢 : 𝒢₀ ≤ mΩ)
    {N : Ω → Measure (RingSpace d β)} (hN : Measurable N) (Pr : Measure Ω) : Filtration ℝ≥0 mΩ where
  seq t := 𝒢₀ ⊔ cycWalkFiltration Pr (markovNgood N) t
  mono' _ _ hab := sup_le_sup_left (cycWalkFiltration_mono Pr _ hab) _
  le' t := sup_le h𝒢 (cycWalkFiltration_le_ambient Pr (markovNgood N)
    (fun s => measurable_markovW hN s.2) t)

/-- `ℱ_t = 𝒢₀ ∨ ℱ^W_t` is the joint exploration filtration of the plan `𝒫_W` for `liftU ∘ N`. -/
theorem cycMarkovFilt_eq (h𝒢 : 𝒢₀ ≤ mΩ)
    {N : Ω → Measure (RingSpace d β)} (hN : Measurable N) (Pr : Measure Ω) :
    cycMarkovFilt 𝒢₀ h𝒢 hN Pr =
      cycMultiFilt (onePlan d β) 𝒢₀ (N := fun ω => liftU (N ω)) (measurable_liftU.comp hN) h𝒢 Pr := by
  refine Filtration.ext (funext fun t => ?_)
  show 𝒢₀ ⊔ cycWalkFiltration Pr (markovNgood N) t = cycFiltration Pr 𝒢₀ _ t
  rw [cycFiltration_eq 𝒢₀ (CycPlan.junk (onePlan d β))]
  unfold cycWalkFiltration
  rw [iSup_comap_markovW_eq t, sup_assoc]

end ElboimSly.Cyclic

end
