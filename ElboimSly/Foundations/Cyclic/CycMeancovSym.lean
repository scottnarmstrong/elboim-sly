/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenLaw
public import ElboimSly.Foundations.Cyclic.CycRegenEnvGlue
public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Foundations.Interchange.LatticeGroup
public import ElboimSly.Foundations.Interchange.LawInvariance
public import Mathlib

/-!
# The regenerated walk is symmetric in law

Symmetric mean and covariance. Let `g` be a lattice automorphism of `ℤᵈ` fixing `0` (a signed
coordinate permutation). Pushing a Poisson environment `N` on `ℕ × S_β` forward by `g` on each
copy gives a Poisson environment with the same intensity (`isPoissonPointProcess_envMap`); the
cyclic walk of `g_* ν` is `g ∘ (cyclic walk of ν)` (`cycWalk_latticeMeasure`), `t_reg` is unchanged
(`cycTreg_latticeMeasure`), so the regenerated walk of `g_* N` is `g ∘ W` (`regenWalk_latticeMeasure`),
and `g ∘ W(t)` has the law of `W(t)` (`law_regen_lattice`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- Apply a lattice automorphism to every copy of an environment on `ℕ × S_β`. -/
noncomputable def envMap (g : LatticeAut d) (ν : Measure (ℕ × RingSpace d β)) :
    Measure (ℕ × RingSpace d β) :=
  ν.map (Prod.map id (ringMapEquiv (edgeEquiv g) (MeasurableEquiv.refl (AddCircle β))))

omit [Fact (0 < β)] in
theorem measurable_envMapFn (g : LatticeAut d) :
    Measurable (Prod.map (id : ℕ → ℕ)
      (ringMapEquiv (edgeEquiv g) (MeasurableEquiv.refl (AddCircle β)))) :=
  measurable_fst.prodMk ((MeasurableEquiv.measurable _).comp measurable_snd)

omit [Fact (0 < β)] in
theorem cycSlice_envMap (g : LatticeAut d) (k : ℕ) (ν : Measure (ℕ × RingSpace d β)) :
    cycSlice k (envMap g ν) = latticeMeasure g (cycSlice k ν) := by
  set ψ := ringMapEquiv (edgeEquiv g) (MeasurableEquiv.refl (AddCircle β)) with hψ
  ext A hA
  have hf := measurable_envMapFn (d := d) (β := β) g
  have hRHS : (latticeMeasure g (cycSlice k ν)) A = (cycSlice k ν) (ψ ⁻¹' A) :=
    Measure.map_apply (MeasurableEquiv.measurable ψ) hA
  rw [hRHS]
  unfold envMap cycSlice
  rw [(measurableEmbedding_prodMk_left k).comap_apply,
    Measure.map_apply hf ((measurableEmbedding_prodMk_left k).measurableSet_image.2 hA),
    (measurableEmbedding_prodMk_left k).comap_apply]
  congr 1
  ext ⟨a, x⟩
  simp only [mem_preimage, mem_image, Prod.map, Prod.mk.injEq, id]
  constructor
  · rintro ⟨y, hy, rfl, h⟩
    exact ⟨x, h ▸ hy, rfl, rfl⟩
  · rintro ⟨y, hy, rfl, rfl⟩
    exact ⟨ψ y, hy, rfl, rfl⟩

theorem isPoissonPointProcess_envMap {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (g : LatticeAut d) :
    IsPoissonPointProcess (fun ω => envMap g (N ω))
      ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe := by
  have : SFinite (ringIntensity d β) := by unfold ringIntensity; infer_instance
  have h := hN.map_measure (measurable_envMapFn (d := d) (β := β) g)
  have e : ((Measure.count : Measure ℕ).prod (ringIntensity d β)).map
      (Prod.map (id : ℕ → ℕ) (ringMapEquiv (edgeEquiv g) (MeasurableEquiv.refl (AddCircle β)))) =
      (Measure.count : Measure ℕ).prod (ringIntensity d β) := by
    rw [← Measure.map_prod_map _ _ measurable_id (MeasurableEquiv.measurable _),
      Measure.map_id, map_ringMapEquiv_lattice]
  rw [e] at h
  exact h

section Pathwise

variable {ν : Measure (RingSpace d β)}

theorem cycWalk_latticeMeasure (hν : Good ν) (g : LatticeAut d) (hg : g.toEquiv 0 = 0)
    (s : ℝ≥0) :
    ElboimSly.cycWalk (latticeMeasure g ν) 0 0 (s : ℝ) = g.toEquiv (ElboimSly.cycWalk ν 0 0 (s : ℝ)) := by
  rw [cycWalk_eq_trajProc (good_latticeMeasure g hν), cycWalk_eq_trajProc hν]
  have := trajProc_latticeMeasure hν g 0 0
  rw [hg] at this
  rw [this]

theorem cycWalk_latticeMeasure_real (hν : Good ν) (g : LatticeAut d) (hg : g.toEquiv 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    ElboimSly.cycWalk (latticeMeasure g ν) 0 0 s = g.toEquiv (ElboimSly.cycWalk ν 0 0 s) := by
  have := cycWalk_latticeMeasure hν g hg s.toNNReal
  rwa [Real.coe_toNNReal _ hs] at this

theorem cycTreg_latticeMeasure (hν : Good ν) (g : LatticeAut d) (hg : g.toEquiv 0 = 0) :
    ElboimSly.cycTreg (latticeMeasure g ν) = ElboimSly.cycTreg ν := by
  have hβ : 0 < β := Fact.out
  have hiff : ∀ k : ℕ, ElboimSly.cycWalk (latticeMeasure g ν) 0 0 ((k : ℝ) * β) = 0 ↔
      ElboimSly.cycWalk ν 0 0 ((k : ℝ) * β) = 0 := fun k => by
    rw [cycWalk_latticeMeasure_real hν g hg (by positivity)]
    constructor
    · intro h
      apply g.toEquiv.injective
      rw [h, hg]
    · intro h; rw [h, hg]
  unfold ElboimSly.cycTreg
  apply le_antisymm
  · refine le_iInf fun k => iInf_le_of_le ⟨k.1, k.2.1, (hiff k.1).2 k.2.2⟩ le_rfl
  · refine le_iInf fun k => iInf_le_of_le ⟨k.1, k.2.1, (hiff k.1).1 k.2.2⟩ le_rfl

theorem regenWalk_latticeMeasure {ν : ℕ → Measure (RingSpace d β)} (hν : ∀ k, Good (ν k))
    (g : LatticeAut d) (hg : g.toEquiv 0 = 0) (t : ℝ≥0) :
    ElboimSly.regenWalk (fun k => latticeMeasure g (ν k)) (t : ℝ) =
      g.toEquiv (ElboimSly.regenWalk ν (t : ℝ)) := by
  rw [← gluedWalk_eq_regenWalk, ← gluedWalk_eq_regenWalk]
  have h : (fun k => ElboimSly.cycTreg (latticeMeasure g (ν k))) =
      fun k => ElboimSly.cycTreg (ν k) := funext fun k => cycTreg_latticeMeasure (hν k) g hg
  rw [h]
  unfold gluedWalk
  exact cycWalk_latticeMeasure (hν _) g hg _

end Pathwise

/-- `g ∘ W(t)` has the law of `W(t)` for `g` a lattice automorphism fixing `0`. -/
theorem law_regen_lattice {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (g : LatticeAut d) (hg : g.toEquiv 0 = 0) (t : ℝ≥0) :
    Pe.map (fun ω => g.toEquiv (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ))) =
      Pe.map (fun ω => ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ)) := by
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  have hN' := isPoissonPointProcess_envMap hN g
  set Gt : Measure (ℕ × RingSpace d β) → Fin d → ℤ := fun ν =>
    regRecProc ((regPlan d β).envFinalOr CycRec.empty ν) t with hGt
  have hGm : Measurable Gt := (measurable_pi_apply t).comp
    (measurable_regRecProc.comp ((regPlan d β).measurable_envFinalOr CycRec.empty))
  have h1 : ∀ᵐ ω ∂Pe, ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) = Gt (N ω) := by
    filter_upwards [regen_env_ae hN] with ω h
    exact congrFun h t
  have h2 : ∀ᵐ ω ∂Pe, ElboimSly.regenWalk (fun k => cycSlice k (envMap g (N ω))) (t : ℝ) =
      Gt (envMap g (N ω)) := by
    filter_upwards [regen_env_ae hN'] with ω h
    exact congrFun h t
  have h3 : ∀ᵐ ω ∂Pe, ElboimSly.regenWalk (fun k => cycSlice k (envMap g (N ω))) (t : ℝ) =
      g.toEquiv (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ)) := by
    filter_upwards [ae_cycGood hN] with ω hω
    simp only [cycSlice_envMap]
    exact regenWalk_latticeMeasure hω g hg t
  have e1 : Pe.map (fun ω => g.toEquiv (ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ))) =
      Pe.map (fun ω => Gt (envMap g (N ω))) := by
    refine Measure.map_congr ?_
    filter_upwards [h2, h3] with ω a b
    rw [← b, a]
  have e2 : Pe.map (fun ω => ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ)) =
      Pe.map (fun ω => Gt (N ω)) := Measure.map_congr h1
  rw [e1, e2]
  have hm1 : Measurable fun ω => envMap g (N ω) := hN'.measurable
  have hm2 : Measurable N := hN.measurable
  have a1 : Pe.map (fun ω => Gt (envMap g (N ω))) = (Pe.map (fun ω => envMap g (N ω))).map Gt :=
    (Measure.map_map hGm hm1).symm
  have a2 : Pe.map (fun ω => Gt (N ω)) = (Pe.map N).map Gt := (Measure.map_map hGm hm2).symm
  rw [a1, a2, hN.map_eq_map hN']

end ElboimSly.Cyclic

end
