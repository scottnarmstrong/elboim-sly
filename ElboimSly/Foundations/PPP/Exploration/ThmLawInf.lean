/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmResample
import Mathlib

/-!
# Sequential first-point exploration: the law of the whole history

Sequential first-point exploration (d$'$). A probability measure on `𝕌 × 𝕆^ℕ` is determined by its
finite-dimensional marginals `Law(U, O_0, …, O_{k-1})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U]

/-- The restriction `π_k : ℋ_∞ → ℋ_k`. -/
def truncHist (k : ℕ) (y : U × (ℕ → Outcome S)) : Hist U S k := (y.1, fun i : Fin k => y.2 i)

theorem measurable_truncHist (k : ℕ) : Measurable (truncHist (U := U) (S := S) k) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply (i : ℕ)).comp
    measurable_snd)

/-- Shortening a history. -/
def shortenHist {k k' : ℕ} (hk : k ≤ k') (η : Hist U S k') : Hist U S k :=
  (η.1, fun i : Fin k => η.2 (Fin.castLE hk i))

theorem measurable_shortenHist {k k' : ℕ} (hk : k ≤ k') :
    Measurable (shortenHist (U := U) (S := S) hk) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun _i => (measurable_pi_apply _).comp measurable_snd)

omit [MeasurableSpace U] in
theorem truncHist_eq_shorten {k k' : ℕ} (hk : k ≤ k') (y : U × (ℕ → Outcome S)) :
    truncHist k y = shortenHist hk (truncHist k' y) := rfl

/-- The cylinder sets. -/
def cylSets (U : Type*) [MeasurableSpace U] (S : Type*) [MeasurableSpace S] :
    Set (Set (U × (ℕ → Outcome S))) :=
  {s | ∃ (k : ℕ) (A : Set (Hist U S k)), MeasurableSet A ∧ s = truncHist k ⁻¹' A}

theorem isPiSystem_cylSets : IsPiSystem (cylSets U S) := by
  rintro _ ⟨k, A, hA, rfl⟩ _ ⟨k', B, hB, rfl⟩ -
  rcases le_total k k' with hk | hk
  · refine ⟨k', shortenHist hk ⁻¹' A ∩ B, (measurable_shortenHist hk hA).inter hB, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [truncHist_eq_shorten hk y]
  · refine ⟨k, A ∩ shortenHist hk ⁻¹' B, hA.inter (measurable_shortenHist hk hB), ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [truncHist_eq_shorten hk y]

theorem generateFrom_cylSets :
    MeasurableSpace.generateFrom (cylSets U S) =
      (inferInstance : MeasurableSpace (U × (ℕ → Outcome S))) := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨k, A, hA, rfl⟩
    exact measurable_truncHist k hA
  · refine sup_le ?_ ?_
    · rintro _ ⟨C, hC, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨0, Prod.fst ⁻¹' C, measurable_fst hC, ?_⟩
      rfl
    · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le fun j => ?_
      rintro _ ⟨_, ⟨D, hD, rfl⟩, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨j + 1,
        (fun η : Hist U S (j + 1) => η.2 (Fin.last j)) ⁻¹' D,
        ((measurable_pi_apply (Fin.last j)).comp measurable_snd) hD, ?_⟩
      rfl

/-- Sequential first-point exploration (d$'$): uniqueness from finite-dimensional marginals. -/
theorem ext_of_truncHist {Q Q' : Measure (U × (ℕ → Outcome S))} [IsFiniteMeasure Q]
    (h : ∀ k, Q.map (truncHist k) = Q'.map (truncHist k)) : Q = Q' := by
  refine ext_of_generate_finite (cylSets U S) generateFrom_cylSets.symm isPiSystem_cylSets ?_ ?_
  · rintro _ ⟨k, A, hA, rfl⟩
    have := congrArg (fun m => m A) (h k)
    simpa [Measure.map_apply (measurable_truncHist k) hA] using this
  · have := congrArg (fun m => m Set.univ) (h 0)
    simpa [Measure.map_apply (measurable_truncHist 0) MeasurableSet.univ] using this

namespace ExplScheme

variable {μ : Measure S} [SigmaFinite μ] (sch : ExplScheme μ U)

theorem Hfun_fst (k : ℕ) (x : U × Measure S) : (sch.Hfun k x).1 = x.1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Hfun_succ, Hist.snoc, ih]

theorem truncHist_Hinf (k : ℕ) (x : U × Measure S) :
    truncHist k (sch.Hinf x) = sch.Hfun k x := by
  refine Prod.ext (sch.Hfun_fst k x).symm (funext fun i => ?_)
  exact (sch.Hfun_coord k x i).symm

theorem measurable_phi (k : ℕ) {g : Hist U S (k + 1) → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun η : Hist U S k => ∫⁻ o, g (η.snoc o) ∂(sch.kernelAt k η) :=
  measurable_lintegral_probeKernel μ (R := sch.Rt k) (h := sch.h k) (sch.measurable_Rt k)
    (sch.measurable_h k) (g := fun p : Hist U S k × Outcome S => g (p.1.snoc p.2))
    (hg.comp (Hist.measurable_snoc k))

end ExplScheme

namespace ExplRun

variable {μ : Measure S} [SigmaFinite μ] {sch : ExplScheme μ U} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} (run : ExplRun sch P)

include run

/-- The whole history `H_∞`. -/
noncomputable def Hinf (ω : Ω) : U × (ℕ → Outcome S) := sch.Hinf (run.X ω)

theorem measurable_Hinf : Measurable run.Hinf := sch.measurable_Hinf.comp run.measurable_X

theorem law_trunc (k : ℕ) : (P.map run.Hinf).map (truncHist k) = P.map (run.H k) := by
  rw [Measure.map_map (measurable_truncHist k) run.measurable_Hinf]
  congr 1
  funext ω
  exact sch.truncHist_Hinf k (run.X ω)

/-- Sequential first-point exploration (d-prime), the second part: any sequence of outcomes with the
same initial law and the same one-step kernels has the law of `H_∞`. -/
theorem law_Hinf_of_kernel {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂}
    [IsProbabilityMeasure P₂] {u₂ : Ω₂ → U} {O₂ : ℕ → Ω₂ → Outcome S} (hu₂ : Measurable u₂)
    (hO₂ : ∀ j, Measurable (O₂ j)) (hlaw : P₂.map u₂ = P.map run.u)
    (hstep : ∀ (k : ℕ) (g : Hist U S (k + 1) → ℝ≥0∞), Measurable g →
      ∫⁻ ω, g (u₂ ω, fun i : Fin (k + 1) => O₂ i ω) ∂P₂ =
        ∫⁻ ω, ∫⁻ o, g (Hist.snoc ((u₂ ω, fun i : Fin k => O₂ i ω) : Hist U S k) o)
          ∂(sch.kernelAt k ((u₂ ω, fun i : Fin k => O₂ i ω) : Hist U S k)) ∂P₂) :
    P₂.map (fun ω => (u₂ ω, fun j => O₂ j ω)) = P.map run.Hinf := by
  classical
  have := run.prob
  have hH₂ : ∀ k, Measurable fun ω => ((u₂ ω, fun i : Fin k => O₂ i ω) : Hist U S k) :=
    fun k => hu₂.prodMk (measurable_pi_iff.2 fun i => hO₂ i)
  have key : ∀ k, P₂.map (fun ω => ((u₂ ω, fun i : Fin k => O₂ i ω) : Hist U S k)) =
      P.map (run.H k) := by
    intro k
    induction k with
    | zero =>
      have e1 : (fun ω => ((u₂ ω, fun i : Fin 0 => O₂ i ω) : Hist U S 0)) =
          (fun a : U => ((a, Fin.elim0) : Hist U S 0)) ∘ u₂ := by
        funext ω; exact Prod.ext rfl (funext fun i => i.elim0)
      have e2 : run.H 0 = (fun a : U => ((a, Fin.elim0) : Hist U S 0)) ∘ run.u := rfl
      have hm : Measurable fun a : U => ((a, Fin.elim0) : Hist U S 0) :=
        measurable_id.prodMk measurable_const
      rw [e1, e2, ← Measure.map_map hm hu₂, ← Measure.map_map hm run.measurable_u, hlaw]
    | succ k ih =>
      refine Measure.ext fun A hA => ?_
      have hφ := sch.measurable_phi k (measurable_one.indicator hA)
      rw [Measure.map_apply (hH₂ (k + 1)) hA, Measure.map_apply (run.measurable_H (k + 1)) hA,
        ← lintegral_indicator_one ((hH₂ (k + 1)) hA),
        ← lintegral_indicator_one ((run.measurable_H (k + 1)) hA)]
      have h1 := hstep k (A.indicator 1) (measurable_one.indicator hA)
      have h2 := run.stepLaw (g := A.indicator 1) (measurable_one.indicator hA)
      have e3 : ∀ ω, A.indicator (1 : Hist U S (k + 1) → ℝ≥0∞) (u₂ ω, fun i : Fin (k + 1) => O₂ i ω)
          = (A.indicator 1) ((u₂ ω, fun i : Fin (k + 1) => O₂ i ω)) := fun ω => rfl
      calc ∫⁻ ω, (((fun ω => ((u₂ ω, fun i : Fin (k + 1) => O₂ i ω) : Hist U S (k + 1))) ⁻¹' A).indicator 1 ω) ∂P₂
          = ∫⁻ ω, A.indicator 1 (u₂ ω, fun i : Fin (k + 1) => O₂ i ω) ∂P₂ := by
            refine lintegral_congr fun ω => ?_
            simp only [Set.indicator]
            exact if_congr Iff.rfl rfl rfl
        _ = ∫⁻ ω, (fun η : Hist U S k => ∫⁻ o, A.indicator (1 : Hist U S (k + 1) → ℝ≥0∞)
              (η.snoc o) ∂(sch.kernelAt k η)) (u₂ ω, fun i : Fin k => O₂ i ω) ∂P₂ := h1
        _ = ∫⁻ η, (fun η : Hist U S k => ∫⁻ o, A.indicator (1 : Hist U S (k + 1) → ℝ≥0∞)
              (η.snoc o) ∂(sch.kernelAt k η)) η
              ∂(P₂.map fun ω => ((u₂ ω, fun i : Fin k => O₂ i ω) : Hist U S k)) :=
            (lintegral_map hφ (hH₂ k)).symm
        _ = ∫⁻ η, (fun η : Hist U S k => ∫⁻ o, A.indicator (1 : Hist U S (k + 1) → ℝ≥0∞)
              (η.snoc o) ∂(sch.kernelAt k η)) η ∂(P.map (run.H k)) := by rw [ih]
        _ = ∫⁻ ω, (fun η : Hist U S k => ∫⁻ o, A.indicator (1 : Hist U S (k + 1) → ℝ≥0∞)
              (η.snoc o) ∂(sch.kernelAt k η)) (run.H k ω) ∂P :=
            lintegral_map hφ (run.measurable_H k)
        _ = ∫⁻ ω, A.indicator 1 (run.H (k + 1) ω) ∂P := h2.symm
        _ = _ := by
            refine lintegral_congr fun ω => ?_
            simp only [Set.indicator]
            exact if_congr Iff.rfl rfl rfl
  have hHm : Measurable fun ω => ((u₂ ω, fun j => O₂ j ω) : U × (ℕ → Outcome S)) :=
    hu₂.prodMk (measurable_pi_iff.2 hO₂)
  have : IsFiniteMeasure (P₂.map fun ω => ((u₂ ω, fun j => O₂ j ω) : U × (ℕ → Outcome S))) :=
    Measure.isFiniteMeasure_map _ _
  refine ext_of_truncHist fun k => ?_
  rw [Measure.map_map (measurable_truncHist k) hHm, run.law_trunc]
  exact key k

end ExplRun

end ElboimSly
