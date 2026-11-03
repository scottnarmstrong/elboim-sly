/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.ExitEmbed
public import ElboimSly.Foundations.StrongApprox.PiTranspose
public import ElboimSly.Foundations.StrongApprox.Signs
public import Mathlib

/-!
# The coupling space

The coupling space (Part II).

The `d`-dimensional Lévy–Ciesielski Brownian motion `Bd d` on `ΩB d`, the coordinate embeddings
for fixed moduli `r`, and the law of the embedding vector for fixed moduli.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

lemma comap_pathC0 {Ω : Type*} [MeasurableSpace Ω] {β : ℝ≥0 → Ω → ℝ} (h : IsProcess β) :
    MeasurableSpace.comap (pathC0 h) inferInstance =
      MeasurableSpace.comap (fun ω t => β t ω) inferInstance :=
  MeasurableSpace.comap_comp (f := Subtype.val) (g := pathC0 h)

/-- The sample space of the `d`-dimensional Lévy–Ciesielski construction. -/
abbrev ΩB (d : ℕ) : Type := Idx d → ℝ

/-- The product Gaussian measure on `ΩB d`. -/
noncomputable def PB (d : ℕ) : Measure (ΩB d) := Measure.infinitePi fun _ : Idx d => gaussianReal 0 1

instance (d : ℕ) : IsProbabilityMeasure (PB d) := by unfold PB; infer_instance

/-- The `d`-dimensional Lévy–Ciesielski Brownian motion. -/
noncomputable def Bd (d : ℕ) : ℝ≥0 → ΩB d → (Fin d → ℝ) :=
  levyCiesielski (fun (α : Idx d) (ω : Idx d → ℝ) => ω α)

theorem isStandardBM_Bd (d : ℕ) : IsStandardBrownianMotion d (Bd d) (PB d) := by
  let μ : Idx d → Measure ℝ := fun _ => gaussianReal 0 1
  have hind : iIndepFun (fun (α : Idx d) (x : Idx d → ℝ) => x α) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (P := μ) (X := fun _ x => x) fun _ => measurable_id
  have hlaw : ∀ α, HasLaw (fun (x : Idx d → ℝ) => x α) (gaussianReal 0 1)
      (Measure.infinitePi μ) := fun α =>
    ⟨(measurable_pi_apply α).aemeasurable, Measure.infinitePi_map_eval μ α⟩
  exact isStandardBrownianMotion_levyCiesielski (P := Measure.infinitePi μ)
    (ξ := fun (α : Idx d) (x : Idx d → ℝ) => x α) (fun α => measurable_pi_apply α) hind hlaw

theorem isStandardRealBM_Bd_coord (d : ℕ) (k : Fin d) :
    IsStandardRealBM (fun t ω => Bd d t ω k) (PB d) :=
  (isStandardBM_Bd d).isStandardRealBM_coord k

/-- The moduli of the `k`-th coordinate, extended by `0`. -/
def rr {d : ℕ} (ℓ : ℕ) (r : Fin ℓ → Fin d → ℝ) (k : Fin d) : ℕ → ℝ :=
  fun i => if h : i < ℓ then r ⟨i, h⟩ k else 0

lemma rr_nonneg {d ℓ : ℕ} {r : Fin ℓ → Fin d → ℝ} (hr : ∀ i k, 0 ≤ r i k) (k : Fin d) (i : ℕ) :
    0 ≤ rr ℓ r k i := by
  unfold rr; split_ifs
  · exact hr _ _
  · exact le_rfl

lemma rr_fin {d ℓ : ℕ} (r : Fin ℓ → Fin d → ℝ) (k : Fin d) (i : Fin ℓ) :
    rr ℓ r k i = r i k := by
  simp [rr]

/-- The embedding vectors of all `d` coordinates, for fixed moduli `r`. -/
noncomputable def vecV {d : ℕ} (ℓ : ℕ) (r : Fin ℓ → Fin d → ℝ) (ω : ΩB d) :
    Fin d → Fin ℓ → ℝ × ℝ≥0∞ :=
  fun k => embVec ℓ (rr ℓ r k) (fun t => Bd d t ω k)

/-- The law of the embedding vector for fixed moduli. -/
noncomputable def Lr {d : ℕ} (ℓ : ℕ) (r : Fin ℓ → Fin d → ℝ) :
    Measure (Fin d → Fin ℓ → ℝ × ℝ≥0∞) :=
  Measure.pi fun k : Fin d => Measure.pi fun i : Fin ℓ =>
    (symLaw (r i k)).prod (exitLaw (r i k))

/-- Laws in the coupling, Step 1: fixed moduli. -/
theorem map_vecV {d ℓ : ℕ} {r : Fin ℓ → Fin d → ℝ} (hr : ∀ i k, 0 ≤ r i k) :
    (PB d).map (vecV ℓ r) = Lr ℓ r := by
  have hbm := isStandardRealBM_Bd_coord d
  have hproc := fun k => isProcess_of_realBM (hbm k)
  have hind : iIndepFun (fun (k : Fin d) (ω : ΩB d) (t : ℝ≥0) => Bd d t ω k) (PB d) :=
    (isStandardBM_Bd d).iIndepFun
  have hind0 : iIndepFun (fun k => pathC0 (hproc k)) (PB d) := by
    rw [iIndepFun_iff_iIndep (fun _ => inferInstance)] at hind ⊢
    convert hind using 2 with k
    exact comap_pathC0 (hproc k)
  set g : ∀ k : Fin d, C0 → Fin ℓ → ℝ × ℝ≥0∞ := fun k w => embVec ℓ (rr ℓ r k) w.1 with hg
  have hind1 := hind0.comp g (fun k => measurable_embVecC0 ℓ (rr ℓ r k))
  have hm : ∀ k, Measurable ((g k) ∘ (pathC0 (hproc k))) := fun k =>
    (measurable_embVecC0 ℓ (rr ℓ r k)).comp (measurable_pathC0 _)
  have := (iIndepFun_iff_map_fun_eq_pi_map (fun k => (hm k).aemeasurable)).1 hind1
  have e : vecV ℓ r = fun ω k => ((g k) ∘ (pathC0 (hproc k))) ω := rfl
  rw [e, this, Lr]
  congr 1
  funext k
  have := map_embVec ℓ (rr ℓ r k) (rr_nonneg hr k) (hbm k)
  simp only [rr_fin] at this
  exact this

end ElboimSly.StrongApprox
