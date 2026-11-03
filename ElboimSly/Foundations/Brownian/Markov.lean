/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Invariance
import Mathlib

/-!
# The Markov property at a fixed time (independence part)

Path space, filtration, shifts; Markov property at a fixed time (a), (b).

* `bmFiltration B a`: the natural filtration `ℱ_a = σ(B(s) : s ≤ a)`.
* `shiftPath B a`: the shifted path `sh_a B (u) = B(a+u) - B(a)`.
* `IsStandardBrownianMotion.indep_shift`: `σ(sh_a B)` is independent of `ℱ_a` (a).
* `IsStandardBrownianMotion.hasLaw_eval`, `hasLaw_increment`, `indep_increment`: (b).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Path space, filtration, shifts. The natural filtration `ℱ_a = σ(B(s) : 0 ≤ s ≤ a)`. -/
@[instance_reducible] def bmFiltration (B : ℝ≥0 → Ω → (Fin d → ℝ)) (a : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ a), MeasurableSpace.comap (B s) inferInstance

/-- Path space, filtration, shifts. The shifted path `sh_a B (u) = B(a+u) - B(a)`, as a path-space
valued map. -/
def shiftPath (B : ℝ≥0 → Ω → (Fin d → ℝ)) (a : ℝ≥0) (ω : Ω) : ℝ≥0 → Fin d → ℝ :=
  fun u => B (a + u) ω - B a ω

lemma bmFiltration_le {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : ∀ t, Measurable (B t)) (a : ℝ≥0) :
    bmFiltration B a ≤ mΩ :=
  iSup₂_le fun s _ => (hB s).comap_le

omit mΩ in
lemma measurable_bmFiltration {B : ℝ≥0 → Ω → (Fin d → ℝ)} {s a : ℝ≥0} (h : s ≤ a) :
    Measurable[bmFiltration B a] (B s) := by
  intro t ht
  exact (le_iSup₂_of_le s h le_rfl :
    MeasurableSpace.comap (B s) inferInstance ≤ bmFiltration B a) _ ⟨t, ht, rfl⟩

omit mΩ in
lemma bmFiltration_mono (B : ℝ≥0 → Ω → (Fin d → ℝ)) {a b : ℝ≥0} (h : a ≤ b) :
    bmFiltration B a ≤ bmFiltration B b :=
  iSup₂_le fun s hs => le_iSup₂_of_le s (hs.trans h) le_rfl

lemma measurable_shiftPath {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : ∀ t, Measurable (B t)) (a : ℝ≥0) :
    Measurable (shiftPath B a) :=
  measurable_pi_iff.2 fun u => (hB (a + u)).sub (hB a)

/-- Markov property at a fixed time (a), independence. `σ(sh_a B)` is independent of `ℱ_a`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.indep_shift [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (a : ℝ≥0) :
    Indep (MeasurableSpace.comap (shiftPath B a) inferInstance) (bmFiltration B a) P := by
  classical
  let ιY := Σ _ : Fin d, ℝ≥0
  let ιZ := Σ _ : Fin d, Set.Iic a
  let Y : ιY → Ω → ℝ := fun p ω => B (a + p.2) ω p.1 - B a ω p.1
  let Z : ιZ → Ω → ℝ := fun q ω => B q.2.1 ω q.1
  have hmem : ∀ p : Σ _ : Fin d, ℝ≥0, MemLp (fun ω => B p.2 ω p.1) 2 P := fun p =>
    ((hB.isPreBrownianReal p.1).isGaussianProcess.hasGaussianLaw_eval p.2).memLp_two
  have hmY : ∀ p, Measurable (Y p) := fun p =>
    ((measurable_pi_apply p.1).comp (hB.measurable _)).sub
      ((measurable_pi_apply p.1).comp (hB.measurable _))
  have hmZ : ∀ q, Measurable (Z q) := fun q => (measurable_pi_apply q.1).comp (hB.measurable _)
  -- the joint process is Gaussian
  have hG : IsGaussianProcess (Sum.elim Y Z) P := by
    let u : ιY ⊕ ιZ → Σ _ : Fin d, ℝ≥0 := Sum.elim (fun p => ⟨p.1, a + p.2⟩) (fun q => ⟨q.1, q.2.1⟩)
    let v : ιY ⊕ ιZ → Σ _ : Fin d, ℝ≥0 := Sum.elim (fun p => ⟨p.1, a⟩) (fun q => ⟨q.1, q.2.1⟩)
    let α : ιY ⊕ ιZ → ℝ := fun _ => 1
    let β : ιY ⊕ ιZ → ℝ := Sum.elim (fun _ => -1) (fun _ => 0)
    have := isGaussianProcess_twoTerms hB.isGaussianProcess u v α β
    convert this using 1
    funext s ω
    rcases s with p | q <;> simp [u, v, α, β, Y, Z, sub_eq_add_neg]
  have hind : IndepFun (fun ω p => Y p ω) (fun ω q => Z q ω) P := by
    refine hG.indepFun_of_covariance_eq_zero (fun p => (hmY p).aemeasurable)
      (fun q => (hmZ q).aemeasurable) ?_
    intro p q
    obtain ⟨i, u⟩ := p
    obtain ⟨j, s, hs⟩ := q
    have hsa : s ≤ a := hs
    show cov[fun ω => B (a + u) ω i - B a ω i, fun ω => B s ω j; P] = 0
    rw [covariance_fun_sub_left (hmem ⟨i, a + u⟩) (hmem ⟨i, a⟩) (hmem ⟨j, s⟩)]
    have h1 := hB.covariance_eval ⟨i, a + u⟩ ⟨j, s⟩
    have h2 := hB.covariance_eval ⟨i, a⟩ ⟨j, s⟩
    simp only at h1 h2
    rw [h1, h2]
    split_ifs
    · rw [min_eq_right (hsa.trans le_self_add), min_eq_right hsa]; ring
    · ring
  -- transfer to the σ-algebras
  have h1 : MeasurableSpace.comap (shiftPath B a) inferInstance ≤
      MeasurableSpace.comap (fun ω p => Y p ω) inferInstance := by
    have : shiftPath B a = (fun (y : ιY → ℝ) (u : ℝ≥0) (i : Fin d) => y ⟨i, u⟩) ∘
        (fun ω p => Y p ω) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    refine MeasurableSpace.comap_mono ?_
    exact (measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun i => measurable_pi_apply _).comap_le
  have h2 : bmFiltration B a ≤ MeasurableSpace.comap (fun ω q => Z q ω) inferInstance := by
    refine iSup₂_le fun s hs => ?_
    have : B s = (fun (z : ιZ → ℝ) (i : Fin d) => z ⟨i, ⟨s, hs⟩⟩) ∘ (fun ω q => Z q ω) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    refine MeasurableSpace.comap_mono ?_
    exact (measurable_pi_iff.2 fun i => measurable_pi_apply _).comap_le
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind h1) h2

/-- The law of `B(t)` is `N_d(0, t I)`, the product of one-dimensional Gaussians. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.hasLaw_eval [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (t : ℝ≥0) :
    HasLaw (B t) (Measure.pi fun _ : Fin d => gaussianReal 0 t) P := by
  have hind : iIndepFun (fun i ω => B t ω i) P :=
    hB.iIndepFun.comp (fun _ (w : ℝ≥0 → ℝ) => w t) fun _ => measurable_pi_apply t
  have hm : ∀ i, Measurable (fun ω => B t ω i) := fun i =>
    (measurable_pi_apply i).comp (hB.measurable t)
  refine ⟨(hB.measurable t).aemeasurable, ?_⟩
  have := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).1 hind
  convert this using 2
  funext i
  exact ((hB.isPreBrownianReal i).hasLaw_eval t).map_eq.symm

/-- Markov property at a fixed time (b), the law of an increment: for `s ≤ t`,
`B(t) - B(s) ~ N_d(0, (t-s) I)`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.hasLaw_increment [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {s t : ℝ≥0} (h : s ≤ t) :
    HasLaw (fun ω => B t ω - B s ω) (Measure.pi fun _ : Fin d => gaussianReal 0 (t - s)) P := by
  have := (hB.shift s).hasLaw_eval (t - s)
  have e : s + (t - s) = t := add_tsub_cancel_of_le h
  simpa [e] using this

/-- Markov property at a fixed time (b), independence of an increment from the past. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.indep_increment [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {s t : ℝ≥0} (h : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (bmFiltration B s) P := by
  refine indep_of_indep_of_le_left (hB.indep_shift s) ?_
  have : (fun ω => B t ω - B s ω) = (fun (w : ℝ≥0 → Fin d → ℝ) => w (t - s)) ∘ shiftPath B s := by
    funext ω
    simp [shiftPath, add_tsub_cancel_of_le h]
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

end ElboimSly.Brownian
