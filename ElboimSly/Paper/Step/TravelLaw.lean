/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelTrunc
public import ElboimSly.Paper.Step.TravelCat
public import ElboimSly.Paper.Step.DrivenLaw
public import Mathlib

/-!
# The truncated block endpoints in the natural coupling

ES22 Lemma 7.3; ES22 Lemma 7.4 (truncation step). In the natural coupling with offset `a` and
all lengths `T`, put `X_i := 𝟙{W_i ∉ farSet K T} W_i(T)` (as a real vector). Then the `X_i` are
measurable, independent (laws in the natural coupling), bounded by `K`, centred
(lattice symmetry of the regenerated walk, through `ppLaw_neg`), and `∑ᵢ E (X_i^{(c)})² ≤ k v` when the second moment
bound `v` of second moment of a truncated endpoint holds; and `P(W_i ∈ farSet K T)` is bounded through the law
`ppLaw` (`stepReg_law`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Y : Ω → PathSpace d}

theorem measurable_stepReg_path (hY : Measurable Y) (hYr : ∀ ω, IsRegPath (Y ω)) :
    Measurable fun ω (t : ℝ≥0) => stepReg β (Y ω) t := by
  have hΦ : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} =>
      drivenRegenFrom β.toNNReal x.1 :=
    measurable_pi_iff.2 (measurable_drivenRegenFrom_subtype toNNReal_pos')
  have := hΦ.comp (hY.subtype_mk (p := IsRegPath) (f := Y) (h := hYr))
  exact this

theorem measurable_stepWj (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0)
    (s : ℕ → ℝ≥0) (j : ℕ) : Measurable fun ω => stepWj β a s (Y ω) j := by
  have hreg : ∀ ω, IsRegPath (stepWin (a + stepPartial s j) (s j) (Y ω)) := fun ω =>
    (isDrivingPath_stepWin (hYp ω) _ _).toIsRegPath
  have hm : Measurable fun ω => (⟨stepWin (a + stepPartial s j) (s j) (Y ω), hreg ω⟩ :
      {x : ℝ≥0 → Fin d → ℤ // IsRegPath x}) := ((measurable_stepWin _ _).comp hY.1).subtype_mk
  have h2 := (measurable_stepRegStopped (β := β) (s j)).comp hm
  have e : ∀ ω, stepWj β a s (Y ω) j =
      stepRegStopped β (s j) (stepWin (a + stepPartial s j) (s j) (Y ω)) :=
    fun ω => stepWj_eq (hYp ω) a s j
  have e' : (fun ω => stepWj β a s (Y ω) j) = ((fun y : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} =>
      stepRegStopped β (s j) y.1) ∘ fun ω => (⟨stepWin (a + stepPartial s j) (s j) (Y ω), hreg ω⟩ :
      {x : ℝ≥0 → Fin d → ℤ // IsRegPath x})) := funext e
  rw [e']
  exact h2

/-- The law of the `j`-th stopped walk of the natural coupling is `ppLaw`. -/
theorem map_stepWj_ppLaw (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (a : ℝ≥0) (s : ℕ → ℝ≥0) (j : ℕ) :
    P.map (fun ω => stepWj β a s (Y ω) j) = ppLaw Pe N (s j) := by
  rw [map_stepWj hY hYp a s j]
  have hlaw := stepReg_law hY hYp hN
  have hm : Measurable fun ω (t : ℝ≥0) => stepReg β (Y ω) t :=
    measurable_stepReg_path hY.1 fun ω => (hYp ω).toIsRegPath
  have e : (fun ω => stepRegStopped β (s j) (Y ω)) =
      (SRW.stopPath (s j)) ∘ (fun ω (t : ℝ≥0) => stepReg β (Y ω) t) := rfl
  unfold ppLaw
  rw [e, ← Measure.map_map (SRW.measurable_stopPath _) hm, hlaw]
  rfl

/-- The truncated endpoint vector `X_i = 𝟙{W_i ∉ farSet K T} W_i(T)` of the natural coupling with
all lengths `T`, as a real vector. -/
noncomputable def travelX (β : ℝ) (a T : ℝ≥0) (K : ℝ) (Y : Ω → PathSpace d) (i : ℕ) (ω : Ω) :
    Fin d → ℝ := fun c => ((truncEnd T K (stepWj β a (fun _ => T) (Y ω) i) c : ℤ) : ℝ)

theorem measurable_intCastPi : Measurable fun v : Fin d → ℤ => (fun c => ((v c : ℤ) : ℝ)) :=
  measurable_pi_iff.2 fun c => (measurable_of_countable (Int.cast : ℤ → ℝ)).comp
    (measurable_pi_apply c)

theorem measurable_travelX (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d) (a T : ℝ≥0) (K : ℝ)
    (i : ℕ) : Measurable (travelX β a T K Y i) :=
  measurable_intCastPi.comp ((measurable_truncEnd T K).comp
    (measurable_stepWj (β := β) hY hYp a (fun _ => T) i))

theorem iIndepFun_travelX (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d) (a T : ℝ≥0) (K : ℝ)
    (k : ℕ) : iIndepFun (fun (i : Fin k) => travelX β a T K Y i) P := by
  have := hY.isProbabilityMeasure
  have h0 := iIndepFun_stepWj (β := β) hY hYp a (fun _ => T)
  have h1 := h0.comp (fun _ => fun w : ℝ≥0 → Fin d → ℤ =>
      (fun c => ((truncEnd T K w c : ℤ) : ℝ)))
    (fun _ => measurable_intCastPi.comp (measurable_truncEnd T K))
  exact h1.precomp (g := fun i : Fin k => (i : ℕ)) Fin.val_injective

omit [Fact (0 < β)] [MeasurableSpace Ω] in
theorem norm_travelX (a T : ℝ≥0) {K : ℝ} (hK : 0 ≤ K) (i : ℕ) (ω : Ω) :
    ‖travelX β a T K Y i ω‖ ≤ K := by
  unfold travelX
  rw [norm_intCast_pi]
  exact norm_truncEnd_le hK _

variable {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe}
  {N : Ωe → Measure (ℕ × RingSpace d β)}

theorem integral_travelX (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (a T : ℝ≥0) {K : ℝ} (hK : 0 ≤ K) (i : ℕ) : ∫ ω, travelX β a T K Y i ω ∂P = 0 := by
  have := hY.isProbabilityMeasure
  have hint : Integrable (travelX β a T K Y i) P :=
    Integrable.of_bound (measurable_travelX hY hYp a T K i).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun ω => norm_travelX a T hK i ω)
  funext c
  have hc := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) c).integral_comp_comm
    hint
  simp only [ContinuousLinearMap.proj_apply] at hc
  rw [Pi.zero_apply, ← hc]
  have hW := measurable_stepWj (β := β) hY hYp a (fun _ => T) i
  have hlaw := map_stepWj_ppLaw hY hYp hN a (fun _ => T) i
  have hF : Measurable fun w : ℝ≥0 → Fin d → ℤ => ((truncEnd T K w c : ℤ) : ℝ) :=
    (measurable_of_countable (Int.cast : ℤ → ℝ)).comp
      ((measurable_pi_apply c).comp (measurable_truncEnd T K))
  have e : ∫ ω, travelX β a T K Y i ω c ∂P =
      ∫ w, ((truncEnd T K w c : ℤ) : ℝ) ∂ppLaw Pe N T := by
    rw [← hlaw, integral_map hW.aemeasurable hF.aestronglyMeasurable]
    rfl
  rw [e]
  exact integral_eq_zero_of_odd (ppLaw_neg hN T) _ hF fun w => by
    simp [truncEnd_neg]

/-- Each coordinate of `X_i` has second moment at most that of `‖truncEnd‖`. -/
theorem integral_travelX_sq_le (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (a T : ℝ≥0) {K v : ℝ} (hK : 0 ≤ K)
    (hv : ∫ w, ‖truncEnd T K w‖ ^ 2 ∂ppLaw Pe N T ≤ v) (i : ℕ) (c : Fin d) :
    ∫ ω, (travelX β a T K Y i ω c) ^ 2 ∂P ≤ v := by
  have := hY.isProbabilityMeasure
  have hW := measurable_stepWj (β := β) hY hYp a (fun _ => T) i
  have hlaw := map_stepWj_ppLaw hY hYp hN a (fun _ => T) i
  have hF : Measurable fun w : ℝ≥0 → Fin d → ℤ => ((truncEnd T K w c : ℤ) : ℝ) ^ 2 :=
    ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp
      ((measurable_pi_apply c).comp (measurable_truncEnd T K))).pow_const 2
  have hG : Measurable fun w : ℝ≥0 → Fin d → ℤ => ‖truncEnd T K w‖ ^ 2 :=
    (measurable_of_countable (fun v : Fin d → ℤ => ‖v‖ ^ 2)).comp (measurable_truncEnd T K)
  have e : ∫ ω, (travelX β a T K Y i ω c) ^ 2 ∂P =
      ∫ w, ((truncEnd T K w c : ℤ) : ℝ) ^ 2 ∂(P.map fun ω => stepWj β a (fun _ => T) (Y ω) i) := by
    rw [integral_map hW.aemeasurable hF.aestronglyMeasurable]
    rfl
  rw [e, hlaw]
  have : IsFiniteMeasure (ppLaw Pe N T) := by rw [← hlaw]; infer_instance
  have hle : ∀ w : ℝ≥0 → Fin d → ℤ, ((truncEnd T K w c : ℤ) : ℝ) ^ 2 ≤ ‖truncEnd T K w‖ ^ 2 := by
    intro w
    have h1 := norm_le_pi_norm (truncEnd T K w) c
    rw [Int.norm_eq_abs] at h1
    calc ((truncEnd T K w c : ℤ) : ℝ) ^ 2 = |((truncEnd T K w c : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hb : ∀ w : ℝ≥0 → Fin d → ℤ, ‖truncEnd T K w‖ ^ 2 ≤ K ^ 2 := fun w =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_truncEnd_le hK w) 2
  refine le_trans (integral_mono (Integrable.of_bound hF.aestronglyMeasurable (K ^ 2)
    (Filter.Eventually.of_forall fun w => ?_)) (Integrable.of_bound hG.aestronglyMeasurable (K ^ 2)
    (Filter.Eventually.of_forall fun w => ?_)) hle) hv
  · rw [Real.norm_of_nonneg (by positivity)]; exact (hle w).trans (hb w)
  · rw [Real.norm_of_nonneg (by positivity)]; exact hb w

/-- The probability that the `i`-th stopped walk is far. -/
theorem measure_stepWj_farSet (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (a T : ℝ≥0) (K : ℝ) (i : ℕ) :
    P {ω | stepWj β a (fun _ => T) (Y ω) i ∈ farSet K T} = ppLaw Pe N T (farSet K T) := by
  rw [← map_stepWj_ppLaw hY hYp hN a (fun _ => T) i,
    Measure.map_apply (measurable_stepWj (β := β) hY hYp a (fun _ => T) i)
      (measurableSet_farSet K T)]
  rfl

end ElboimSly.Paper.Step
