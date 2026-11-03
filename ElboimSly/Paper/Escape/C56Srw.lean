/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Adapted
public import ElboimSly.Paper.Base.IdentH4
public import ElboimSly.Foundations.SRW.Claim56B0Stopped
public import ElboimSly.Foundations.SRW.Maximal
public import ElboimSly.Foundations.SRW.Claim56Small
public import Mathlib

/-!
# ES22 Claim 5.6: the regenerated walk below time `β` is an SRW

ES22 Claim 5.6, "Law on `[0, β]`" (the cyclic walk is an SRW up to time β (b)).  Events about the walk on
`[0, R]`, `R ≤ β`, have the same probability as for the model SRW when they are regular and depend
on the path stopped at `R`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.SRW

theorem isRegularPath_of_rc {d : ℕ} {γ : ℝ≥0 → Fin d → ℤ} (h : IsRCPath γ) : IsRegularPath γ := by
  intro t
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (h t)
  refine ⟨u - t, tsub_pos_of_lt hu, fun s hs1 hs2 => hsub ⟨hs1, ?_⟩⟩
  have : t + (u - t) = u := add_tsub_cancel_of_le hu.le
  rwa [this] at hs2

theorem IsRegSet.compl' {d : ℕ} {Γ : Set (PathSpace d)} (h : IsRegSet Γ) : IsRegSet Γᶜ := by
  obtain ⟨Γ', hm, hΓ⟩ := h
  exact ⟨Γ'ᶜ, hm.compl, fun γ hγ => by simp [hΓ γ hγ]⟩

/-- Transfer of a stopped regular event from the walk to the model SRW. -/
theorem transfer_stopped {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → PathSpace d} (R : ℝ≥0) (hZm : Measurable fun ω s => Z ω (min s R))
    (hZr : ∀ ω, IsRegularPath fun s => Z ω (min s R))
    (hlaw : P.map (fun ω s => Z ω (min s R)) =
      (srwP d).map (fun ω s => srwZ d ω (min s R))) {Γ : Set (PathSpace d)} (hΓ : IsRegSet Γ)
    (hstop : ∀ γ, γ ∈ Γ ↔ (fun s => γ (min s R)) ∈ Γ) :
    P {ω | Z ω ∈ Γ} = (srwP d) {ω | srwZ d ω ∈ Γ} := by
  obtain ⟨Γ', hΓm, hΓ'⟩ := hΓ
  have hsm : Measurable fun ω s => srwZ d ω (min s R) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply (min s R)).comp (srwZ_isSRW d).1
  have hsr : ∀ ω, IsRegularPath fun s => srwZ d ω (min s R) :=
    fun ω => ((srwZ_isSRW d).2.1 ω).stop R
  have e1 : {ω | Z ω ∈ Γ} = (fun ω s => Z ω (min s R)) ⁻¹' Γ' := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← hΓ' _ (hZr ω)]
    exact hstop _
  have e2 : {ω | srwZ d ω ∈ Γ} = (fun ω s => srwZ d ω (min s R)) ⁻¹' Γ' := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← hΓ' _ (hsr ω)]
    exact hstop _
  rw [e1, e2, ← Measure.map_apply hZm hΓm, ← Measure.map_apply hsm hΓm, hlaw]

section Regen

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ (k + 2) β)}

/-- The law of the regenerated walk stopped at `R ≤ β` is the stopped SRW law. -/
theorem stopped_regen_law (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    {R : ℝ≥0} (hR : (R : ℝ) ≤ β) :
    Pr.map (fun ω s => escW N ω (min s R)) =
      (srwP (k + 2)).map (fun ω s => srwZ (k + 2) ω (min s R)) := by
  have hrestr := regen_restrict_law hN hR (srwZ_isSRW (k + 2))
  -- the stopped path is a measurable function of the restriction to `[0, R]`
  let Φ : (Set.Icc (0 : ℝ≥0) R → Fin (k + 2) → ℤ) → PathSpace (k + 2) :=
    fun f s => f ⟨min s R, bot_le, min_le_right _ _⟩
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun s => measurable_pi_apply _
  have hNg : Measurable (avoidPath (cycNgood N)) :=
    measurable_avoidPath_cycNgood hN.measurable
  have hrE : Measurable fun ω (t : Set.Icc (0 : ℝ≥0) R) => escW N ω (t : ℝ≥0) :=
    measurable_pi_iff.2 fun t => (measurable_pi_apply (t : ℝ≥0)).comp hNg
  have hrZ : Measurable fun ω (t : Set.Icc (0 : ℝ≥0) R) => srwZ (k + 2) ω (t : ℝ≥0) :=
    measurable_pi_iff.2 fun t => (measurable_pi_apply (t : ℝ≥0)).comp (srwZ_isSRW (k + 2)).1
  have e1 : Pr.map (fun ω s => escW N ω (min s R)) =
      (Pr.map (fun ω (t : Set.Icc (0 : ℝ≥0) R) => escW N ω (t : ℝ≥0))).map Φ := by
    rw [Measure.map_map hΦ hrE]; rfl
  have e2 : Pr.map (fun ω (t : Set.Icc (0 : ℝ≥0) R) => escW N ω (t : ℝ≥0)) =
      Pr.map (fun ω (t : Set.Icc (0 : ℝ≥0) R) =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_cycNgood_eq hN] with ω hω
    funext t
    exact congrFun (avoidWalk_congr hω) _
  have e3 : (srwP (k + 2)).map (fun ω s => srwZ (k + 2) ω (min s R)) =
      ((srwP (k + 2)).map (fun ω (t : Set.Icc (0 : ℝ≥0) R) => srwZ (k + 2) ω (t : ℝ≥0))).map Φ := by
    rw [Measure.map_map hΦ hrZ]; rfl
  rw [e1, e2, hrestr, e3]

theorem measurable_escW_stop (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    (R : ℝ≥0) : Measurable fun ω s => escW N ω (min s R) :=
  measurable_pi_iff.2 fun s => (measurable_pi_apply (min s R)).comp
    (measurable_avoidPath_cycNgood hN.measurable)

omit mΩ in
theorem regular_escW_stop (ω : Ω) (R : ℝ≥0) :
    IsRegularPath fun s => escW N ω (min s R) := by
  refine isRegularPath_of_rc ?_
  have := isRCPath_comp_mono (isRCPath_avoidPath (cycGood_cycNgood N ω))
    (g := fun s : ℝ≥0 => min s R) (continuous_id.min continuous_const)
    (fun a b h => min_le_min h le_rfl)
  exact this

/-- Maximal inequality for the walk on `[0, R]`, `R ≤ β`. -/
theorem prob_max_regen (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    {R : ℝ≥0} (hR : (R : ℝ) ≤ β) (hR0 : 0 < R) {a : ℝ} (ha : 0 ≤ a) :
    Pr {ω | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖escW N ω s‖} ≤
      ENNReal.ofReal (4 * (k + 2 : ℕ) * Real.exp (-min (a ^ 2 / (8 * R)) (a / 2))) := by
  have := hN.isProbabilityMeasure
  have hreg : IsRegSet {γ : PathSpace (k + 2) | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖γ s‖} := by
    have h := isRegSet_forall_pred (d := k + 2) (fun _ y => ‖y‖ < a)
      (fun y s hn => ⟨1, one_pos, fun s' _ _ => hn⟩) 0 R
    have h2 := h.compl'
    obtain ⟨Γ', hm, hΓ⟩ := h2
    refine ⟨Γ', hm, fun γ hγ => ?_⟩
    rw [← hΓ γ hγ]
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, not_lt]
    constructor
    · rintro ⟨s, hs, hle⟩; exact ⟨s, zero_le, hs, hle⟩
    · rintro ⟨s, -, hs, hle⟩; exact ⟨s, hs, hle⟩
  have hstop : ∀ γ : PathSpace (k + 2), γ ∈ {γ : PathSpace (k + 2) | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖γ s‖} ↔
      (fun s => γ (min s R)) ∈ {γ : PathSpace (k + 2) | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖γ s‖} := by
    intro γ
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨s, hs, hle⟩; exact ⟨s, hs, by rwa [min_eq_left hs]⟩
    · rintro ⟨s, hs, hle⟩; exact ⟨s, hs, by rwa [min_eq_left hs] at hle⟩
  have key := transfer_stopped (P := Pr) (Z := fun ω => escW N ω) R (measurable_escW_stop hN R)
    (fun ω => regular_escW_stop ω R) (stopped_regen_law hN hR) hreg hstop
  have hmax := (srwZ_isSRW (k + 2)).maximal (T := R) hR0 ha
  have : Pr {ω | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖escW N ω s‖} =
      (srwP (k + 2)) {ω | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖srwZ (k + 2) ω s‖} := key
  rw [this]
  have := (srwZ_isSRW (k + 2)).isProbabilityMeasure
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 ?_
  exact hmax

/-- The kernel event for the walk on `[0, R]`, `R ≤ β`. -/
theorem prob_ker_regen (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    {R : ℝ≥0} (hR : (R : ℝ) ≤ β) (Q : Set (Fin (k + 2) → ℤ)) (x z : Fin (k + 2) → ℤ) :
    Pr {ω | escW N ω ∈ kerSet Q R x z} = ENNReal.ofReal (kernel Q R x z) := by
  have := hN.isProbabilityMeasure
  have hstop : ∀ γ : PathSpace (k + 2), γ ∈ kerSet Q R x z ↔
      (fun s => γ (min s R)) ∈ kerSet Q R x z := by
    intro γ
    simp only [kerSet, mem_ofPred_eq, min_self]
    refine and_congr Iff.rfl (forall_congr' fun s => imp_congr_right fun hs => ?_)
    rw [min_eq_left hs]
  have key := transfer_stopped (P := Pr) (Z := fun ω => escW N ω) R (measurable_escW_stop hN R)
    (fun ω => regular_escW_stop ω R) (stopped_regen_law hN hR) (isRegSet_kerSet Q R x z) hstop
  rw [show {ω | escW N ω ∈ kerSet Q R x z} = {ω | (fun ω => escW N ω) ω ∈ kerSet Q R x z} from rfl,
    key]
  exact (srwZ_isSRW (k + 2)).prob_kerSet Q R x z

end Regen

end ElboimSly.Paper.Escape

end
