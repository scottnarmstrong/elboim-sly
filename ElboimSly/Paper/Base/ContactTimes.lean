/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.TwoParticleAdapt
public import ElboimSly.Paper.Base.Hitting
public import Mathlib

/-!
# Contact times of the two particles

Contacts are few (i) and (iii).

`kap m` is the written proof's `κ_{m+1}`: `κ_1 = inf {s ≥ 0 : ‖D(s)‖ ≤ 1}` and
`κ_{m+1} = inf {s ≥ κ_m + 1 : ‖D(s)‖ ≤ 1}`, with `D = y - a - X₁` and `y = 𝔉_{a,b}(X₁, X₂)`.

* `kap_isStoppingTime`: each `κ_m` is a stopping time for `𝒢_t = σ(X̄(s) : s ≤ t)`.
* `kap_succ_ge`: the finite `κ_m` are at least `1` apart.
* `drvD_stopped_measurable`: `D(κ_m)` is `𝒢_{κ_m}`-measurable.
* `norm_drvD_kap_pos`: on `Ḡ ∩ {κ_m < ∞}`, `0 < ‖D(κ_m)‖ ≤ 1`.
* `exists_kap_of_norm_le`, `exists_kap_of_l1_leftLim`: part (iii).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ}

theorem isStepPath_comp₂ {V W X : Type*} (F : V → W → X) {f : ℝ≥0 → V} {g : ℝ≥0 → W}
    (hf : IsStepPath f) (hg : IsStepPath g) : IsStepPath fun s => F (f s) (g s) := by
  refine ⟨fun s => ?_, fun T => ?_⟩
  · filter_upwards [hf.rc s, hg.rc s] with u h1 h2
    rw [h1, h2]
  · refine ((hf.fin T).union (hg.fin T)).subset fun r hr => ?_
    obtain ⟨⟨hr0, hr1⟩, hrT⟩ := hr
    by_contra hcon
    simp only [mem_union, mem_inter_iff, not_or, not_and, mem_Iic] at hcon
    obtain ⟨c1, c2⟩ := hcon
    have e1 : ∀ᶠ u in 𝓝[<] r, f u = f r := by
      by_contra h; exact c1 ⟨hr0, h⟩ hrT
    have e2 : ∀ᶠ u in 𝓝[<] r, g u = g r := by
      by_contra h; exact c2 ⟨hr0, h⟩ hrT
    exact hr1 (by filter_upwards [e1, e2] with u hu1 hu2; rw [hu1, hu2])

theorem isStepPath_const {V : Type*} (c : V) : IsStepPath fun _ : ℝ≥0 => c :=
  ⟨fun _ => Eventually.of_forall fun _ => rfl, fun T => by
    have : CDisc (fun _ : ℝ≥0 => c) = ∅ := by
      ext r
      simp [CDisc]
    rw [this]; simp⟩

section

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

/-- `D = y - a - X₁`. -/
noncomputable def drvD (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a b : Fin d → ℤ) (ω : Ω)
    (t : ℝ≥0) : Fin d → ℤ :=
  drvTwo Ñ a b ω t - a - drvX Ñ 0 ω t

/-- The set `{z : ‖z‖ ≤ 1}`. -/
def unitBall (d : ℕ) : Set (Fin d → ℤ) := {z | ‖z‖ ≤ 1}

/-- Contacts are few: `κ_{m+1}`, indexed from `0`. -/
noncomputable def kap (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a b : Fin d → ℤ) :
    ℕ → Ω → WithTop ℝ≥0
  | 0 => hitAfter (drvD Ñ a b) (fun _ => unitBall d) (fun _ => 0) 0
  | m + 1 => hitAfter (drvD Ñ a b) (fun _ => unitBall d) (kap Ñ a b m) 1

omit [MeasurableSpace Ω] in
theorem isStepPath_drvD (a b : Fin d → ℤ) (ω : Ω) : IsStepPath (drvD Ñ a b ω) := by
  have hy := (isTwoParticle_drvTwo (Ñ := Ñ) a b ω).step
  have hx := (drivers_isDrivingPath (Ñ := Ñ) 0 ω).step
  have h1 : IsStepPath fun s => drvTwo Ñ a b ω s - a :=
    isStepPath_comp₂ (fun u v => u - v) hy (isStepPath_const a)
  exact isStepPath_comp₂ (fun u v => u - v) h1 hx

theorem measurable_sub_gen {Ω' : Type*} {m : MeasurableSpace Ω'} {f g : Ω' → Fin d → ℤ}
    (hf : Measurable[m] f) (hg : Measurable[m] g) (a : Fin d → ℤ) :
    Measurable[m] fun ω => f ω - a - g ω :=
  (measurable_of_countable (fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 - a - p.2)).comp
    (hf.prodMk hg)

omit [MeasurableSpace Ω] in
theorem stopReal_le_of_le_coe {τ : Ω → WithTop ℝ≥0} {ω : Ω} {s : ℝ≥0}
    (h : τ ω ≤ (s : WithTop ℝ≥0)) : τ ω ≠ ⊤ ∧ stopReal τ ω ≤ s := by
  have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top h
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
  refine ⟨hne, ?_⟩
  have e : stopReal τ ω = t := by simp only [stopReal, ← ht, WithTop.untopD_coe]
  rw [e]; exact WithTop.coe_le_coe.1 (ht ▸ h)

omit [MeasurableSpace Ω] in
theorem stopReal_eq_of_ne_top {τ : Ω → WithTop ℝ≥0} {ω : Ω} (h : τ ω ≠ ⊤) :
    (stopReal τ ω : WithTop ℝ≥0) = τ ω := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
  simp only [stopReal, ← ht, WithTop.untopD_coe]

theorem drvD_adapted (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (a b : Fin d → ℤ) (t : ℝ≥0) :
    Measurable[natFil (drvPair Ñ) t] fun ω => drvD Ñ a b ω t := by
  have h0 : Measurable[natFil (drvPair Ñ) t] fun ω => drvPair Ñ ω t :=
    measurable_natFil (drvPair Ñ) le_rfl
  have hx : Measurable[natFil (drvPair Ñ) t] fun ω => drvX Ñ 0 ω t := by
    have e : (fun ω => drvX Ñ 0 ω t) = fun ω => fun i : Fin d => drvPair Ñ ω t (Fin.castAdd d i) := by
      funext ω i; exact (Fin.append_left _ _ i).symm
    rw [e]; exact measurable_fst.comp (measurable_pairVal_gen h0)
  exact measurable_sub_gen (drvTwo_adapted h a b t) hx a

theorem kap_isStoppingTime (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (a b : Fin d → ℤ) :
    ∀ m, IsStoppingTime (drivers_pair_admissible h).filtration (kap Ñ a b m)
  | 0 => hitAfter_isStoppingTime _ (isStoppingTime_const _ (0 : ℝ≥0))
      (fun t => drvD_adapted h a b t) (isStepPath_drvD a b) (fun _z => MeasurableSet.const _)
  | m + 1 => hitAfter_isStoppingTime _ (kap_isStoppingTime h a b m)
      (fun t => drvD_adapted h a b t) (isStepPath_drvD a b) (fun _z => MeasurableSet.const _)

/-- `D(κ_m)` is `𝒢_{κ_m}`-measurable on `{κ_m < ∞}`. -/
theorem drvD_stopped_measurable (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (a b : Fin d → ℤ) (m : ℕ) (z : Fin d → ℤ) :
    MeasurableSet[(kap_isStoppingTime h a b m).measurableSpace]
      {ω | kap Ñ a b m ω ≠ ⊤ ∧ drvD Ñ a b ω (stopReal (kap Ñ a b m) ω) = z} :=
  measurableSet_stopped_eq _ (kap_isStoppingTime h a b m) (fun t => drvD_adapted h a b t)
    (isStepPath_drvD a b) z

end

section

variable {Ω : Type} [MeasurableSpace Ω] {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

omit [MeasurableSpace Ω] in
theorem kap_succ_ge (a b : Fin d → ℤ) (m : ℕ) {ω : Ω} (hω : kap Ñ a b m ω ≠ ⊤) :
    ((stopReal (kap Ñ a b m) ω + 1 : ℝ≥0) : WithTop ℝ≥0) ≤ kap Ñ a b (m + 1) ω :=
  le_hitAfter (isStepPath_drvD a b) ω hω

omit [MeasurableSpace Ω] in
theorem kap_succ_ne_top (a b : Fin d → ℤ) (m : ℕ) {ω : Ω} (hω : kap Ñ a b (m + 1) ω ≠ ⊤) :
    kap Ñ a b m ω ≠ ⊤ := fun h => hω (hitAfter_top ω h)

omit [MeasurableSpace Ω] in
theorem stopReal_kap_succ (a b : Fin d → ℤ) (m : ℕ) {ω : Ω} (hω : kap Ñ a b (m + 1) ω ≠ ⊤) :
    stopReal (kap Ñ a b m) ω + 1 ≤ stopReal (kap Ñ a b (m + 1)) ω := by
  have h := kap_succ_ge a b m (kap_succ_ne_top a b m hω)
  rw [← stopReal_eq_of_ne_top hω] at h
  exact WithTop.coe_le_coe.1 h

omit [MeasurableSpace Ω] in
theorem kap_le_stopReal (a b : Fin d → ℤ) (m : ℕ) {ω : Ω} (hω : kap Ñ a b m ω ≠ ⊤) :
    (m : ℝ≥0) ≤ stopReal (kap Ñ a b m) ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := stopReal_kap_succ a b m hω
    have := ih (kap_succ_ne_top a b m hω)
    push_cast; exact add_le_add ‹_› le_rfl |>.trans ‹_›

omit [MeasurableSpace Ω] in
theorem stopReal_kap_mono (a b : Fin d → ℤ) {m m' : ℕ} (hm : m ≤ m') {ω : Ω}
    (hω : kap Ñ a b m' ω ≠ ⊤) : stopReal (kap Ñ a b m) ω ≤ stopReal (kap Ñ a b m') ω := by
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m' hm' ih =>
    exact (ih (kap_succ_ne_top a b m' hω)).trans
      (le_trans le_self_add (stopReal_kap_succ a b m' hω))

omit [MeasurableSpace Ω] in
theorem drvD_kap_mem (a b : Fin d → ℤ) (m : ℕ) {ω : Ω} (hω : kap Ñ a b m ω ≠ ⊤) :
    ‖drvD Ñ a b ω (stopReal (kap Ñ a b m) ω)‖ ≤ 1 := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hω
  have e : stopReal (kap Ñ a b m) ω = t := by simp only [stopReal, ← ht, WithTop.untopD_coe]
  rw [e]
  cases m with
  | zero => exact (hitAfter_attained (isStepPath_drvD a b) ht.symm).2.2
  | succ m => exact (hitAfter_attained (isStepPath_drvD a b) ht.symm).2.2

omit [MeasurableSpace Ω] in
/-- On `Ḡ`, `0 < ‖D(κ_m)‖ ≤ 1` on `{κ_m < ∞}`. -/
theorem drvD_kap_pos (a b : Fin d → ℤ) (hab : a ≠ b) (m : ℕ) {ω : Ω}
    (hG : ω ∈ drvGood Ñ) (_hω : kap Ñ a b m ω ≠ ⊤) :
    0 < ‖drvD Ñ a b ω (stopReal (kap Ñ a b m) ω)‖ := by
  have hdata : TwoParticleData a b (drvX Ñ 0 ω) (drvX Ñ 1 ω) (drvTwo Ñ a b ω) :=
    ⟨drivers_isDrivingPath 0 ω, drivers_isDrivingPath 1 ω,
      fun r hr hr' => drivers_no_common_jump hG r ⟨hr, hr'⟩, isTwoParticle_drvTwo a b ω⟩
  rw [norm_pos_iff]
  intro hz
  refine hdata.ne hab (stopReal (kap Ñ a b m) ω) ?_
  have : drvTwo Ñ a b ω (stopReal (kap Ñ a b m) ω) - a - drvX Ñ 0 ω (stopReal (kap Ñ a b m) ω)
      = 0 := hz
  rw [sub_sub, sub_eq_zero] at this
  exact this

omit [MeasurableSpace Ω] in
theorem exists_kap_of_norm_le (a b : Fin d → ℤ) (ω : Ω) {s : ℝ≥0}
    (hs : ‖drvD Ñ a b ω s‖ ≤ 1) :
    ∃ m, kap Ñ a b m ω ≠ ⊤ ∧ stopReal (kap Ñ a b m) ω ≤ s ∧
      s < stopReal (kap Ñ a b m) ω + 1 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ m, kap Ñ a b m ω ≠ ⊤ ∧ stopReal (kap Ñ a b m) ω ≤ s := by
    intro m
    induction m with
    | zero =>
      have hcell : ω ∈ hitCell (drvD Ñ a b) (fun _ => unitBall d) (fun _ => (0 : WithTop ℝ≥0))
          0 s := ⟨⟨by simp, by simp [stopReal]⟩, hs⟩
      exact stopReal_le_of_le_coe (hitAfter_le_of_mem_hitCell hcell)
    | succ m ih =>
      have hcell : ω ∈ hitCell (drvD Ñ a b) (fun _ => unitBall d) (kap Ñ a b m) 1 s :=
        ⟨⟨ih.1, hcon m ih.1 ih.2⟩, hs⟩
      exact stopReal_le_of_le_coe (hitAfter_le_of_mem_hitCell hcell)
  obtain ⟨m, hm⟩ := exists_nat_gt s
  have h1 := kap_le_stopReal a b m (key m).1
  have h2 := (key m).2
  have : (m : ℝ≥0) ≤ s := h1.trans h2
  exact absurd hm (not_lt.2 this)

omit [MeasurableSpace Ω] in
theorem exists_kap_of_leftNorm (a b : Fin d → ℤ) (ω : Ω) {r : ℝ≥0} (hr : 0 < r)
    (hev : ∀ᶠ u in 𝓝[<] r, ‖drvD Ñ a b ω u‖ ≤ 1) :
    ∃ m, kap Ñ a b m ω ≠ ⊤ ∧ stopReal (kap Ñ a b m) ω < r ∧
      r ≤ stopReal (kap Ñ a b m) ω + 1 := by
  obtain ⟨l, hl0, hl⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (show (0 : ℝ≥0) < r from hr)).1 hev
  have hlr : l < r := hl0
  classical
  set N := ⌈r⌉₊ with hN
  set Pm : ℕ → Prop := fun m => kap Ñ a b m ω ≠ ⊤ ∧ stopReal (kap Ñ a b m) ω < r with hPm
  have hbd : ∀ m, Pm m → m ≤ N := by
    intro m hm
    have h1 := kap_le_stopReal a b m hm.1
    have : (m : ℝ≥0) < r := lt_of_le_of_lt h1 hm.2
    have h2 : (m : ℝ≥0) ≤ (N : ℝ≥0) := this.le.trans (Nat.le_ceil r)
    exact_mod_cast h2
  obtain ⟨s0, hs0l, hs0r⟩ := exists_between hlr
  obtain ⟨m0, hm0, hm0s, -⟩ := exists_kap_of_norm_le a b ω (hl ⟨hs0l, hs0r⟩)
  have hP0 : Pm m0 := ⟨hm0, lt_of_le_of_lt hm0s hs0r⟩
  have hms : Pm (Nat.findGreatest Pm N) := Nat.findGreatest_spec (hbd m0 hP0) hP0
  refine ⟨Nat.findGreatest Pm N, hms.1, hms.2, ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt hlr hlt)
  obtain ⟨m, hm, hms1, hms2⟩ := exists_kap_of_norm_le a b ω
    (hl ⟨(le_max_left _ _).trans_lt hs1, hs2⟩)
  have hPm1 : Pm m := ⟨hm, lt_of_le_of_lt hms1 hs2⟩
  have hle : m ≤ Nat.findGreatest Pm N := Nat.le_findGreatest (hbd m hPm1) hPm1
  have := stopReal_kap_mono a b hle hms.1
  have h3 := (le_max_right _ _).trans_lt hs1
  exact absurd (hms2.trans_le (add_le_add_left this 1)) (not_lt.2 h3.le)

omit [MeasurableSpace Ω] in
/-- Part (iii), second half: `‖D(r-)‖₁ = 1` puts `r` in `(κ_m, κ_m + 1]`. -/
theorem exists_kap_of_l1_leftLim (a b : Fin d → ℤ) (ω : Ω) {r : ℝ≥0} (hr : 0 < r)
    (h1 : l1 (Function.leftLim (drvTwo Ñ a b ω) r - (a + Function.leftLim (drvX Ñ 0 ω) r)) = 1) :
    ∃ m, kap Ñ a b m ω ≠ ⊤ ∧ stopReal (kap Ñ a b m) ω < r ∧
      r ≤ stopReal (kap Ñ a b m) ω + 1 := by
  refine exists_kap_of_leftNorm a b ω hr ?_
  filter_upwards [(isTwoParticle_drvTwo (Ñ := Ñ) a b ω).step.eventually_left_leftLim hr,
    (drivers_isDrivingPath (Ñ := Ñ) 0 ω).step.eventually_left_leftLim hr] with u hu1 hu2
  have e : drvD Ñ a b ω u = Function.leftLim (drvTwo Ñ a b ω) r -
      (a + Function.leftLim (drvX Ñ 0 ω) r) := by
    unfold drvD; rw [hu1, hu2, sub_sub]
  rw [e]
  exact (norm_le_l1 _).trans (by rw [h1]; norm_num)

end

end ElboimSly.Paper
