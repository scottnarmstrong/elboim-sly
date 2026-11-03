/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Srw
public import ElboimSly.Paper.Escape.C56Rel
public import ElboimSly.Paper.Escape.C56Rel2
public import ElboimSly.Paper.Escape.C56Param
public import ElboimSly.Paper.Escape.C56GProps
public import ElboimSly.Paper.Escape.C56Gam
public import ElboimSly.Paper.Escape.C56Slice
public import Mathlib

/-!
# ES22 Claim 5.6, phase `0`

ES22 Claim 5.6, "Phase `0`".  `ℬ₀` holds with probability at least
`½ c_1^{201d} (2√τ)^{-201dC_1}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.SRW ElboimSly.Brownian

/-- A path whose relaxed times have large measure has a relaxed time in the window. -/
theorem exists_relaxed_of_volume {d : ℕ} {β : ℝ} (g : ℝ → Fin d → ℤ) {Ti lo : ℝ}
    (hlo0 : 0 ≤ lo) (hloTi : lo ≤ Ti) (hgap : 1 / 10 * Ti < Ti - lo)
    (hvol : ENNReal.ofReal (9 / 10 * Ti) ≤
      volume {s : ℝ | s ∈ Icc 0 Ti ∧ IsRelaxedTimeWrt β g 0 s}) :
    ∃ r ∈ Ico lo Ti, IsRelaxedTimeWrt β g 0 r := by
  by_contra hno
  push Not at hno
  have hsub : {s : ℝ | s ∈ Icc 0 Ti ∧ IsRelaxedTimeWrt β g 0 s} ⊆ Icc 0 Ti \ Ico lo Ti := by
    rintro s ⟨hs1, hs2⟩
    exact ⟨hs1, fun hJ => hno s hJ hs2⟩
  have hJ_sub : Ico lo Ti ⊆ Icc 0 Ti := fun s hs => ⟨by linarith [hs.1], hs.2.le⟩
  have hvol' := (measure_mono hsub).trans
    (le_of_eq (measure_sdiff (μ := volume) hJ_sub measurableSet_Ico.nullMeasurableSet
      (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)))
  rw [Real.volume_Icc, Real.volume_Ico] at hvol'
  have hTi0 : 0 ≤ Ti := hlo0.trans hloTi
  have hJlen : 0 ≤ Ti - lo := by linarith
  have h1 := hvol.trans hvol'
  simp only [sub_zero] at h1
  have h2 : ENNReal.ofReal (9 / 10 * Ti) + ENNReal.ofReal (Ti - lo) ≤ ENNReal.ofReal Ti := by
    calc ENNReal.ofReal (9 / 10 * Ti) + ENNReal.ofReal (Ti - lo)
        ≤ (ENNReal.ofReal Ti - ENNReal.ofReal (Ti - lo)) + ENNReal.ofReal (Ti - lo) := by gcongr
      _ = ENNReal.ofReal Ti := tsub_add_cancel_of_le (ENNReal.ofReal_le_ofReal (by linarith))
  rw [← ENNReal.ofReal_add (by linarith) hJlen] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff hTi0).1 h2
  linarith

theorem claimBox_eq {k : ℕ} (u : Fin (k + 2) → ℤ) (j : ℕ) : claimBox u j = escBlockMinus j u := by
  ext x
  simp only [claimBox, boxSet, sideLen, escBlockMinus, mem_ofPred_eq, mem_Icc]
  constructor
  · intro h
    refine ⟨?_, fun c hc => ?_⟩
    · have := h 0
      simp only [Fin.val_zero, ite_true] at this
      push_cast at this
      omega
    · have := h c
      have hc' : c.val ≠ 0 := fun h0 => hc (Fin.ext (by simpa using h0))
      simp only [hc', ite_false] at this
      push_cast at this
      omega
  · rintro ⟨h0, hc⟩ i
    by_cases hi : i.val = 0
    · have : i = 0 := Fin.ext (by simpa using hi)
      subst this
      simp only [Fin.val_zero, ite_true]
      push_cast
      omega
    · have hi' : i ≠ 0 := fun h => hi (by simp [h])
      simp only [hi, ite_false]
      push_cast
      have := hc i hi'
      omega

theorem EscG_zero_iff (β : ℝ) {k : ℕ} (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t : ℝ)
    (y : ℝ → Fin (k + 2) → ℤ) : EscG β j u v z t y 0 ↔ EscB0 β j u v z t y := by
  unfold EscG
  exact ⟨fun h => h.1, fun h => ⟨h, fun i' h1 h2 => by omega⟩⟩

theorem claimFv_eq {k : ℕ} (j : ℕ) (u v z : Fin (k + 2) → ℤ) (t s : ℝ) (hs : s ≤ t / 2) :
    claimFv j u t v s = escCurve j u v z t s := by
  funext i
  simp only [escCurve, es56F, hs, ite_true, claimFv, claimQ, escCentre, escCast, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have : (i.val = 0) ↔ (i = 0) := ⟨fun h => Fin.ext (by simpa using h), fun h => by simp [h]⟩
  simp only [this]
  ring

theorem claim56Geom_of {k : ℕ} {j : ℕ} {β t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β)
    (hj : 1 ≤ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j) (hsb : Real.sqrt β ≤ t)
    (hm3 : 3 ≤ escPhaseM β t) : Claim56Geom (k + 2) j t (escPhaseM β t) := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hS : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  have h4 := four_pow_m_le hβ0 hsb
  have hpm : (0 : ℝ) < 4 ^ escPhaseM β t := by positivity
  have e1 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e2 : (4 : ℝ) ^ j = 4 * 4 ^ (j - 1) := by
    obtain ⟨i0, rfl⟩ : ∃ i0, j = i0 + 1 := ⟨j - 1, by omega⟩
    simp [pow_succ]; ring
  refine ⟨by omega, hj, by rw [e1]; linarith, by rw [e1]; exact ht2, hm3, ?_, ?_⟩
  · nlinarith
  · apply Real.le_sqrt_of_sq_le
    unfold claimTau
    have : Real.sqrt β ≤ t / 4 ^ escPhaseM β t := by rw [le_div_iff₀ hpm]; linarith
    nlinarith

theorem rho_zero_eq_claimR0 {t : ℝ} (_ht : 0 ≤ t) (m : ℕ) : es56Rho t m 0 = claimR0 m t := by
  rw [rho_of_le (Nat.zero_le _), Nat.sub_zero]
  unfold claimR0 claimTau
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have h22 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hs : Real.sqrt t = 2 ^ m * Real.sqrt (t / 4 ^ m) := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 ^ m by positivity), ← Real.sqrt_mul (by positivity), h22]
    congr 1; field_simp
  rw [hs, pow_add]
  have : (2 : ℝ) ^ 5 = 32 := by norm_num
  rw [this]
  have hm : (0 : ℝ) < 2 ^ m := by positivity
  field_simp

section Point0

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- **Phase `0`, pointwise.** -/
theorem phase0_pointwise {N : Ω → Measure (CycS ℕ (k + 2) β)} {ω : Ω} {j : ℕ}
    {u v z : Fin (k + 2) → ℤ} (_hgeom : EscGeom j u v z) {t : ℝ} (_hβ : (2 : ℝ) ^ 40 ≤ β)
    (hsb : Real.sqrt β ≤ t) (_ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (hm3 : 3 ≤ escPhaseM β t)
    (hS1a : ∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau (escPhaseM β t) t → v + escW N ω s ∈ claimBox u j)
    (hS1b : ∀ s : ℝ≥0, 0.5 * claimTau (escPhaseM β t) t ≤ s →
      (s : ℝ) ≤ 0.6 * claimTau (escPhaseM β t) t →
      ‖(fun i => (((v + escW N ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤
        claimR0 (escPhaseM β t) t)
    (hS2 : ∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau (escPhaseM β t) t →
      ‖escW N ω s‖ < β ^ (0.3 : ℝ))
    (hS3 : ENNReal.ofReal (9 / 10 * (0.6 * claimTau (escPhaseM β t) t)) ≤
      volume {s : ℝ | s ∈ Icc 0 (0.6 * claimTau (escPhaseM β t) t) ∧
        IsRelaxedTimeWrt β (fun r => escW N ω r.toNNReal) 0 s}) :
    EscB0 β j u v z t (escYv N v ω) := by
  have hβ0 : 0 < β := Fact.out
  have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 hβ0) hsb
  set m := escPhaseM β t with hm
  set τ := claimTau m t with hτ
  have hpm : (0 : ℝ) < 4 ^ m := by positivity
  have hτ0 : 0 < τ := div_pos ht0 hpm
  have hb0 : es56B t m 0 = 0.6 * τ := by
    unfold es56B; rw [ite_eq_left (Nat.zero_le _), Nat.sub_zero]; simp only [hτ, claimTau]; ring
  have ha0 : escPhaseA t m 0 = 0.5 * τ := by
    unfold escPhaseA; rw [ite_eq_left (Nat.zero_le _), Nat.sub_zero]; simp only [hτ, claimTau]
    field_simp; norm_num
  have h64 : (64 : ℝ) ≤ 4 ^ m := by
    calc (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hm3
  have hτt : τ ≤ t / 64 := by
    simp only [hτ, claimTau]; exact div_le_div_of_nonneg_left ht0.le (by norm_num) h64
  -- a relaxed time in the window
  obtain ⟨r, hr, hrrel⟩ := exists_relaxed_of_volume (β := β) (fun r => escW N ω r.toNNReal)
    (Ti := 0.6 * τ) (lo := 0.5 * τ) (by positivity) (by linarith) (by linarith) hS3
  have hrel : IsRelaxedTimeWrt β (escYv N v ω) 0 r := by
    have := (isRelaxedTimeWrt_add_const (β := β) v (fun r => escW N ω r.toNNReal) 0 r).2 hrrel
    exact this
  have hmem : r ∈ relaxedSet β (escYv N v ω) 0 := ⟨by linarith [hr.1], hrel⟩
  have hz0 : escZeta β (escYv N v ω) t m 0 = escZetaStep β (escYv N v ω) (escPhaseA t m 0)
      (es56B t m 0) 0 := rfl
  obtain ⟨hlt, hle⟩ := escZetaStep_lt_of_exists (lo := escPhaseA t m 0) (hi := es56B t m 0) hmem
    (by rw [ha0]; exact hr.1)
    (by rw [hb0]; exact hr.2)
  have hzm := escZeta_mem β (escYv N v ω) ht0.le m 0
  refine ⟨by rw [← hz0] at hlt; exact hlt, ?_, ?_⟩
  · intro s hs0 hs
    have hsz : s ≤ 0.6 * τ := by
      have : escZeta β (escYv N v ω) t m 0 < 0.6 * τ := by rw [← hb0]; rw [← hz0] at hlt; exact hlt
      linarith
    have hsnn : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0
    have h1 := hS1a s.toNNReal (by rw [hsnn]; exact hsz)
    rw [claimBox_eq] at h1
    have hy : escYv N v ω s = v + escW N ω s.toNNReal := rfl
    refine ⟨by rw [hy]; exact h1, ?_⟩
    have h2 := hS2 s.toNNReal (by rw [hsnn]; exact hsz)
    have : escCast (escYv N v ω s) - escCast v = escCast (escW N ω s.toNNReal) := by
      rw [hy]; ext c; simp [escCast]
    rw [this]
    have h3 : ‖escCast (escW N ω s.toNNReal)‖ = ‖escW N ω s.toNNReal‖ := norm_escCast _
    rw [h3]; exact h2.le
  · have hsz : escZeta β (escYv N v ω) t m 0 < 0.6 * τ := by
      rw [← hb0]; rw [← hz0] at hlt; exact hlt
    have hza : 0.5 * τ ≤ escZeta β (escYv N v ω) t m 0 := by rw [← ha0]; exact hzm.1
    set ζ := escZeta β (escYv N v ω) t m 0 with hζ
    have hζ0 : 0 ≤ ζ := by linarith
    have hsnn : ((ζ.toNNReal : ℝ≥0) : ℝ) = ζ := Real.coe_toNNReal _ hζ0
    have h1 := hS1b ζ.toNNReal (by rw [hsnn]; exact hza) (by rw [hsnn]; exact hsz.le)
    rw [hsnn] at h1
    have hfv := claimFv_eq j u v z t ζ (by linarith)
    have hy : escYv N v ω ζ = v + escW N ω ζ.toNNReal := rfl
    rw [hy, rho_zero_eq_claimR0 ht0.le m]
    rw [hfv] at h1
    exact h1

section Prob0


/-- **Phase `0`.** -/
theorem phase0_prob {n₀ n : ℕ} {t₀ : ℝ} {Ω' : Type} (𝒢₀ : MeasurableSpace Ω')
    [mΩ' : MeasurableSpace Ω'] {Pr : Measure Ω'} {N N' : Ω' → Measure (CycS ℕ (k + 2) β)}
    (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') {j : ℕ}
    {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β)
    (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (hjn : (4 : ℝ) ^ j ≤ 4 ^ n) (hsb : Real.sqrt β ≤ t) (hm3 : 3 ≤ escPhaseM β t)
    (hn0 : (4 : ℝ) ^ n₀ < 0.6 * claimTau (escPhaseM β t) t) (η ε1 : ℝ)
    (hη : Real.exp (-((avoidLevel (0.6 * claimTau (escPhaseM β t) t) : ℕ) : ℝ) ^ 2) ≤ η)
    (hε1 : 4 * ((k + 2 : ℕ) : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 /
      (8 * (((0.6 * claimTau (escPhaseM β t) t).toNNReal : ℝ≥0) : ℝ))) (β ^ (0.3 : ℝ) / 2)) ≤ ε1)
    (hsmall : ε1 + η ≤ cBox ^ (201 * (k + 2)) /
      (2 * Real.sqrt (claimTau (escPhaseM β t) t)) ^ (201 * (k + 2) * CBox) / 2) :
    ENNReal.ofReal (cBox ^ (201 * (k + 2)) /
      (2 * Real.sqrt (claimTau (escPhaseM β t) t)) ^ (201 * (k + 2) * CBox) / 2) ≤
      Pr {ω : Ω' | EscG β j u v z t (escYv N v ω) 0} := by
  have := S.space.ppp.isProbabilityMeasure
  have hβ0 : 0 < β := Fact.out
  have ht0 : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 hβ0) hsb
  set m := escPhaseM β t with hm
  set τ := claimTau m t with hτ
  have hpm : (0 : ℝ) < 4 ^ m := by positivity
  have hτ0 : 0 < τ := div_pos ht0 hpm
  have hS20 : (2 : ℝ) ^ 20 ≤ Real.sqrt β := by
    apply Real.le_sqrt_of_sq_le
    calc ((2 : ℝ) ^ 20) ^ 2 = 2 ^ 40 := by rw [← pow_mul]
      _ ≤ β := hβ
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  have hlt4 := lt_four_pow_m_succ hβ0 hsb
  rw [pow_succ] at hlt4
  have hτ4 : τ < 4 * Real.sqrt β := by
    simp only [hτ, claimTau]; rw [div_lt_iff₀ hpm]; linarith
  have hτβ : 0.6 * τ ≤ β := by nlinarith
  set R : ℝ≥0 := (0.6 * τ).toNNReal with hRdef
  have hRc : (R : ℝ) = 0.6 * τ := Real.coe_toNNReal _ (by positivity)
  have hR0 : 0 < R := by
    rw [← NNReal.coe_pos, hRc]; positivity
  have hv : v ∈ claimBox u j := by rw [claimBox_eq]; exact hgeom.hvm
  have G := claim56Geom_of (k := k) hβ (by have := hgeom.hj; omega) ht1 ht2 hsb hm3
  have hlaw := stopped_regen_law S.space.ppp (R := R) (by rw [hRc]; exact hτβ)
  have hS1 := claim56_B0_stopped (P := Pr) (Z := fun ω => escW N ω) G u v hv R
    (by rw [hRc]) (measurable_escW_stop S.space.ppp R) (fun ω => regular_escW_stop ω R) hlaw
  set a : ℝ := β ^ (0.3 : ℝ) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hβ0.le _
  -- the maximal bound
  have hS2 : Pr {ω | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖escW N ω s‖} ≤ ENNReal.ofReal ε1 :=
    (prob_max_regen S.space.ppp (R := R) (by rw [hRc]; exact hτβ) hR0 ha0).trans
      (ENNReal.ofReal_le_ofReal hε1)
  -- the relaxed-path bound
  have hT0n : 0.6 * τ ≤ (4 : ℝ) ^ n := by
    have : t ≤ (4 : ℝ) ^ n := ht2.trans hjn
    have h1 : τ ≤ t := by
      simp only [hτ, claimTau]
      have : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
      rw [div_le_iff₀ hpm]; nlinarith
    linarith
  have hrel := relPathSet_prob (N := N) S.params S.space.ppp hn0 hT0n
  have hNg := measurable_avoidPath_cycNgood S.space.ppp.measurable
  have hXm := measurable_escCPath hNg
  have hrelm : MeasurableSet (relPathSet (k := k) β (0.6 * τ)) :=
    measurableSet_relPathSet hβ0 _
  set E3 : Set Ω' := {ω | escCPath N ω ∈ relPathSet β (0.6 * τ)} with hE3
  have hE3m : MeasurableSet E3 := hXm hrelm
  have hη0 : 0 ≤ η := le_trans (Real.exp_pos _).le hη
  have hE3c : Pr E3ᶜ ≤ ENNReal.ofReal η := by
    rw [prob_compl_eq_one_sub hE3m]
    set e := Real.exp (-((avoidLevel (0.6 * τ) : ℕ) : ℝ) ^ 2) with he
    have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ((avoidLevel (0.6 * τ) : ℕ) : ℝ)])
    have h1 : ENNReal.ofReal (1 - e) ≤ Pr E3 := hrel
    calc 1 - Pr E3 ≤ 1 - ENNReal.ofReal (1 - e) := tsub_le_tsub_left h1 _
      _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]; congr 1; ring
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hη
  -- the inclusion
  set c0 : ℝ := cBox ^ (201 * (k + 2)) /
    (2 * Real.sqrt (claimTau (escPhaseM β t) t)) ^ (201 * (k + 2) * CBox) with hc0
  have hsub : {ω | (∀ s : ℝ≥0, (s : ℝ) ≤ 0.6 * claimTau m t → v + escW N ω s ∈ claimBox u j) ∧
        ∀ s : ℝ≥0, 0.5 * claimTau m t ≤ s → (s : ℝ) ≤ 0.6 * claimTau m t →
          ‖(fun i => (((v + escW N ω s) i : ℤ) : ℝ)) - claimFv j u t v s‖ ≤ claimR0 m t} ⊆
      {ω | EscG β j u v z t (escYv N v ω) 0} ∪
        ({ω | ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖escW N ω s‖} ∪ E3ᶜ) := by
    intro ω hω
    by_cases h2 : ∃ s : ℝ≥0, s ≤ R ∧ a ≤ ‖escW N ω s‖
    · exact Or.inr (Or.inl h2)
    by_cases h3 : ω ∈ E3
    swap
    · exact Or.inr (Or.inr h3)
    left
    rw [mem_ofPred_eq, EscG_zero_iff]
    push Not at h2
    refine phase0_pointwise hgeom hβ hsb ht1 hm3 hω.1 hω.2
      (fun s hs => h2 s (by rw [← NNReal.coe_le_coe, hRc]; exact hs)) ?_
    -- the relaxed measure
    have hh : escCPath N ω ∈ relPathSet β (0.6 * τ) := h3
    rcases hh with hcl | hrm
    · exfalso
      obtain ⟨i, hi, -⟩ := hcl
      have : ⌊0.6 * τ / β⌋₊ = 0 := Nat.floor_eq_zero.2 ((div_lt_one hβ0).2 (by nlinarith))
      rw [this] at hi
      simp at hi
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hrm
      have : (0 : ℝ) ≤ 1 / (scaleIndex (0.6 * τ) : ℝ) := by positivity
      nlinarith
  have hmain : ENNReal.ofReal c0 ≤ Pr {ω : Ω' | EscG β j u v z t (escYv N v ω) 0} +
      (ENNReal.ofReal ε1 + ENNReal.ofReal η) := by
    refine hS1.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_))
    gcongr
    exact (measure_union_le _ _).trans (add_le_add hS2 hE3c)
  have hε10 : 0 ≤ ε1 := le_trans (by positivity) hε1
  rw [← ENNReal.ofReal_add hε10 hη0] at hmain
  have : ENNReal.ofReal (c0 / 2) ≤ ENNReal.ofReal c0 - ENNReal.ofReal (ε1 + η) := by
    rw [← ENNReal.ofReal_sub _ (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact this.trans (tsub_le_iff_right.2 hmain)

end Prob0

end Point0

end ElboimSly.Paper.Escape

end
