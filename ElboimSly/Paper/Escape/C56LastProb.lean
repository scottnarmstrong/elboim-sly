/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Last2
public import ElboimSly.Paper.Escape.C56Zero
public import ElboimSly.Paper.Escape.C56Phase
public import Mathlib

/-!
# ES22 Claim 5.6, phase `2m+1`: the probability

ES22 Claim 5.6, "Phase `2m+1`", ES22 Claim 5.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.SRW ElboimSly.Brownian

variable {k : ℕ}

/-- The event `E^e` of the last phase, as a set of `((x, a'), p)`. -/
def lastFam (β : ℝ) (j : ℕ) (u z : Fin (k + 2) → ℤ) (t : ℝ) :
    Set (((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ)) :=
  {q | q.1.1 + q.2.fn (t - q.1.2).toNNReal = z ∧
    ∀ s : ℝ, 0 ≤ s → s ≤ t - q.1.2 →
      (q.1.1 + q.2.fn s.toNNReal ∈ escBlockMinus j u ∧ ‖q.2.fn s.toNNReal‖ ≤ β ^ (0.3 : ℝ))}

theorem measurableSet_lastFam (β : ℝ) (j : ℕ) (u z : Fin (k + 2) → ℤ) (t : ℝ) :
    MeasurableSet (lastFam β j u z t) := by
  have h1 : Measurable (fun q : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) =>
      q.1.1 + q.2.fn (t - q.1.2).toNNReal) := by
    have h := measurable_fn_at (fun q : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) => q.2)
      measurable_snd (fun q => (t - q.1.2).toNNReal)
      ((measurable_const.sub (measurable_snd.comp measurable_fst)).real_toNNReal)
    exact (measurable_of_countable (fun p : (Fin (k + 2) → ℤ) × (Fin (k + 2) → ℤ) => p.1 + p.2)).comp
      ((measurable_fst.comp measurable_fst).prodMk h)
  have hA : MeasurableSet {q : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
      q.1.1 + q.2.fn (t - q.1.2).toNNReal = z} := h1 (measurableSet_singleton z)
  have hB : MeasurableSet {q : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
      ∀ s : ℝ, 0 ≤ s → s ≤ t - q.1.2 →
        (q.1.1 + q.2.fn s.toNNReal ∈ escBlockMinus j u ∧ ‖q.2.fn s.toNNReal‖ ≤ β ^ (0.3 : ℝ))} := by
    have e : {q : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) |
        ∀ s : ℝ, 0 ≤ s → s ≤ t - q.1.2 →
          (q.1.1 + q.2.fn s.toNNReal ∈ escBlockMinus j u ∧ ‖q.2.fn s.toNNReal‖ ≤ β ^ (0.3 : ℝ))} =
        ⋃ x : Fin (k + 2) → ℤ, ({q | q.1.1 = x} ∩
          (fun q : ((Fin (k + 2) → ℤ) × ℝ) × CPath (Fin (k + 2) → ℤ) =>
            (q.2, (0 : ℝ), t - q.1.2)) ⁻¹'
            forallBetween (fun y _ => x + y ∈ escBlockMinus j u ∧ ‖y‖ ≤ β ^ (0.3 : ℝ))) := by
      ext q
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, forallBetween]
      constructor
      · intro h; exact ⟨q.1.1, rfl, h⟩
      · rintro ⟨x, hx, h⟩ s hs0 hs
        rw [hx]; exact h s hs0 hs
    rw [e]
    refine MeasurableSet.iUnion fun x => MeasurableSet.inter ?_ ?_
    · exact (measurable_fst.comp measurable_fst) (measurableSet_singleton x)
    · refine ((measurable_snd.prodMk (measurable_const.prodMk
        (measurable_const.sub (measurable_snd.comp measurable_fst)))))
        (measurableSet_forallBetween _ fun y => ?_)
      by_cases h : x + y ∈ escBlockMinus j u ∧ ‖y‖ ≤ β ^ (0.3 : ℝ)
      · simp only [h, and_self, ofPred_true]; exact isClosed_univ
      · simp only [h, ofPred_false]; exact isClosed_empty
  exact hA.inter hB

theorem claimFw_eq (j : ℕ) (u v z : Fin (k + 2) → ℤ) {t s : ℝ} (ht : 0 < t) (hs : t / 2 ≤ s) :
    claimFw j u t z s = escCurve j u v z t s := by
  unfold escCurve
  rw [es56F_of_ge ht hs]
  funext i
  simp only [claimFw, claimQ, escCentre, escCast, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  have : (i.val = 0) ↔ (i = 0) := ⟨fun h => Fin.ext (by simpa using h), fun h => by simp [h]⟩
  simp only [this]
  ring

theorem escR_two_m_le_rho_zero {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : 1 ≤ m) :
    escR t m (2 * m) ≤ es56Rho t m 0 := by
  unfold escR escKappa
  rw [ite_eq_left (by omega), rho_of_gt (by omega : m < 2 * m), rho_of_le (Nat.zero_le _)]
  have e : 2 * m - m + 3 = m + 3 := by omega
  rw [e, Nat.sub_zero]
  have hs := Real.sqrt_pos.2 ht
  have h4 : (2 : ℝ) ^ (m + 5) = 2 ^ (m + 3) * 4 := by
    rw [show m + 5 = (m + 3) + 2 by ring, pow_add]; norm_num
  rw [h4, ← div_div]
  have hX : 0 < Real.sqrt t / 2 ^ (m + 3) := by positivity
  linarith

section Slice

variable {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS ℕ (k + 2) β)}

/-- **The slice bound of the last phase.** -/
theorem last_slice (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr) {j : ℕ}
    {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β)
    (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (hm3 : 3 ≤ escPhaseM β t) {a' : ℝ}
    (hT1 : t - 0.5 * claimTau (escPhaseM β t) t ≤ a')
    (hT2 : a' ≤ t - 0.3 * claimTau (escPhaseM β t) t) (x : Fin (k + 2) → ℤ)
    (hx : ‖escCast x - escCurve j u v z t a'‖ ≤ 24 / 100 * escR t (escPhaseM β t) (2 * escPhaseM β t))
    (ε2 : ℝ) (hε2 : 4 * ((k + 2 : ℕ) : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 /
      (8 * (((t - a').toNNReal : ℝ≥0) : ℝ))) (β ^ (0.3 : ℝ) / 2)) ≤ ε2) :
    ENNReal.ofReal (cBox ^ (k + 2) / (3 * Real.sqrt (claimTau (escPhaseM β t) t)) ^
        ((k + 2) * CBox) - ε2) ≤
      Pr {ω | escCPath N ω ∈ {p | ((x, a'), p) ∈ lastFam β j u z t}} := by
  have := hN.isProbabilityMeasure
  have hβ0 : 0 < β := Fact.out
  obtain ⟨hS, hsβ, hSj⟩ := sqrt_facts (by have := hgeom.hj; omega) hβ hβj ht1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  set m := escPhaseM β t with hm
  set τ := claimTau m t with hτ
  have hpm : (0 : ℝ) < 4 ^ m := by positivity
  have hlt4 := lt_four_pow_m_succ hβ0 hsβ
  rw [pow_succ] at hlt4
  have hτ4 : τ < 4 * Real.sqrt β := by
    simp only [hτ, claimTau]; rw [div_lt_iff₀ hpm]; linarith
  have hτ0 : 0 < τ := div_pos ht0 hpm
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ0.le
  set R : ℝ≥0 := (t - a').toNNReal with hRdef
  have hRc : (R : ℝ) = t - a' := Real.coe_toNNReal _ (by nlinarith)
  have hR0 : 0 < R := by rw [← NNReal.coe_pos, hRc]; nlinarith
  have hRβ : (R : ℝ) ≤ β := by rw [hRc]; nlinarith
  have G := claim56Geom_of (k := k) hβ (by have := hgeom.hj; omega) ht1 ht2 hsβ hm3
  have h64 : (64 : ℝ) ≤ 4 ^ m := by
    calc (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hm3
  have hτt : τ ≤ t / 64 := by
    simp only [hτ, claimTau]; exact div_le_div_of_nonneg_left ht0.le (by norm_num) h64
  -- the kernel lower bound
  have hker := claim56_B2m1 (d := k + 2) G u z
    (fun i hi => by
      have : i = 0 := Fin.ext (by simpa using hi)
      subst this; exact hgeom.z0)
    (fun i hi => by
      have hi' : i ≠ 0 := fun h => hi (by simp [h])
      have := hgeom.zc hi'
      constructor <;> linarith [this.1, this.2])
    (T' := R) (by rw [hRc]; linarith) (by rw [hRc]; linarith) (x := x) (by
      have h1 : claimFw j u t z (t - R) = escCurve j u v z t a' := by
        rw [hRc, sub_sub_cancel]
        exact claimFw_eq j u v z ht0 (by linarith)
      rw [h1]
      refine hx.trans ?_
      rw [← rho_zero_eq_claimR0 ht0.le m]
      have := escR_two_m_le_rho_zero ht0 (m := m) (by omega)
      have := escR_pos ht0 m (2 * m)
      linarith)
  have hkerP := prob_ker_regen hN hRβ (claimBox u j) x z
  have ha0 : 0 ≤ β ^ (0.3 : ℝ) := Real.rpow_nonneg hβ0.le _
  have hmax := (prob_max_regen hN hRβ hR0 ha0).trans (ENNReal.ofReal_le_ofReal hε2)
  have hsub : {ω | escW N ω ∈ kerSet (claimBox u j) R x z} ⊆
      {ω | escCPath N ω ∈ {p | ((x, a'), p) ∈ lastFam β j u z t}} ∪
        {ω | ∃ s : ℝ≥0, s ≤ R ∧ β ^ (0.3 : ℝ) ≤ ‖escW N ω s‖} := by
    intro ω hω
    by_cases h2 : ∃ s : ℝ≥0, s ≤ R ∧ β ^ (0.3 : ℝ) ≤ ‖escW N ω s‖
    · exact Or.inr h2
    left
    push Not at h2
    obtain ⟨hz, hQ⟩ := hω
    refine ⟨hz, fun s hs0 hs => ?_⟩
    have hsR : s.toNNReal ≤ R := Real.toNNReal_le_toNNReal (by linarith)
    refine ⟨?_, (h2 _ hsR).le⟩
    have := hQ _ hsR
    rw [claimBox_eq] at this
    exact this
  have hmain : ENNReal.ofReal (kernel (claimBox u j) R x z) ≤
      Pr {ω | escCPath N ω ∈ {p | ((x, a'), p) ∈ lastFam β j u z t}} + ENNReal.ofReal ε2 := by
    rw [← hkerP]
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hmax))
  have hε20 : 0 ≤ ε2 := le_trans (by positivity) hε2
  have hk2 : ENNReal.ofReal (cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) - ε2) ≤
      ENNReal.ofReal (kernel (claimBox u j) R x z) - ENNReal.ofReal ε2 := by
    rw [← ENNReal.ofReal_sub _ hε20]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact hk2.trans (tsub_le_iff_right.2 hmain)

end Slice

section Prob

variable {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} {𝒢₀ : MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- **Phase `2m+1`.** -/
theorem last_prob (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') {j : ℕ}
    {u v z : Fin (k + 2) → ℤ} (hgeom : EscGeom j u v z) {t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β)
    (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (hm3 : 3 ≤ escPhaseM β t) (ε2 : ℝ)
    (hε2 : ∀ T' : ℝ≥0, 0.3 * claimTau (escPhaseM β t) t ≤ T' → (T' : ℝ) ≤ 0.5 * claimTau (escPhaseM β t) t →
      4 * ((k + 2 : ℕ) : ℝ) * Real.exp (-min ((β ^ (0.3 : ℝ)) ^ 2 / (8 * (T' : ℝ)))
        (β ^ (0.3 : ℝ) / 2)) ≤ ε2)
    (hsmall : ε2 ≤ cBox ^ (k + 2) / (3 * Real.sqrt (claimTau (escPhaseM β t) t)) ^
      ((k + 2) * CBox) / 2) :
    ENNReal.ofReal (cBox ^ (k + 2) / (3 * Real.sqrt (claimTau (escPhaseM β t) t)) ^
        ((k + 2) * CBox) / 2) *
      Pr {ω | EscG β j u v z t (escYv N v ω) (2 * escPhaseM β t)} ≤
    Pr ({ω | EscG β j u v z t (escYv N v ω) (2 * escPhaseM β t)} ∩
      {ω | EscBlast β j u z t (escYv N v ω)}) := by
  have := S.space.ppp.isProbabilityMeasure
  have hβ0 : 0 < β := Fact.out
  obtain ⟨hS, hsβ, hSj⟩ := sqrt_facts (by have := hgeom.hj; omega) hβ hβj ht1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  set m := escPhaseM β t with hm
  set τ := claimTau m t with hτ
  have hZ := isStoppingTime_escZt S ht0.le m (2 * m)
  have hfin : ∀ᵐ ω ∂Pr, ((fun ω => ((escZt N t m (2 * m) ω : ℝ≥0) : WithTop ℝ≥0)) ω) ≠ ⊤ :=
    ae_of_all _ fun ω => WithTop.coe_ne_top
  obtain ⟨M, hM, ⟨hXm, hXrc, hind, hlaw⟩, hcpl⟩ := es4_couple S hZ hfin
  set A : Set Ω := {ω | EscG β j u v z t (escYv N v ω) (2 * m)} with hAdef
  have hA : MeasurableSet[hZ.measurableSpace] A := measurableSet_EscG S j u v z ht0 (2 * m)
  have hNg : Measurable (avoidPath (cycNgood N)) :=
    measurable_avoidPath_cycNgood S.space.ppp.measurable
  have hXc : Measurable (escCPath M) := measurable_escCPath hXm
  set tnf : Ω → ℝ≥0 := fun ω => escZt N t m (2 * m) ω with htnf
  have htnm : Measurable[hZ.measurableSpace] tnf := measurable_stopReal_stop hZ
  have hUx : Measurable[hZ.measurableSpace] (fun ω => v + escW N ω (tnf ω)) := by
    have h := @measurable_fn_at (Fin (k + 2) → ℤ) _ _ _ Ω hZ.measurableSpace
      (fun ω => stopP N t m (2 * m) ω) (measurable_stopP S ht0.le m (2 * m)) tnf htnm
    have e : (fun ω => (stopP N t m (2 * m) ω).fn (tnf ω)) = fun ω => escW N ω (tnf ω) := by
      funext ω; simp [stopP, CPath.stop_fn, tnf, escCPath_fn]
    rw [e] at h
    exact (measurable_of_countable (fun x : Fin (k + 2) → ℤ => v + x)).comp h
  have hU : Measurable[hZ.measurableSpace]
      (fun ω => ((v + escW N ω (tnf ω), ((tnf ω : ℝ≥0) : ℝ)))) :=
    hUx.prodMk htnm.coe_nnreal_real
  have hΓm := measurableSet_lastFam β j u z t
  have hyvat : ∀ ω, escYv N v ω ((tnf ω : ℝ≥0) : ℝ) = v + escW N ω (tnf ω) := by
    intro ω; simp [escYv, escY]
  have hq : ∀ ω ∈ A, ENNReal.ofReal (cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) - ε2) ≤
      (Pr.map (escCPath M)) {p | ((v + escW N ω (tnf ω), ((tnf ω : ℝ≥0) : ℝ)), p) ∈
        lastFam β j u z t} := by
    intro ω hω
    have hset : MeasurableSet {p : CPath (Fin (k + 2) → ℤ) |
        ((v + escW N ω (tnf ω), ((tnf ω : ℝ≥0) : ℝ)), p) ∈ lastFam β j u z t} :=
      measurable_prodMk_left hΓm
    rw [map_escCPath_eq hXm S.space.ppp hlaw,
      Measure.map_apply (measurable_escCPath hNg) hset]
    have hTmem := escZeta_mem β (escYv N v ω) ht0.le m (2 * m)
    have hz : escZeta β (escYv N v ω) t m (2 * m) = ((tnf ω : ℝ≥0) : ℝ) :=
      escZeta_yv v ht0.le ω m (2 * m)
    have hx : ‖escCast (v + escW N ω (tnf ω)) - escCurve j u v z t ((tnf ω : ℝ≥0) : ℝ)‖ ≤
        24 / 100 * escR t m (2 * m) := by
      have := (hω.2 (2 * m) (by omega) le_rfl).2.2
      rw [hz, hyvat] at this
      exact this
    have hA2 := escPhaseA_two_m (t := t) (by omega : 1 ≤ m)
    have hb2 : es56B t m (2 * m) = t - 0.3 * τ := by
      unfold es56B; rw [ite_eq_right (by omega)]
      have : 2 * m - m = m := by omega
      rw [this]; simp only [hτ, claimTau]; ring
    have hT1 : t - 0.5 * τ ≤ ((tnf ω : ℝ≥0) : ℝ) := by
      rw [← hz]; have := hTmem.1; rw [hA2] at this
      have e : t / (2 * 4 ^ m) = 0.5 * τ := by simp only [hτ, claimTau]; field_simp; norm_num
      linarith
    have hT2 : ((tnf ω : ℝ≥0) : ℝ) ≤ t - 0.3 * τ := by
      rw [← hz]; have := hTmem.2; rw [hb2] at this; exact this
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (last_slice S.space.ppp hgeom hβ hβj ht1 ht2 hm3 hT1 hT2 _ hx ε2 ?_)
    · linarith
    · have hnn : (((t - ((tnf ω : ℝ≥0) : ℝ)).toNNReal : ℝ≥0) : ℝ) = t - ((tnf ω : ℝ≥0) : ℝ) :=
        Real.coe_toNNReal _ (by linarith [hT2, show 0 < τ from div_pos ht0 (by positivity)])
      apply hε2
      · rw [hnn]; linarith
      · rw [hnn]; linarith
  have hfreeze := freeze_ge hZ.measurableSpace Pr hZ.measurableSpace_le hU hXc
    (indep_escCPath hind) hA hΓm hq
  have hε20 : ε2 ≤ cBox ^ (k + 2) / (3 * Real.sqrt τ) ^ ((k + 2) * CBox) / 2 := hsmall
  refine le_trans (by gcongr; linarith) (hfreeze.trans
    (measure_mono_ae ?_))
  filter_upwards [ae_cycNgood_eq S.space.ppp, hcpl] with ω hωN hωc hω
  obtain ⟨hωA, hωE1⟩ := hω
  refine ⟨hωA, ?_⟩
  obtain ⟨hEz, hEs⟩ := hωE1
  exact last_pointwise hωN hgeom hβ hβj ht1 ht2 hm3 (hωc (escZt N t m (2 * m) ω) rfl) hωA
    hEz (fun s hs => by simpa [Real.toNNReal_coe] using (hEs (s : ℝ) s.2 hs).1)
    (fun s hs => by simpa [Real.toNNReal_coe] using (hEs (s : ℝ) s.2 hs).2)

end Prob

end ElboimSly.Paper.Escape

end
