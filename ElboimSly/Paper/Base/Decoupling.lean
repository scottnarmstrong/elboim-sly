/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.DecouplingCount
public import ElboimSly.Paper.Base.ContactMain
public import Mathlib

/-!
# Decoupling the second particle

Decoupling the second particle (ES22 §8).

In the setting of contacts are few, let `T > 0`, `n ≥ 1`, `k ∈ ℕ`.  Then `b + X₂` is an SRW
started at `b`, independent of `a + X₁`, and
`P(sup_{s ∈ [0,T]} ‖y(s) - b - X₂(s)‖ > 2 n⁵ k) ≤ (1 - c₁)^k + 2(T+1) e^{4d(e-1) - n⁵}`.
The event is measurable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

omit [MeasurableSpace Ω] in
theorem kap_ne_top_of_le (a b : Fin d → ℤ) {m m' : ℕ} (hm : m ≤ m') {ω : Ω}
    (h : kap Ñ a b m' ω ≠ ⊤) : kap Ñ a b m ω ≠ ⊤ := by
  induction m', hm using Nat.le_induction with
  | base => exact h
  | succ m' hm' ih => exact ih (kap_succ_ne_top a b m' h)

omit [MeasurableSpace Ω] in
/-- The number of contacts before time `s` is at most `2 n⁵ k`. -/
theorem ncard_contactSet_le (a b : Fin d → ℤ) (_hab : a ≠ b) {ω : Ω} (hG : ω ∈ drvGood Ñ)
    {T : ℝ≥0} {n k : ℕ} (hH : ω ∈ windowsOK Ñ T n) (hk : kap Ñ a b k ω = ⊤) {s : ℝ≥0}
    (hs : s ≤ T) :
    (contactSet a (drvX Ñ 0 ω) (drvX Ñ 1 ω) (drvTwo Ñ a b ω) s).ncard ≤ 2 * n ^ 5 * k := by
  have hdat := drvData hG a b
  set C := contactSet a (drvX Ñ 0 ω) (drvX Ñ 1 ω) (drvTwo Ñ a b ω) s with hC
  have hCfin : C.Finite := contactSet_finite hdat s
  set J : ℕ → Set ℝ≥0 := fun m => {r | r ∈ C ∧ kap Ñ a b m ω ≠ ⊤ ∧
    stopReal (kap Ñ a b m) ω < r ∧ r ≤ stopReal (kap Ñ a b m) ω + 1} with hJ
  have hcov : C ⊆ ⋃ m ∈ Finset.range k, J m := by
    intro r hr
    obtain ⟨hr0, hrs, hl1, hjump⟩ := hr
    obtain ⟨m, hm, hm1, hm2⟩ := exists_kap_of_l1_leftLim a b ω hr0 hl1
    have hmk : m < k := by
      by_contra hmk
      push Not at hmk
      exact (kap_ne_top_of_le a b hmk hm) hk
    simp only [mem_iUnion, Finset.mem_range]
    exact ⟨m, hmk, ⟨hr0, hrs, hl1, hjump⟩, hm, hm1, hm2⟩
  have hJb : ∀ m, (J m).ncard ≤ 2 * n ^ 5 := by
    intro m
    rcases (J m).eq_empty_or_nonempty with he | ⟨r, hr⟩
    · rw [he]; simp
    · obtain ⟨⟨hr0, hrs, hl1, hjump⟩, hm, hm1, hm2⟩ := hr
      set κ := stopReal (kap Ñ a b m) ω with hκ
      have hκT : κ ≤ T := (hm1.le.trans hrs).trans hs
      set l := ⌊κ⌋₊ with hl
      have hlκ : (l : ℝ≥0) ≤ κ := Nat.floor_le bot_le
      have hκl : κ < l + 1 := Nat.lt_floor_add_one κ
      have hsub : J m ⊆ (CDisc (drvX Ñ 0 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)) ∪
          (CDisc (drvX Ñ 1 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)) := by
        rintro r' ⟨⟨hr'0, hr's, hl1', hj'⟩, -, hm1', hm2'⟩
        have h1 : (l : ℝ≥0) < r' := hlκ.trans_lt hm1'
        have h2 : r' ≤ (l : ℝ≥0) + 2 := by
          refine hm2'.trans ?_
          have : κ + 1 ≤ (l : ℝ≥0) + 1 + 1 := by gcongr
          calc κ + 1 ≤ (l : ℝ≥0) + 1 + 1 := this
            _ = (l : ℝ≥0) + 2 := by ring
        rcases hj' with hj | hj
        · exact Or.inl ⟨hj, h1, h2⟩
        · exact Or.inr ⟨hj, h1, h2⟩
      have hfin0 : (CDisc (drvX Ñ 0 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)).Finite :=
        (hdat.hx₁.step.fin ((l : ℝ≥0) + 2)).subset
          (inter_subset_inter_right _ Ioc_subset_Iic_self)
      have hfin1 : (CDisc (drvX Ñ 1 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)).Finite :=
        (hdat.hx₂.step.fin ((l : ℝ≥0) + 2)).subset
          (inter_subset_inter_right _ Ioc_subset_Iic_self)
      have hlT : (l : ℝ≥0) ≤ T := hlκ.trans hκT
      calc (J m).ncard ≤ ((CDisc (drvX Ñ 0 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)) ∪
            (CDisc (drvX Ñ 1 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2))).ncard :=
            Set.ncard_le_ncard hsub (hfin0.union hfin1)
        _ ≤ (CDisc (drvX Ñ 0 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)).ncard +
            (CDisc (drvX Ñ 1 ω) ∩ Ioc (l : ℝ≥0) ((l : ℝ≥0) + 2)).ncard := Set.ncard_union_le _ _
        _ ≤ n ^ 5 + n ^ 5 := by
            refine add_le_add ((ncard_jumps_le_winCount hG 0 l).trans (hH l hlT 0))
              ((ncard_jumps_le_winCount hG 1 l).trans (hH l hlT 1))
        _ = 2 * n ^ 5 := by ring
  have hUfin : (⋃ m ∈ Finset.range k, J m).Finite :=
    hCfin.subset (iUnion₂_subset fun m _ r hr => hr.1)
  calc C.ncard ≤ (⋃ m ∈ Finset.range k, J m).ncard := Set.ncard_le_ncard hcov hUfin
    _ ≤ ∑ m ∈ Finset.range k, (J m).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _m ∈ Finset.range k, 2 * n ^ 5 := Finset.sum_le_sum fun m _ => hJb m
    _ = 2 * n ^ 5 * k := by simp [mul_comm]

/-- The bad event `sup_{s ≤ T} ‖y(s) - b - X₂(s)‖ > 2 n⁵ k`. -/
def decoupBad (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a b : Fin d → ℤ) (T : ℝ≥0) (n k : ℕ) :
    Set Ω :=
  {ω | ∃ s : ℝ≥0, s ≤ T ∧ ((2 * n ^ 5 * k : ℕ) : ℝ) <
    ‖drvTwo Ñ a b ω s - b - drvX Ñ 1 ω s‖}

section

variable [NeZero d] (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
include h

omit [NeZero d] in
theorem measurableSet_decoupBad (a b : Fin d → ℤ) (T : ℝ≥0) (n k : ℕ) :
    MeasurableSet (decoupBad Ñ a b T n k) := by
  set Z : Ω → PathSpace d := fun ω s => drvTwo Ñ a b ω s - b - drvX Ñ 1 ω s with hZ
  have hm : ∀ s, Measurable fun ω => Z ω s := fun s =>
    (measurable_sub_gen (m := inferInstance)
      ((drvTwo_adapted h a b s).mono (natFil_le (measurable_drvPair h) s) le_rfl)
      (measurable_pi_apply s |>.comp (measurable_drvX h 1)) b)
  have hreg : ∀ ω, IsRegularPath (Z ω) := fun ω =>
    isRegularPath_of_isStepPath (isStepPath_comp₂ (fun u v => u - v)
      (isStepPath_comp₂ (fun u v => u - v) (isTwoParticle_drvTwo a b ω).step (isStepPath_const b))
      (drivers_isDrivingPath 1 ω).step)
  have := measurableSet_exists_Icc hm hreg {z : Fin d → ℤ | ((2 * n ^ 5 * k : ℕ) : ℝ) < ‖z‖}
    (a := 0) (b := T) bot_le
  convert this using 1
  ext ω
  simp [decoupBad, hZ]

/-- Decoupling the second particle. -/
theorem es8_decoupling (hd : 3 ≤ d) (a b : Fin d → ℤ) (hab : a ≠ b) (T : ℝ≥0) (n k : ℕ) :
    (IsSRW P (drvX Ñ 1) ∧ IndepFun (drvX Ñ 0) (drvX Ñ 1) P) ∧
    MeasurableSet (decoupBad Ñ a b T n k) ∧
    P (decoupBad Ñ a b T n k) ≤ ENNReal.ofReal ((1 - es8C1 d) ^ k +
      2 * ((T : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)) := by
  refine ⟨⟨drivers_isSRW h 1, (drivers_indep h).indepFun (by decide : (0 : Fin 2) ≠ 1)⟩,
    measurableSet_decoupBad h a b T n k, ?_⟩
  have := (drivers_isSRW h 0).isProbabilityMeasure
  have hsub : decoupBad Ñ a b T n k ≤ᵐ[P] (windowsOK Ñ T n)ᶜ ∪ {ω | kap Ñ a b k ω < ⊤} := by
    filter_upwards [drivers_ae_good h] with ω hG hω
    obtain ⟨s, hsT, hs⟩ := hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not, not_lt, top_le_iff] at hcon
    obtain ⟨hH, hk⟩ := hcon
    have hdat := drvData hG a b
    have h1 := hdat.norm_E_le hab s
    have h2 := ncard_contactSet_le a b hab hG hH hk hsT
    have h3 : (((contactSet a (drvX Ñ 0 ω) (drvX Ñ 1 ω) (drvTwo Ñ a b ω) s).ncard : ℕ) : ℝ) ≤
        ((2 * n ^ 5 * k : ℕ) : ℝ) := by exact_mod_cast h2
    exact absurd hs (not_lt.2 (h1.trans h3))
  calc P (decoupBad Ñ a b T n k) ≤ P ((windowsOK Ñ T n)ᶜ ∪ {ω | kap Ñ a b k ω < ⊤}) :=
        measure_mono_ae hsub
    _ ≤ P (windowsOK Ñ T n)ᶜ + P {ω | kap Ñ a b k ω < ⊤} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * ((T : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5)) +
        ENNReal.ofReal ((1 - es8C1 d) ^ k) := add_le_add (prob_windows h T n) (prob_kap_le h hd a b hab k)
    _ = _ := by
        rw [add_comm, ← ENNReal.ofReal_add (pow_nonneg (sub_nonneg.2 (es8C1_lt_one d).le) _)
          (by have := Real.exp_pos (4 * d * (Real.exp 1 - 1) - (n : ℝ) ^ 5); positivity)]

end

end ElboimSly.Paper
