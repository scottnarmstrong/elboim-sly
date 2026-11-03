/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Binomial
public import ElboimSly.Foundations.StrongApprox.Gaussian

/-!
# The binomial quantile coupling

Quantile coupling function; Law, measurability and symmetry of the quantile coupling (Part I).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal Real ENNReal unitInterval

namespace ElboimSly
namespace StrongApprox

/-! ### Partial sums of `sab` -/

theorem sabF_mono (m : ℕ) : Monotone (sabF m) := by
  intro a b hab
  unfold sabF
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : (i : ℤ) ≤ a
  · simp only [h, le_trans h hab, ite_true, le_refl]
  · by_cases h2 : (i : ℤ) ≤ b
    · simp only [h, h2, ite_true, ite_false]; exact sab_nonneg m i
    · simp only [h, h2, ite_false, le_refl]

theorem sabF_of_ge (m : ℕ) {j : ℤ} (hj : (m : ℤ) ≤ j) : sabF m j = 1 := by
  unfold sabF
  rw [← sum_sab m]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : (i : ℤ) ≤ j := by
    have : i < m + 1 := Finset.mem_range.1 hi
    omega
  simp [this]

theorem sabF_of_neg (m : ℕ) {j : ℤ} (hj : j < 0) : sabF m j = 0 := by
  unfold sabF
  refine Finset.sum_eq_zero fun i _ => ?_
  have : ¬ (i : ℤ) ≤ j := by omega
  simp [this]

theorem sabF_sub (m : ℕ) (j : ℤ) : sabF m j - sabF m (j - 1) = sab m j := by
  unfold sabF
  rw [← Finset.sum_sub_distrib]
  by_cases h : 0 ≤ j ∧ j ≤ m
  · have hj : j.toNat < m + 1 := by omega
    rw [Finset.sum_eq_single j.toNat]
    · have : ((j.toNat : ℕ) : ℤ) = j := by omega
      simp [this]
    · intro i _ hne
      have : (i : ℤ) ≠ j := by omega
      by_cases h1 : (i : ℤ) ≤ j
      · have h2 : (i : ℤ) ≤ j - 1 := by omega
        simp [h1, h2]
      · have h2 : ¬ (i : ℤ) ≤ j - 1 := by omega
        simp [h1, h2]
    · intro hn; exact absurd (Finset.mem_range.2 hj) hn
  · have hs : sab m j = 0 := by unfold sab; simp [h]
    rw [hs]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < m + 1 := Finset.mem_range.1 hi
    by_cases h1 : (i : ℤ) ≤ j
    · have h2 : (i : ℤ) ≤ j - 1 := by omega
      simp [h1, h2]
    · have h2 : ¬ (i : ℤ) ≤ j - 1 := by omega
      simp [h1, h2]

theorem sabT_eq_sabF (m : ℕ) (j : ℤ) : sabT m j = sabF m (m - j) := by
  unfold sabT sabF
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := by have := Finset.mem_range.1 hk; omega
  have e : m + 1 - 1 - k = m - k := by omega
  rw [e, sab_natCast_symm hk']
  have h1 : (((m - k : ℕ) : ℤ)) = (m : ℤ) - k := by omega
  by_cases h : j ≤ (((m - k : ℕ)) : ℤ)
  · have h2 : (k : ℤ) ≤ m - j := by omega
    simp [h, h2]
  · have h2 : ¬ (k : ℤ) ≤ m - j := by omega
    simp [h, h2]

theorem sabF_symm (m : ℕ) (a : ℤ) : sabF m a + sabF m ((m : ℤ) - a - 1) = 1 := by
  have h := sabF_add_sabT m (a + 1)
  rw [sabT_eq_sabF] at h
  have e : (m : ℤ) - (a + 1) = (m : ℤ) - a - 1 := by ring
  rw [e, add_sub_cancel_right] at h
  exact h

theorem sabF_lt_of_lt {m : ℕ} {a : ℤ} (h0 : 0 ≤ a + 1) (h1 : a + 1 ≤ m) : sabF m a < sabF m (a + 1) := by
  have := sabF_sub m (a + 1)
  rw [add_sub_cancel_right] at this
  have hp := sab_pos (m := m) (j := a + 1) h0 h1
  linarith

/-! ### The quantile coupling function -/

/-- Quantile coupling function. `saq m z = min {j : ℕ | Φ(z) ≤ F m j}`. -/
noncomputable def saq (m : ℕ) (z : ℝ) : ℕ := sInf {j : ℕ | saPhi z ≤ sabF m j}

theorem saq_mem (m : ℕ) (z : ℝ) : saPhi z ≤ sabF m (saq m z) := by
  have : {j : ℕ | saPhi z ≤ sabF m j}.Nonempty :=
    ⟨m, by show saPhi z ≤ sabF m (m : ℤ); rw [sabF_of_ge m (le_refl _)]; exact (saPhi_lt_one z).le⟩
  exact Nat.sInf_mem this

/-- Quantile coupling function, `saq m z ≤ j ↔ Φ(z) ≤ F m j`. -/
theorem saq_le_iff (m : ℕ) (z : ℝ) (j : ℕ) : saq m z ≤ j ↔ saPhi z ≤ sabF m j := by
  constructor
  · intro h
    exact (saq_mem m z).trans (sabF_mono m (by exact_mod_cast h))
  · intro h
    exact Nat.sInf_le h

theorem saq_le_m (m : ℕ) (z : ℝ) : saq m z ≤ m :=
  (saq_le_iff m z m).2 (by rw [sabF_of_ge m (le_refl _)]; exact (saPhi_lt_one z).le)

/-- Quantile coupling function, `j ≤ saq m z ↔ Φ̄(z) < T m j` for integers `j`. -/
theorem le_saq_iff (m : ℕ) (z : ℝ) (j : ℤ) : j ≤ saq m z ↔ saPhib z < sabT m j := by
  have hT := sabF_add_sabT m j
  by_cases hj : j ≤ 0
  · have : sabF m (j - 1) = 0 := sabF_of_neg m (by omega)
    constructor
    · intro _
      have : sabT m j = 1 := by linarith
      rw [this]; unfold saPhib; linarith [saPhi_pos z]
    · intro _; omega
  · rw [not_le] at hj
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j - 1 by omega)
    have h1 : j = (n : ℤ) + 1 := by omega
    have := saq_le_iff m z n
    constructor
    · intro h
      have h2 : ¬ saq m z ≤ n := by omega
      rw [this, not_le] at h2
      have : sabF m ((n : ℤ)) = sabF m (j - 1) := by rw [hn]
      unfold saPhib; linarith
    · intro h
      by_contra h2
      have h3 : saq m z ≤ n := by omega
      rw [this] at h3
      have : sabF m ((n : ℤ)) = sabF m (j - 1) := by rw [hn]
      unfold saPhib at h; linarith

/-- Law, measurability and symmetry of the quantile coupling(a), monotonicity. -/
theorem saq_monotone (m : ℕ) : Monotone (saq m) := by
  intro a b hab
  rw [saq_le_iff]
  exact (saPhi_monotone hab).trans (saq_mem m b)

/-- Law, measurability and symmetry of the quantile coupling(a), measurability. -/
theorem measurable_saq : Measurable (Function.uncurry saq) := by
  refine measurable_from_prod_countable_right fun m => ?_
  exact (saq_monotone m).measurable

theorem sabF_le_one (m : ℕ) (j : ℤ) : sabF m j ≤ 1 := by
  have := sabF_add_sabT m (j + 1)
  have h2 := sabT_nonneg m (j + 1)
  rw [add_sub_cancel_right] at this
  linarith

theorem measurableSet_saq_le (m : ℕ) (j : ℕ) : MeasurableSet {z : ℝ | saq m z ≤ j} :=
  (saq_monotone m).measurable (measurableSet_Iic (a := j))

theorem saN_real_saq_le (m j : ℕ) : saN.real {z | saq m z ≤ j} = sabF m j := by
  have : {z : ℝ | saq m z ≤ j} = {z | saPhi z ≤ sabF m j} := by
    ext z; simp only [mem_ofPred_eq]; exact saq_le_iff m z j
  rw [this]
  exact saN_real_saPhi_le (sabF_nonneg m _) (sabF_le_one m _)

theorem saN_real_saq_eq (m j : ℕ) : saN.real {z | saq m z = j} = sab m j := by
  rcases j with _ | n
  · have : {z : ℝ | saq m z = 0} = {z | saq m z ≤ 0} := by
      ext z; simp
    rw [this, saN_real_saq_le]
    have h := sabF_sub m 0
    rw [sabF_of_neg m (by omega : (0 : ℤ) - 1 < 0), sub_zero] at h
    simpa using h
  · have : {z : ℝ | saq m z = n + 1} = {z | saq m z ≤ n + 1} \ {z | saq m z ≤ n} := by
      ext z; simp only [mem_ofPred_eq, Set.mem_sdiff]; omega
    rw [this, measureReal_sdiff (fun z hz => by simp only [mem_ofPred_eq] at hz ⊢; omega)
      (measurableSet_saq_le m n), saN_real_saq_le, saN_real_saq_le]
    have h := sabF_sub m ((n : ℤ) + 1)
    rw [add_sub_cancel_right] at h
    push_cast at h ⊢
    exact h

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : Ω → ℝ}

/-- Law, measurability and symmetry of the quantile coupling(b): `saq m η ~ Bin(m, 1/2)`. -/
theorem hasLaw_saq (hη : HasLaw η saN P) (m : ℕ) :
    HasLaw (fun ω => saq m (η ω)) (binomial m sahalf) P := by
  have : IsProbabilityMeasure P := hη.isProbabilityMeasure
  have hm : Measurable (saq m) := (saq_monotone m).measurable
  refine ⟨hm.comp_aemeasurable hη.aemeasurable, ?_⟩
  refine Measure.ext_of_measureReal_singleton fun k => ?_
  rw [map_measureReal_apply_of_aemeasurable
    (show AEMeasurable (fun ω => saq m (η ω)) P from hm.comp_aemeasurable hη.aemeasurable)
    (MeasurableSet.singleton k), binomial_real_singleton_half]
  have := hη.measureReal_eq (p := fun z => saq m z = k) (hm (MeasurableSet.singleton k))
  rw [show (fun ω => saq m (η ω)) ⁻¹' {k} = {ω | saq m (η ω) = k} from rfl, this]
  exact saN_real_saq_eq m k

/-- Law, measurability and symmetry of the quantile coupling(b): `m - saq m η ~ Bin(m, 1/2)`. -/
theorem hasLaw_sub_saq (hη : HasLaw η saN P) (m : ℕ) :
    HasLaw (fun ω => m - saq m (η ω)) (binomial m sahalf) P := by
  have : IsProbabilityMeasure P := hη.isProbabilityMeasure
  have hm : Measurable (saq m) := (saq_monotone m).measurable
  have hm2 : Measurable fun z => m - saq m z := hm.const_sub m
  refine ⟨hm2.comp_aemeasurable hη.aemeasurable, ?_⟩
  refine Measure.ext_of_measureReal_singleton fun k => ?_
  rw [map_measureReal_apply_of_aemeasurable
    (show AEMeasurable (fun ω => m - saq m (η ω)) P from hm2.comp_aemeasurable hη.aemeasurable)
    (MeasurableSet.singleton k), binomial_real_singleton_half]
  have := hη.measureReal_eq (p := fun z => m - saq m z = k) (hm2 (MeasurableSet.singleton k))
  rw [show (fun ω => m - saq m (η ω)) ⁻¹' {k} = {ω | m - saq m (η ω) = k} from rfl, this]
  by_cases hk : k ≤ m
  · have : {z : ℝ | m - saq m z = k} = {z | saq m z = m - k} := by
      ext z; simp only [mem_ofPred_eq]; have := saq_le_m m z; omega
    rw [this, saN_real_saq_eq, sab_natCast_symm hk]
  · have : {z : ℝ | m - saq m z = k} = ∅ := by
      ext z; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; omega
    rw [this, measureReal_empty, sab_natCast, Nat.choose_eq_zero_of_lt (not_le.1 hk)]
    simp

end Law

theorem saPhi_neg (z : ℝ) : saPhi (-z) = saPhib z := by
  rw [saPhi_eq_integral, saPhib_eq_integral]
  have := integral_comp_neg_Iic (-z) saphi
  simp only [saphi_neg, neg_neg] at this
  exact this

theorem saq_neg_le_iff (m : ℕ) (z : ℝ) (j : ℕ) :
    saq m (-z) ≤ j ↔ sabF m ((m : ℤ) - j - 1) ≤ saPhi z := by
  rw [saq_le_iff, saPhi_neg]
  have := sabF_symm m (j : ℤ)
  unfold saPhib
  constructor <;> intro h <;> linarith

/-- Law, measurability and symmetry of the quantile coupling(c). -/
theorem saq_neg (m : ℕ) (z : ℝ) :
    (saq m (-z) : ℤ) = m - saq m z - 1 ∨ (saq m (-z) : ℤ) = m - saq m z := by
  have hi0 := saq_le_m m z
  have hmem := saq_mem m z
  have hA : saq m (-z) ≤ m - saq m z := by
    rw [saq_neg_le_iff]
    have : ((m : ℤ) - ((m - saq m z : ℕ) : ℤ) - 1) = (saq m z : ℤ) - 1 := by omega
    rw [this]
    rcases Nat.eq_zero_or_pos (saq m z) with h0 | hpos
    · rw [sabF_of_neg m (by omega)]
      exact (saPhi_pos z).le
    · have hmin : ¬ saq m z ≤ saq m z - 1 := by omega
      rw [saq_le_iff, not_le] at hmin
      have e : (((saq m z - 1 : ℕ)) : ℤ) = (saq m z : ℤ) - 1 := by omega
      rw [e] at hmin
      exact hmin.le
  by_contra hcon
  push Not at hcon
  have hB : m - saq m z ≥ 2 := by omega
  have hq : saq m (-z) ≤ m - saq m z - 2 := by omega
  rw [saq_neg_le_iff] at hq
  have e : ((m : ℤ) - ((m - saq m z - 2 : ℕ) : ℤ) - 1) = (saq m z : ℤ) + 1 := by omega
  rw [e] at hq
  have := sabF_lt_of_lt (m := m) (a := (saq m z : ℤ)) (by omega) (by omega)
  linarith

end StrongApprox
end ElboimSly
