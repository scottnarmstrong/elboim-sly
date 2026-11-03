/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Schauder
import Mathlib

/-!
# The Schauder covariance identity

The Schauder covariance identity.

For `u v : ℝ` the kernel `kernel u v = clamp u * clamp v + ∑' n, ∑ k, S_{n,k}(u) S_{n,k}(v)`
(the sum of `a_h(u) a_h(v)` over the Haar index set, grouped by level) equals
`min (clamp u) (clamp v)`. Consequently `∑' m, kernel (s - m) (t - m) = min s t` for `s, t ≥ 0`.

The proof follows the written proof: first on dyadic points, by induction on the level (we use the
equivalent form "the partial kernel of level `N` equals `min` on `D_N`" instead of the orthogonal
vectors `e_{N,j}`), then by density.
-/

@[expose] public section

open scoped NNReal

namespace ElboimSly.Brownian

/-- The level-`N` partial sum of `∑_h a_h(u) a_h(v)`, over `h ∈ {*} ∪ {(n,k) : n < N}`. -/
noncomputable def kernelPartial (N : ℕ) (u v : ℝ) : ℝ :=
  clamp u * clamp v + ∑ n ∈ Finset.range N, ∑ k : Fin (2 ^ n), schauder n k u * schauder n k v

/-- The Schauder covariance identity. The kernel `k(u,v) = ∑_{h ∈ ℋ} a_h(u) a_h(v)`, with the
sum over the Haar index set grouped by level. -/
noncomputable def kernel (u v : ℝ) : ℝ :=
  clamp u * clamp v + ∑' n : ℕ, ∑ k : Fin (2 ^ n), schauder n k u * schauder n k v

lemma kernelPartial_succ (N : ℕ) (u v : ℝ) :
    kernelPartial (N + 1) u v =
      kernelPartial N u v + ∑ k : Fin (2 ^ N), schauder N k u * schauder N k v := by
  unfold kernelPartial
  rw [Finset.sum_range_succ]
  ring

lemma kernelPartial_symm (N : ℕ) (u v : ℝ) : kernelPartial N u v = kernelPartial N v u := by
  unfold kernelPartial
  simp only [mul_comm]

lemma kernel_symm (u v : ℝ) : kernel u v = kernel v u := by
  unfold kernel
  simp only [mul_comm]

lemma schauder_midpoint' {n N : ℕ} (hn : n < N) (j k : ℕ) :
    schauder n k ((2 * j + 1 : ℝ) / 2 ^ (N + 1)) =
      (schauder n k ((j : ℝ) / 2 ^ N) + schauder n k (((j : ℝ) + 1) / 2 ^ N)) / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  exact schauder_midpoint n m j k

lemma kernelPartial_midpoint (N a : ℕ) (ha : a < 2 ^ N) (v : ℝ) :
    kernelPartial N ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) v =
      (kernelPartial N ((a : ℝ) / 2 ^ N) v + kernelPartial N (((a : ℝ) + 1) / 2 ^ N) v) / 2 := by
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  have ha' : (a : ℝ) + 1 ≤ 2 ^ N := by exact_mod_cast ha
  have hl0 : 0 ≤ (a : ℝ) / 2 ^ N := by positivity
  have hl1 : (a : ℝ) / 2 ^ N ≤ 1 := by rw [div_le_one hp]; linarith
  have hr0 : 0 ≤ ((a : ℝ) + 1) / 2 ^ N := by positivity
  have hr1 : ((a : ℝ) + 1) / 2 ^ N ≤ 1 := by rw [div_le_one hp]; linarith
  have hmid : (2 * a + 1 : ℝ) / 2 ^ (N + 1) = ((a : ℝ) / 2 ^ N + ((a : ℝ) + 1) / 2 ^ N) / 2 := by
    rw [pow_succ]; field_simp; ring
  have hc : clamp ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) =
      (clamp ((a : ℝ) / 2 ^ N) + clamp (((a : ℝ) + 1) / 2 ^ N)) / 2 := by
    have hm0 : 0 ≤ (2 * a + 1 : ℝ) / 2 ^ (N + 1) := by positivity
    have hm1 : (2 * a + 1 : ℝ) / 2 ^ (N + 1) ≤ 1 := by rw [hmid]; linarith
    rw [clamp_of_mem hm0 hm1, clamp_of_mem hl0 hl1, clamp_of_mem hr0 hr1, hmid]
  have hs : ∀ n ∈ Finset.range N,
      ∑ k : Fin (2 ^ n), schauder n k ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) * schauder n k v =
        ((∑ k : Fin (2 ^ n), schauder n k ((a : ℝ) / 2 ^ N) * schauder n k v) +
          ∑ k : Fin (2 ^ n), schauder n k (((a : ℝ) + 1) / 2 ^ N) * schauder n k v) / 2 := by
    intro n hn
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [schauder_midpoint' (Finset.mem_range.mp hn)]
    ring
  unfold kernelPartial
  rw [hc, Finset.sum_congr rfl hs, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

lemma kernelPartial_midpoint_right (N b : ℕ) (hb : b < 2 ^ N) (u : ℝ) :
    kernelPartial N u ((2 * b + 1 : ℝ) / 2 ^ (N + 1)) =
      (kernelPartial N u ((b : ℝ) / 2 ^ N) + kernelPartial N u (((b : ℝ) + 1) / 2 ^ N)) / 2 := by
  rw [kernelPartial_symm, kernelPartial_midpoint N b hb, kernelPartial_symm N _ u,
    kernelPartial_symm N _ u]

/-! ### Arithmetic of minima -/

lemma min_aux_old_new (a b : ℕ) {t : ℝ} (ht : 0 < t) :
    (min ((b : ℝ) * t) (a * t) + min (((b : ℝ) + 1) * t) (a * t)) / 2 =
      min (((b : ℝ) + 1 / 2) * t) (a * t) := by
  rcases le_or_gt a b with h | h
  · have h' : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [min_eq_right (by nlinarith), min_eq_right (by nlinarith), min_eq_right (by nlinarith)]
    ring
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    rw [min_eq_left (by nlinarith), min_eq_left (by nlinarith), min_eq_left (by nlinarith)]
    ring

lemma min_aux_new_new (a b : ℕ) {t : ℝ} (ht : 0 < t) :
    (min ((a : ℝ) * t) (b * t) + min ((a : ℝ) * t) (((b : ℝ) + 1) * t) +
        (min (((a : ℝ) + 1) * t) (b * t) + min (((a : ℝ) + 1) * t) (((b : ℝ) + 1) * t))) / 4
      + (if a = b then t / 4 else 0) =
      min (((a : ℝ) + 1 / 2) * t) (((b : ℝ) + 1 / 2) * t) := by
  rcases lt_trichotomy a b with h | h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    have hne : ¬ a = b := h.ne
    simp only [hne, ↓reduceIte]
    rw [min_eq_left (by nlinarith), min_eq_left (by nlinarith),
      min_eq_left (by nlinarith), min_eq_left (by nlinarith), min_eq_left (by nlinarith)]
    ring
  · subst h
    simp only [↓reduceIte]
    rw [min_eq_left (by nlinarith), min_eq_left (by nlinarith),
      min_eq_right (by nlinarith), min_eq_left (by nlinarith), min_eq_left (by nlinarith)]
    ring
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    have hne : ¬ a = b := h.ne'
    simp only [hne, ↓reduceIte]
    rw [min_eq_right (by nlinarith), min_eq_right (by nlinarith),
      min_eq_right (by nlinarith), min_eq_right (by nlinarith), min_eq_right (by nlinarith)]
    ring

lemma sum_level_mid (N a b : ℕ) (ha : a < 2 ^ N) :
    ∑ k : Fin (2 ^ N), schauder N k ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) *
        schauder N k ((2 * b + 1 : ℝ) / 2 ^ (N + 1)) =
      if a = b then (4 * (2 : ℝ) ^ N)⁻¹ else 0 := by
  simp only [schauder_level_mid]
  split_ifs with hab
  · subst hab
    rw [← schauderAmp_sq, pow_two, ← Finset.sum_range (fun k =>
      (if k = a then schauderAmp N else 0) * (if k = a then schauderAmp N else 0))]
    simp [Finset.sum_ite_eq', ha, mul_ite, ite_mul]
  · refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : (k : ℕ) = a
    · have : (k : ℕ) ≠ b := fun h' => hab (h.symm.trans h')
      simp [this]
    · simp [h]

lemma schauder_level_old (N a k : ℕ) : schauder N k ((a : ℝ) / 2 ^ N) = 0 := by
  simpa using schauder_dyadic N 0 a k

lemma new_eq (N b : ℕ) : (2 * b + 1 : ℝ) / 2 ^ (N + 1) = ((b : ℝ) + 1 / 2) * ((2 : ℝ) ^ N)⁻¹ := by
  rw [pow_succ]; field_simp

lemma old_eq (N a : ℕ) : (a : ℝ) / 2 ^ N = (a : ℝ) * ((2 : ℝ) ^ N)⁻¹ := div_eq_mul_inv _ _

lemma succ_eq (N b : ℕ) : ((b : ℝ) + 1) / 2 ^ N = ((b : ℝ) + 1) * ((2 : ℝ) ^ N)⁻¹ :=
  div_eq_mul_inv _ _

/-- The dyadic identity for the partial kernel of level `N`. -/
theorem kernelPartial_dyadic (N : ℕ) (p q : ℕ) (hp : p ≤ 2 ^ N) (hq : q ≤ 2 ^ N) :
    kernelPartial N ((p : ℝ) / 2 ^ N) ((q : ℝ) / 2 ^ N) = min ((p : ℝ) / 2 ^ N) ((q : ℝ) / 2 ^ N) := by
  induction N generalizing p q with
  | zero =>
    have hp' : (p : ℝ) ≤ 1 := by exact_mod_cast hp
    have hq' : (q : ℝ) ≤ 1 := by exact_mod_cast hq
    simp only [kernelPartial, Finset.range_zero, Finset.sum_empty, add_zero, pow_zero, div_one]
    rw [clamp_of_mem (Nat.cast_nonneg _) hp', clamp_of_mem (Nat.cast_nonneg _) hq']
    rcases le_total p q with h | h
    · have : (p : ℝ) ≤ q := by exact_mod_cast h
      rw [min_eq_left this]
      interval_cases p <;> interval_cases q <;> simp
    · have : (q : ℝ) ≤ p := by exact_mod_cast h
      rw [min_eq_right this]
      interval_cases p <;> interval_cases q <;> simp
  | succ N ih =>
    have ht0 : (0 : ℝ) < ((2 : ℝ) ^ N)⁻¹ := by positivity
    have hold : ∀ a : ℕ, ((2 * a : ℕ) : ℝ) / 2 ^ (N + 1) = (a : ℝ) / 2 ^ N := by
      intro a; rw [pow_succ]; push_cast; field_simp
    have hnew : ∀ a : ℕ, ((2 * a + 1 : ℕ) : ℝ) / 2 ^ (N + 1) = (2 * a + 1 : ℝ) / 2 ^ (N + 1) := by
      intro a; push_cast; rfl
    have oo : ∀ a b : ℕ, a ≤ 2 ^ N → b ≤ 2 ^ N →
        kernelPartial (N + 1) ((a : ℝ) / 2 ^ N) ((b : ℝ) / 2 ^ N) =
          min ((a : ℝ) / 2 ^ N) ((b : ℝ) / 2 ^ N) := by
      intro a b ha hb
      rw [kernelPartial_succ, ih a b ha hb]
      simp [schauder_level_old]
    have no : ∀ a b : ℕ, a < 2 ^ N → b ≤ 2 ^ N →
        kernelPartial (N + 1) ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) ((b : ℝ) / 2 ^ N) =
          min ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) ((b : ℝ) / 2 ^ N) := by
      intro a b ha hb
      have h1 := ih a b ha.le hb
      have h2 := ih (a + 1) b (by omega) hb
      push_cast at h2
      rw [kernelPartial_succ, kernelPartial_midpoint N a ha, h1, h2]
      have hz : ∑ k : Fin (2 ^ N), schauder N k ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) *
          schauder N k ((b : ℝ) / 2 ^ N) = 0 := by simp [schauder_level_old]
      rw [hz, add_zero]
      simp only [old_eq, succ_eq, new_eq]
      exact min_aux_old_new b a ht0
    have nn : ∀ a b : ℕ, a < 2 ^ N → b < 2 ^ N →
        kernelPartial (N + 1) ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) ((2 * b + 1 : ℝ) / 2 ^ (N + 1)) =
          min ((2 * a + 1 : ℝ) / 2 ^ (N + 1)) ((2 * b + 1 : ℝ) / 2 ^ (N + 1)) := by
      intro a b ha hb
      have i1 := ih a b ha.le hb.le
      have i2 := ih a (b + 1) ha.le (by omega)
      have i3 := ih (a + 1) b (by omega) hb.le
      have i4 := ih (a + 1) (b + 1) (by omega) (by omega)
      push_cast at i2 i3 i4
      rw [kernelPartial_succ, kernelPartial_midpoint N a ha,
        kernelPartial_midpoint_right N b hb, kernelPartial_midpoint_right N b hb,
        sum_level_mid N a b ha, i1, i2, i3, i4]
      have e4 : ((4 : ℝ) * 2 ^ N)⁻¹ = ((2 : ℝ) ^ N)⁻¹ / 4 := by field_simp
      rw [e4]
      simp only [old_eq, succ_eq, new_eq]
      have := min_aux_new_new a b ht0
      linarith
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' p <;> obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' q
    · rw [hold, hold]
      exact oo a b (by rw [pow_succ] at hp; omega) (by rw [pow_succ] at hq; omega)
    · rw [hold, hnew, kernelPartial_symm, min_comm]
      exact no b a (by rw [pow_succ] at hq; omega) (by rw [pow_succ] at hp; omega)
    · rw [hnew, hold]
      exact no a b (by rw [pow_succ] at hp; omega) (by rw [pow_succ] at hq; omega)
    · rw [hnew, hnew]
      exact nn a b (by rw [pow_succ] at hp; omega) (by rw [pow_succ] at hq; omega)

/-! ### The infinite kernel -/

lemma summable_level_bound : Summable (fun n : ℕ => ((4 : ℝ) * 2 ^ n)⁻¹) := by
  have : (fun n : ℕ => ((4 : ℝ) * 2 ^ n)⁻¹) = fun n => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
    funext n; rw [mul_inv, one_div, one_div, inv_pow]
  rw [this]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

lemma summable_level (u v : ℝ) :
    Summable (fun n : ℕ => ∑ k : Fin (2 ^ n), schauder n k u * schauder n k v) :=
  Summable.of_norm_bounded summable_level_bound fun n => abs_sum_schauder_mul_le n u v

lemma continuous_kernel : Continuous (fun x : ℝ × ℝ => kernel x.1 x.2) := by
  unfold kernel
  refine Continuous.add (by have := continuous_clamp; fun_prop) ?_
  refine continuous_tsum (u := fun n : ℕ => ((4 : ℝ) * 2 ^ n)⁻¹) (fun n => ?_)
    summable_level_bound (fun n x => abs_sum_schauder_mul_le n x.1 x.2)
  have := continuous_schauder
  fun_prop

lemma tendsto_kernelPartial (u v : ℝ) :
    Filter.Tendsto (fun N => kernelPartial N u v) Filter.atTop (nhds (kernel u v)) := by
  unfold kernelPartial kernel
  exact ((summable_level u v).hasSum.tendsto_sum_nat).const_add _

lemma dyadic_scale (N e p : ℕ) : ((p * 2 ^ e : ℕ) : ℝ) / 2 ^ (N + e) = (p : ℝ) / 2 ^ N := by
  push_cast; rw [pow_add]; field_simp

/-- The kernel is `min` on the dyadic grid. -/
lemma kernel_dyadic (N p q : ℕ) (hp : p ≤ 2 ^ N) (hq : q ≤ 2 ^ N) :
    kernel ((p : ℝ) / 2 ^ N) ((q : ℝ) / 2 ^ N) = min ((p : ℝ) / 2 ^ N) ((q : ℝ) / 2 ^ N) := by
  refine tendsto_nhds_unique (tendsto_kernelPartial _ _) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop N] with M hM
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hM
  have h1 := kernelPartial_dyadic (N + e) (p * 2 ^ e) (q * 2 ^ e)
    (by rw [pow_add]; exact Nat.mul_le_mul_right _ hp)
    (by rw [pow_add]; exact Nat.mul_le_mul_right _ hq)
  rw [dyadic_scale, dyadic_scale] at h1
  exact h1.symm

lemma exists_dyadic_approx {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ p : ℕ → ℕ, (∀ N, p N ≤ 2 ^ N) ∧
      Filter.Tendsto (fun N => (p N : ℝ) / 2 ^ N) Filter.atTop (nhds u) := by
  refine ⟨fun N => ⌊(2 : ℝ) ^ N * u⌋₊, fun N => ?_, ?_⟩
  · have h : (⌊(2 : ℝ) ^ N * u⌋₊ : ℝ) ≤ 2 ^ N := by
      calc (⌊(2 : ℝ) ^ N * u⌋₊ : ℝ) ≤ 2 ^ N * u := Nat.floor_le (by positivity)
        _ ≤ 2 ^ N := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) N]
    exact_mod_cast h
  · have hlow : ∀ N : ℕ, u - (1 / 2 : ℝ) ^ N ≤ (⌊(2 : ℝ) ^ N * u⌋₊ : ℝ) / 2 ^ N := by
      intro N
      have h2 : (0 : ℝ) < 2 ^ N := by positivity
      have := Nat.lt_floor_add_one ((2 : ℝ) ^ N * u)
      rw [le_div_iff₀ h2, sub_mul, one_div, inv_pow, inv_mul_cancel₀ h2.ne']
      linarith
    have hup : ∀ N : ℕ, (⌊(2 : ℝ) ^ N * u⌋₊ : ℝ) / 2 ^ N ≤ u := by
      intro N
      have h2 : (0 : ℝ) < 2 ^ N := by positivity
      rw [div_le_iff₀ h2]
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ N * u by positivity)
      linarith
    have hg : Filter.Tendsto (fun N : ℕ => u - (1 / 2 : ℝ) ^ N) Filter.atTop (nhds u) := by
      simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds hlow hup

lemma kernel_eq_min_unit {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    kernel u v = min u v := by
  obtain ⟨p, hp, hpt⟩ := exists_dyadic_approx hu0 hu1
  obtain ⟨q, hq, hqt⟩ := exists_dyadic_approx hv0 hv1
  have h1 : Filter.Tendsto (fun N => kernel ((p N : ℝ) / 2 ^ N) ((q N : ℝ) / 2 ^ N))
      Filter.atTop (nhds (kernel u v)) :=
    (continuous_kernel.tendsto (u, v)).comp (hpt.prodMk_nhds hqt)
  have h2 : Filter.Tendsto (fun N => min ((p N : ℝ) / 2 ^ N) ((q N : ℝ) / 2 ^ N))
      Filter.atTop (nhds (min u v)) := hpt.min hqt
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  exact (kernel_dyadic N _ _ (hp N) (hq N)).symm

/-- The Schauder covariance identity, first assertion: `k(u,v) = min (cl u) (cl v)`. -/
theorem kernel_eq_min (u v : ℝ) : kernel u v = min (clamp u) (clamp v) := by
  have h : kernel u v = kernel (clamp u) (clamp v) := by
    unfold kernel
    rw [clamp_of_mem (clamp_nonneg u) (clamp_le_one u),
      clamp_of_mem (clamp_nonneg v) (clamp_le_one v)]
    congr 1
    refine tsum_congr fun n => Finset.sum_congr rfl fun k _ => ?_
    rw [schauder_clamp k.2, schauder_clamp k.2]
  rw [h]
  exact kernel_eq_min_unit (clamp_nonneg u) (clamp_le_one u) (clamp_nonneg v) (clamp_le_one v)

lemma sum_clamp_range (w : ℝ) (hw : 0 ≤ w) (M : ℕ) :
    ∑ m ∈ Finset.range M, clamp (w - m) = min w M := by
  induction M with
  | zero => simp [hw]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    rcases le_total w M with h | h
    · rw [clamp_of_nonpos (by linarith), min_eq_left h, min_eq_left (by linarith)]; ring
    · rcases le_total (w - M) 1 with h' | h'
      · rw [min_eq_right h, clamp_of_mem (by linarith) h', min_eq_left (by linarith)]; ring
      · rw [min_eq_right h, clamp_of_one_le h', min_eq_right (by linarith)]

lemma hasSum_clamp_sub (w : ℝ) (hw : 0 ≤ w) : HasSum (fun m : ℕ => clamp (w - m)) w := by
  have h : HasSum (fun m : ℕ => clamp (w - m)) (∑ m ∈ Finset.range ⌈w⌉₊, clamp (w - m)) :=
    hasSum_sum_of_ne_finset_zero fun m hm => by
      rw [Finset.mem_range, not_lt] at hm
      have h1 := Nat.le_ceil w
      have h2 : (⌈w⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
      exact clamp_of_nonpos (by linarith)
  rwa [sum_clamp_range w hw, min_eq_left (Nat.le_ceil w)] at h

/-- The Schauder covariance identity, second assertion: `∑_m k(s-m, t-m) = min s t`. -/
theorem hasSum_kernel_sub {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    HasSum (fun m : ℕ => kernel (s - m) (t - m)) (min s t) := by
  have := hasSum_clamp_sub (min s t) (le_min hs ht)
  convert this using 2 with m
  rw [kernel_eq_min, min_clamp, ← min_sub_sub_right]

end ElboimSly.Brownian
