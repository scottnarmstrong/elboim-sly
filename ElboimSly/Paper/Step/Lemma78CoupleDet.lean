/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleAux
public import Mathlib

/-!
# The deterministic separation argument

W_2 after zeta_i, given ℱ^+_zeta_i, proof, "Separation". For good `ν`, the explored region
`R_{T_i}` (walk 1 up to `t'_n`, walk 2 up to `ζ`) does not meet the region of the restarted
walk `W₂(ζ + ·)` on `(0, r]`, provided that `W₂` stays at distance `> 1` from `V` on `[ζ, ζ + r)`
and has no `thit`-type approach on `(ζ, ζ + r)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem exists_Ioo_of_eventually_left {s : ℝ≥0} (hs : 0 < s) {P : ℝ≥0 → Prop}
    (h : ∀ᶠ a in 𝓝[<] s, P a) : ∃ l : ℝ≥0, l < s ∧ ∀ a, l < a → a < s → P a := by
  obtain ⟨l, hlmem, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs).1 h
  exact ⟨l, hlmem, fun a h1 h2 => hsub ⟨h1, h2⟩⟩

/-- The walk datum of the restarted walk. -/
noncomputable def step78Datum (u : Fin d → ℤ) (q : ℝ) (μ : Measure (RingSpace d β)) (ζ : ℝ≥0) :
    CycData Unit d := ((), cycWalk μ u q ζ, q + ζ, true)

theorem step78_envFn_restart {ν : Measure (Unit × RingSpace d β)} (hν : CycGood ν)
    (u : Fin d → ℤ) (q : ℝ) (ζ s : ℝ≥0) :
    envFn ν (step78Datum u q (cycSlice () ν) ζ) s = cycWalk (cycSlice () ν) u q ((ζ : ℝ) + s) := by
  rw [step78_envFn_fwd ν _ rfl]
  exact cycWalk_restart (hν ()) u q ζ.2 s.2

/-- If a point of the region of the restarted walk lies in `R_{t'_n + ζ}`, then one of the
approach conditions fails. -/
theorem step78_separation {ν : Measure (Unit × RingSpace d β)} (hν : CycGood ν)
    (junk : CycEntry Unit d) (u : Fin d → ℤ) (q : ℝ) (Tn ζ r : ℝ≥0)
    (hnear : ∀ s'' : ℝ, (ζ : ℝ) ≤ s'' → s'' < ζ + r → ∀ s1 ∈ Icc (0 : ℝ) Tn,
      1 < ‖cycWalk (cycSlice () ν) u q s'' - cycWalk (cycSlice () ν) 0 0 s1‖)
    (hthit : ∀ s'' : ℝ, (ζ : ℝ) < s'' → s'' < ζ + r → ∀ s''' : ℝ, 0 < s''' → s''' < ζ →
      (∃ k : ℤ, s''' = s'' + k * β) →
        1 < ‖cycWalk (cycSlice () ν) u q s'' - cycWalk (cycSlice () ν) u q s'''‖)
    {x : CycS Unit d β}
    (hx : x ∈ (CycRec.trunc (Tn + ζ) ((step78Plan d β u q Tn).envFinal ν)).region β) :
    x ∉ CycEntry.region β
      ((step78Datum u q (cycSlice () ν) ζ, (envPath ν (step78Datum u q (cycSlice () ν) ζ)).cut r) :
        CycEntry Unit d) := by
  set δ := step78Datum u q (cycSlice () ν) ζ with hδ
  rintro ⟨s, hs0, hsr, -, h2, h3⟩
  have hsr' : s ≤ r := by
    simpa [CycEntry.len, CycPath.cut] using hsr
  have hleft : Edge.Mem ((envPath ν δ).1.left s) x.2.1 := by
    have := h3
    simp only [CycEntry.path, CycPath.cut] at this
    rwa [CPath.left_cut _ _ hs0 (by exact_mod_cast hsr')] at this
  -- the left limit of the restarted walk
  have hz : ∀ᶠ a : ℝ≥0 in 𝓝[<] s, cycWalk (cycSlice () ν) u q ((ζ : ℝ) + a) =
      (envPath ν δ).1.left s := by
    filter_upwards [(envPath ν δ).1.eventually_left hs0] with a ha
    rw [← ha, (envPath_len (δ := δ) (hν ())).2, hδ, step78_envFn_restart hν]
  obtain ⟨l1, hl1, hz1⟩ := exists_Ioo_of_eventually_left hs0 hz
  have hclock : x.2.2 = (((q + ζ + s : ℝ)) : AddCircle β) := by
    have h2' : x.2.2 = CycData.clock β δ s := h2
    rw [h2']; simp [CycData.clock, CycData.sgn, CycData.phase, CycData.fwd, hδ, step78Datum]
  rcases step78_region_subset hν junk hx with ⟨r1, hr1, hr1T, hc1, z1, hz1', hm1⟩ |
      ⟨r2, hr2, hr2ζ, hc2, z2, hz2', hm2⟩
  · -- walk 1
    obtain ⟨a, hla, has⟩ := exists_between hl1
    have : (𝓝[<] r1).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr1⟩
    obtain ⟨a', ha', ha'r⟩ := (hz1'.and (eventually_nhdsWithin_of_forall
      (fun (a : ℝ≥0) (ha : a ∈ Iio r1) => ha))).exists
    have hnorm := norm_le_one_of_edge_mem hleft hm1
    have := hnear ((ζ : ℝ) + a) (by simp) (by
      have : (a : ℝ) < s := by exact_mod_cast has
      have : (s : ℝ) ≤ r := by exact_mod_cast hsr'
      linarith) (a' : ℝ) ⟨a'.2, by
        have : (a' : ℝ) < r1 := by exact_mod_cast ha'r
        have : (r1 : ℝ) ≤ Tn := by exact_mod_cast hr1T
        linarith⟩
    rw [hz1 a hla has, ha'] at this
    exact absurd hnorm (not_le.2 this)
  · -- walk 2
    obtain ⟨l2, hl2, hz2⟩ := exists_Ioo_of_eventually_left hr2 hz2'
    obtain ⟨k, hk⟩ := exists_int_of_coe_eq (hclock.symm.trans hc2)
    have hl1R : (l1 : ℝ) < s := by exact_mod_cast hl1
    have hl2R : (l2 : ℝ) < r2 := by exact_mod_cast hl2
    have hsR : (s : ℝ) ≤ r := by exact_mod_cast hsr'
    have hr2R : (r2 : ℝ) ≤ ζ := by exact_mod_cast hr2ζ
    set m : ℝ := min ((s : ℝ) - l1) ((r2 : ℝ) - l2) with hmdef
    have hm : 0 < m := lt_min (by linarith) (by linarith)
    have hm1 : m ≤ (s : ℝ) - l1 := min_le_left _ _
    have hm2' : m ≤ (r2 : ℝ) - l2 := min_le_right _ _
    set η : ℝ := m / 2 with hη
    have hl1n : (0 : ℝ) ≤ l1 := l1.2
    have hl2n : (0 : ℝ) ≤ l2 := l2.2
    set a : ℝ≥0 := (s - η : ℝ).toNNReal with hadef
    set b : ℝ≥0 := (r2 - η : ℝ).toNNReal with hbdef
    have haR : (a : ℝ) = s - η := Real.coe_toNNReal _ (by linarith)
    have hbR : (b : ℝ) = r2 - η := Real.coe_toNNReal _ (by linarith)
    have hla : l1 < a := by
      rw [← NNReal.coe_lt_coe, haR]; linarith
    have has : a < s := by
      rw [← NNReal.coe_lt_coe, haR]; linarith
    have hlb : l2 < b := by
      rw [← NNReal.coe_lt_coe, hbR]; linarith
    have hbr : b < r2 := by
      rw [← NNReal.coe_lt_coe, hbR]; linarith
    have hnorm := norm_le_one_of_edge_mem hleft hm2
    have := hthit ((ζ : ℝ) + a) (by rw [haR]; linarith) (by rw [haR]; linarith) (b : ℝ)
      (by rw [hbR]; linarith) (by rw [hbR]; linarith) ⟨k, by rw [hbR, haR]; linarith⟩
    rw [hz1 a hla has, hz2 b hlb hbr] at this
    exact absurd hnorm (not_le.2 this)

/-- **w_2 after zeta_i, given ℱ^+_zeta_i, deterministic core.** If `ν'` agrees with `ν` outside the explored region
`R_{t'_n + ζ}`, then the walk of `ν'` started from the restarted datum follows `W₂(ζ + ·)`
on `[0, r]`. -/
theorem step78_agree_det {ν ν' : Measure (Unit × RingSpace d β)} (hν : CycGood ν)
    (hν' : CycGood ν') (junk : CycEntry Unit d) (u : Fin d → ℤ) (q : ℝ) (Tn ζ r : ℝ≥0)
    (hnear : ∀ s'' : ℝ, (ζ : ℝ) ≤ s'' → s'' < ζ + r → ∀ s1 ∈ Icc (0 : ℝ) Tn,
      1 < ‖cycWalk (cycSlice () ν) u q s'' - cycWalk (cycSlice () ν) 0 0 s1‖)
    (hthit : ∀ s'' : ℝ, (ζ : ℝ) < s'' → s'' < ζ + r → ∀ s''' : ℝ, 0 < s''' → s''' < ζ →
      (∃ k : ℤ, s''' = s'' + k * β) →
        1 < ‖cycWalk (cycSlice () ν) u q s'' - cycWalk (cycSlice () ν) u q s'''‖)
    (hag : ∀ x : CycS Unit d β,
      x ∉ (CycRec.trunc (Tn + ζ) ((step78Plan d β u q Tn).envFinal ν)).region β →
        ν {x} = ν' {x}) :
    ∀ s : ℝ≥0, s ≤ r → envFn ν' (step78Datum u q (cycSlice () ν) ζ) s =
      cycWalk (cycSlice () ν) u q ((ζ : ℝ) + s) := by
  intro s hs
  have h := envFn_eq_of_agree (ν := ν) (ν' := ν') (δ := step78Datum u q (cycSlice () ν) ζ)
    (hν ()) (hν' ()) (r := r) (fun x hx => hag x fun hxR =>
      step78_separation hν junk u q Tn ζ r hnear hthit hxR hx) s hs
  rw [h]
  exact step78_envFn_restart hν u q ζ s


/-- **w_2 after zeta_i, given ℱ^+_zeta_i, no closing before `b`**: the restarted walk does not return to its
starting point at a multiple of `β` before time `s`. -/
theorem step78_no_close {μ : Measure (RingSpace d β)} (hμ : Good μ) (u : Fin d → ℤ) (q : ℝ)
    (ζ s : ℝ≥0)
    (hthit : ∀ s'' : ℝ, (ζ : ℝ) < s'' → s'' < ζ + s → ∀ s''' : ℝ, 0 < s''' → s''' < ζ →
      (∃ k : ℤ, s''' = s'' + k * β) → 1 < ‖cycWalk μ u q s'' - cycWalk μ u q s'''‖)
    (hZ0 : (ζ : ℝ) = 0 → ∀ k : ℕ, 1 ≤ k → cycWalk μ u q (k * β) = u → (s : ℝ) ≤ k * β)
    {k : ℕ} (hk : 1 ≤ k) (hks : (k : ℝ) * β < s) :
    cycWalk μ u q ((ζ : ℝ) + k * β) ≠ cycWalk μ u q ζ := by
  intro h
  have hβ : 0 < β := Fact.out
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkβ : β ≤ k * β := by nlinarith
  rcases (ζ.2 : (0 : ℝ) ≤ ζ).eq_or_lt with hz | hz
  · have hz' : (ζ : ℝ) = 0 := hz.symm
    have h' := h
    rw [hz', zero_add, cycWalk_zero hμ] at h'
    have := hZ0 hz' k hk h'
    linarith
  · have hper := cycWalk_periodic_before hμ u q ζ.2 h
    set m : ℝ := min (ζ : ℝ) (k * β) with hm
    have hm0 : 0 < m := lt_min hz (by linarith)
    set η : ℝ := m / 2 with hη
    have hη1 : η < ζ := by have := min_le_left (ζ : ℝ) (k * β); linarith
    have hη2 : η < k * β := by have := min_le_right (ζ : ℝ) (k * β); linarith
    have hη0 : 0 < η := by linarith
    have := hthit ((ζ : ℝ) + k * β - η) (by linarith) (by linarith) ((ζ : ℝ) - η) (by linarith)
      (by linarith) ⟨-(k : ℤ), by push_cast; ring⟩
    have h1 : (0 : ℝ) ≤ (ζ : ℝ) - η := by linarith
    have h2 : (ζ : ℝ) - η ≤ ζ := by linarith
    have h3 := hper ((ζ : ℝ) - η) h1 h2
    rw [show (ζ : ℝ) + k * β - η = ((ζ : ℝ) - η) + k * β by ring, h3, sub_self, norm_zero] at this
    exact absurd this (by norm_num)


end ElboimSly.Paper.Step

end
