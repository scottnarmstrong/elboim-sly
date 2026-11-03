/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Geom
public import ElboimSly.Paper.Escape.C57Jump
public import ElboimSly.Paper.Escape.ReadDisjoint
public import ElboimSly.Paper.Avoid.ProcessLaw
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingRegen
public import Mathlib

/-!
# The deterministic core of ES22 Claim 5.7

ES22 Claim 5.7, "On `E₅₇ ∩ E_far ∩ E_av`".

`c57_core`: fix a sample point.  Let `q = P̃` be the environment path of the backward walk in the
fresh environment `Ñ_{S₂}`, `Z = Y' - p_i` the regenerated continuation of part (c) of the plan
coupling and `w = W_i^←` the backward walk in the true environment.  If

* `Z` agrees with `q - p_i` up to the closing time of `q - p_i` (coupling (c)),
* `w` agrees with `q` up to `r` whenever the cut path of `q` reads no point of the explored region
  `R` (coupling (b)), and `R` lies in the union of the regions of the entries of the record,
* `p_i + Z` stays in the box of eq. (85) up to time `S = 4^{j-1}` and is outside `𝒬` at `S`
  (`E₅₇`), `‖Z(r)‖ ≥ L₇ + 1` for `r ∈ [t₇, 4ⁿ]` (`E_far`) and `p_i + Z(r) ∉ A₇` for `r ≤ 4ⁿ`
  (`E_av`),

then the true backward walk leaves `𝒬` before `S`, at a point of `F_B`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem escFace_not_mem_escQ {j : ℕ} (hj : 1 ≤ j) {u x : EscV k} (hx : x ∈ escFace j u) :
    x ∉ escQ j u := by
  intro hQ
  have h1 : u 0 + 2 ^ j / 2 ≤ x 0 := hQ.1.1
  have h2 : x 0 = u 0 + 2 ^ (j - 1) - 1 := hx.1
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hpow : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hpm : (2 : ℤ) ^ (m + 1 - 1) = 2 ^ m := by simp
  rw [hpm] at h2
  rw [hpow] at h1
  omega

theorem c57_core {j : ℕ} (hj : 4 ≤ j) {u : EscV k} {I i : ℕ} (hi : 1 ≤ i ∧ i ≤ I)
    (E : ℕ → CycEntry ℕ (k + 2)) (p : ℕ → EscV k) (β' : ℝ) (n : ℕ) (L7 t7 : ℝ) (ht7 : 0 ≤ t7)
    (hE0 : ∀ r : ℝ≥0, 0 < r → (r : ℝ≥0∞) ≤ (E 0).len → (E 0).path.left r ∉ escBlock j u)
    (hEdata : ∀ m, 1 ≤ m → m ≤ I → (E m).data = (((0 : ℕ), p m, β', true) : CycData ℕ (k + 2)))
    (HV : ∀ R : ℝ, max (Real.log β) 10 ≤ R → ∀ r'' : ℝ≥0, 0 < r'' → (r'' : ℝ≥0∞) ≤ (E i).len →
      ‖(E i).path.left r'' - p i‖ ≤ R → (r'' : ℝ) ≤ 4 * R ^ 2 * Real.log R ^ 2)
    (HD : ∀ m, 1 ≤ m → m ≤ I → m ≠ i → ∀ r'' : ℝ≥0, 0 < r'' → (r'' : ℝ≥0∞) ≤ (E m).len →
      (n : ℝ) ^ 17 / 6 - 2 < ‖(E m).path.left r'' - p i‖)
    (R : Set (CycS ℕ (k + 2) β)) (hR : R ⊆ ⋃ m ∈ Finset.range (I + 1), (E m).region β)
    (q w : CycPath (k + 2)) (Z : ℝ≥0 → EscV k)
    (hq0 : q.1.fn 0 = p i) (hpQ : p i ∈ escQ j u)
    (Hb : ∀ r : ℝ≥0, Disjoint (CycEntry.region β
        ((((0 : ℕ), p i, β', false) : CycData ℕ (k + 2)), q.cut (r : ℝ≥0∞))) R →
      ∀ s : ℝ≥0, s ≤ r → q.1.fn s = w.1.fn s)
    (Hc : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ pathTreg β.toNNReal (fun s => q.1.fn s - p i) →
      Z r = q.1.fn r - p i)
    (S : ℝ≥0) (hS : 0 < S) (hS4 : (S : ℝ) ≤ 4 ^ n)
    (E57 : ∀ τ ∈ qSet 0 S, p i + Z τ ∈ escBigBox j u) (E57' : p i + Z S ∉ escQ j u)
    (Efar : ∀ τ : ℝ≥0, t7 ≤ τ → (τ : ℝ) ≤ 4 ^ n →
      (τ ∈ qSet t7.toNNReal ((4 : ℝ≥0) ^ n) ∨ ∃ m : ℕ, τ = m * β.toNNReal) → L7 + 1 ≤ ‖Z τ‖)
    (Eav : ∀ τ ∈ qSet 0 ((4 : ℝ≥0) ^ n), p i + Z τ ∉ avoidSet (p i) L7 E I)
    (hL7 : max (Real.log β) 10 ≤ L7 + 1)
    (hβ : t7 + 4 * (L7 + 1) ^ 2 * Real.log (L7 + 1) ^ 2 < β)
    (hn : L7 + 1 < (n : ℝ) ^ 17 / 6 - 2) :
    ExitJ (escQ j u) (escFace j u) (S : ℝ≥0∞) w.1 := by
  have hβ0 : 0 < β := Fact.out
  have hL7pos : 0 < L7 + 1 := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hL7)
  have ht7β : t7 < β := by
    have : 0 ≤ 4 * (L7 + 1) ^ 2 * Real.log (L7 + 1) ^ 2 := by positivity
    linarith
  -- no regeneration up to `4^n`
  have hnoreg : ∀ r : ℝ≥0, (r : ℝ) ≤ 4 ^ n →
      (r : ℝ≥0∞) ≤ pathTreg β.toNNReal (fun s => q.1.fn s - p i) := by
    intro r hr
    by_contra hlt
    rw [not_le] at hlt
    have hfin : pathTreg β.toNNReal (fun s => q.1.fn s - p i) < ⊤ :=
      lt_trans hlt ENNReal.coe_lt_top
    obtain ⟨jj, hjj1, hjj, hz⟩ := pathTreg_exists hfin
    set r' : ℝ≥0 := (jj : ℝ≥0) * β.toNNReal with hr'
    have hr'le : (r' : ℝ≥0∞) ≤ pathTreg β.toNNReal (fun s => q.1.fn s - p i) := hjj ▸ le_rfl
    have hr'r : r' < r := by exact_mod_cast hlt.trans_le' hr'le |> fun h => h
    have hr'4 : (r' : ℝ) ≤ 4 ^ n := le_trans (le_of_lt (by exact_mod_cast hr'r)) hr
    have hZ0 := Hc r' hr'le
    have hzero : q.1.fn r' - p i = 0 := hz
    rw [hzero] at hZ0
    have hrβ : β ≤ (r' : ℝ) := by
      have : (r' : ℝ) = (jj : ℝ) * β := by
        rw [hr']; push_cast; rw [Real.coe_toNNReal _ hβ0.le]
      rw [this]
      have : (1 : ℝ) ≤ jj := by exact_mod_cast hjj1
      nlinarith
    have := Efar r' (by linarith) hr'4 (Or.inr ⟨jj, rfl⟩)
    rw [hZ0, norm_zero] at this
    linarith
  have hZq : ∀ r : ℝ≥0, (r : ℝ) ≤ 4 ^ n → Z r = q.1.fn r - p i := fun r hr => Hc r (hnoreg r hr)
  have hqZ : ∀ r : ℝ≥0, (r : ℝ) ≤ 4 ^ n → q.1.fn r = p i + Z r := fun r hr => by
    rw [hZq r hr]; abel
  have hSle : ∀ s : ℝ≥0, s ≤ S → (s : ℝ) ≤ 4 ^ n := fun s hs =>
    le_trans (by exact_mod_cast hs) hS4
  have hRC : IsRCPath q.1.fn := fun t => q.1.rc t
  have hqSet4 : ∀ τ ∈ qSet 0 ((4 : ℝ≥0) ^ n), (τ : ℝ) ≤ 4 ^ n := fun τ hτ => by
    have := (mem_qSet_Icc zero_le hτ).2
    exact_mod_cast this
  -- the events for the path `q`, at all times
  have E57q : ∀ s : ℝ≥0, s ≤ S → q.1.fn s ∈ escBigBox j u := by
    intro s hs
    by_contra hnot
    obtain ⟨τ, hτ, hτq⟩ := exists_qSet hRC (zero_le : (0 : ℝ≥0) ≤ s) hs
    have hτ4 : (τ : ℝ) ≤ 4 ^ n := hSle τ (mem_qSet_Icc zero_le hτ).2
    have := E57 τ hτ
    rw [← hqZ τ hτ4, hτq] at this
    exact hnot this
  have Eavq : ∀ s : ℝ≥0, (s : ℝ) ≤ 4 ^ n → q.1.fn s ∉ avoidSet (p i) L7 E I := by
    intro s hs hmem
    have hs' : s ≤ (4 : ℝ≥0) ^ n := by exact_mod_cast hs
    obtain ⟨τ, hτ, hτq⟩ := exists_qSet hRC (zero_le : (0 : ℝ≥0) ≤ s) hs'
    have hτ4 := hqSet4 τ hτ
    have := Eav τ hτ
    rw [← hqZ τ hτ4, hτq] at this
    exact this hmem
  have Efarq : ∀ s : ℝ≥0, t7 ≤ s → (s : ℝ) ≤ 4 ^ n → L7 + 1 ≤ ‖q.1.fn s - p i‖ := by
    intro s hs1 hs2
    have hs' : s ≤ (4 : ℝ≥0) ^ n := by exact_mod_cast hs2
    have hts : t7.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hs1
    obtain ⟨τ, hτ, hτq⟩ := exists_qSet hRC hts hs'
    have hτ' := mem_qSet_Icc (hts.trans hs') hτ
    have hτ4 : (τ : ℝ) ≤ 4 ^ n := by exact_mod_cast hτ'.2
    have ht7τ : t7 ≤ τ := by
      have := hτ'.1
      exact (Real.toNNReal_le_iff_le_coe.1 this)
    have := Efar τ ht7τ hτ4 (Or.inl hτ)
    rw [hZq τ hτ4, hτq] at this
    exact this
  -- exit geometry
  obtain ⟨r₁, hr₁pos, hr₁S, hin, hF, -⟩ := exit_geom hj q hS (by rw [hq0]; exact hpQ)
    (fun s hs => E57q s hs)
    (by rw [hqZ S (hSle S le_rfl)]; exact E57')
  have hr₁4 : ∀ s : ℝ≥0, s ≤ r₁ → (s : ℝ) ≤ 4 ^ n := fun s hs => hSle s (hs.trans hr₁S)
  have hne : ∀ r' : ℝ≥0, 0 < r' → (𝓝[<] r').NeBot := fun r' hr' =>
    nhdsLT_neBot_of_exists_lt ⟨0, hr'⟩
  have hQ : ∀ r' : ℝ≥0, 0 < r' → r' ≤ r₁ → q.1.left r' ∈ escQ j u := by
    intro r' hr' hle
    have := hne r' hr'
    obtain ⟨s, hs, hsr⟩ := ((q.1.eventually_left hr').and
      (self_mem_nhdsWithin (a := r') (s := Iio r'))).exists
    rw [← hs]; exact hin s (lt_of_lt_of_le hsr hle)
  have hav : ∀ r' : ℝ≥0, 0 < r' → r' ≤ r₁ → q.1.left r' ∉ avoidSet (p i) L7 E I := by
    intro r' hr' hle
    have := hne r' hr'
    obtain ⟨s, hs, hsr⟩ := ((q.1.eventually_left hr').and
      (self_mem_nhdsWithin (a := r') (s := Iio r'))).exists
    have hsr' : s < r' := hsr
    rw [← hs]
    exact Eavq s (hr₁4 s (le_trans hsr'.le hle))
  have hfar : ∀ r' : ℝ≥0, 0 < r' → r' ≤ r₁ → t7 < r' → L7 + 1 ≤ ‖q.1.left r' - p i‖ := by
    intro r' hr' hle ht
    have := hne r' hr'
    have hlt : t7.toNNReal < r' := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht7]; exact ht
    obtain ⟨s, hs, hsI⟩ := ((q.1.eventually_left hr').and (Ioo_mem_nhdsLT hlt)).exists
    have hts : t7 ≤ s := by
      have := hsI.1
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht7] at this
      exact this.le
    have hsr' : s < r' := hsI.2
    have h4 := hr₁4 s (le_trans hsr'.le hle)
    have := Efarq s hts h4
    rw [← hs]; exact this
  have hdis := read_disjoint hj hi E p β' n L7 t7 hE0 hEdata HV HD q r₁ hQ hav hfar hL7 hβ hn
  have hdis' := Disjoint.mono_right hR hdis
  have hw := Hb r₁ hdis'
  have hFnotQ : q.1.fn r₁ ∉ escQ j u := escFace_not_mem_escQ (by omega) hF
  exact exitJ_of_exit (Set.disjoint_left.2 fun x hx hxQ => escFace_not_mem_escQ (by omega) hx hxQ)
    w.1 hr₁pos hr₁S (fun s hs => by rw [← hw s hs.le]; exact hin s hs) (by rw [← hw r₁ le_rfl]; exact hF)

end ElboimSly.Paper.Escape
