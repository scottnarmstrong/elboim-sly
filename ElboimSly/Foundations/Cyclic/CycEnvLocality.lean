/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycEnvPath
public import ElboimSly.Foundations.Interchange.PathConvert
public import ElboimSly.Foundations.Interchange.BoundedPath
public import Mathlib

/-!
# Locality of the environment path

Basic properties of world-lines (a), last sentence: if `ν'` is good and agrees with `ν` on
`cycReg((δ, r, P(· ∧ r)))`, then `P^{ν'}_δ = P^ν_δ` on `[0, r]`.

We prove it in terms of atoms (`ν {x} = ν' {x}` for `x` in the region), and deduce the
statement for restrictions of measures.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)]

omit [Fact (0 < β)] in
theorem isPathOn_of_agree {μ μ' : Measure (RingSpace d β)} {a : ℝ} {γ : ℝ≥0 → Fin d → ℤ}
    (h : IsForwardPath μ a γ) {r : ℝ≥0}
    (hag : ∀ s : ℝ≥0, 0 < s → s ≤ r → ∀ z, IsLeftLimit γ s z → ∀ e : Edge d, e.Mem z →
      (Rings μ e (a + s) ↔ Rings μ' e (a + s))) :
    IsPathOn μ' a (a + r) (fwdReal a γ) := by
  have hf := Interchange.IsForwardPath.toPathOn h (a + r)
  refine ⟨hf.1, hf.2.1, hf.2.2.1, fun t ht z hz => ?_⟩
  have hsw := hf.2.2.2 t ht z hz
  have hta : a < t := ht.1
  have hs0 : 0 < (t - a).toNNReal := Real.toNNReal_pos.mpr (sub_pos.mpr hta)
  have hcoe : a + ((t - a).toNNReal : ℝ) = t := by
    rw [Real.coe_toNNReal _ (sub_pos.mpr hta).le]; ring
  have hsr : (t - a).toNNReal ≤ r := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (sub_pos.mpr hta).le]
    linarith [ht.2]
  obtain ⟨z0, hz0⟩ := h.2.1 _ hs0
  have hz0' : IsLeftLimitAbove a (fwdReal a γ) t z0 := fwdReal_isLeftLimitAbove hta hz0
  have hzz : z = z0 := IsLeftLimitAbove.unique hta hz hz0'
  subst hzz
  have hag' := hag _ hs0 hsr z hz0
  rw [hcoe] at hag'
  refine ⟨fun e he hr => hsw.1 e he ((hag' e he).mpr hr),
    fun hn => hsw.2 fun ⟨e, he, hr⟩ => hn ⟨e, he, (hag' e he).mp hr⟩⟩

omit [Fact (0 < β)] in
theorem forwardPath_eq_of_agree {μ μ' : Measure (RingSpace d β)} {a : ℝ}
    {γ γ' : ℝ≥0 → Fin d → ℤ} (h : IsForwardPath μ a γ) (h' : IsForwardPath μ' a γ')
    (h0 : γ 0 = γ' 0) {r : ℝ≥0}
    (hag : ∀ s : ℝ≥0, 0 < s → s ≤ r → ∀ z, IsLeftLimit γ s z → ∀ e : Edge d, e.Mem z →
      (Rings μ e (a + s) ↔ Rings μ' e (a + s))) :
    ∀ s : ℝ≥0, s ≤ r → γ' s = γ s := by
  intro s hs
  have hf := isPathOn_of_agree h hag
  have hf' := Interchange.IsForwardPath.toPathOn h' (a + r)
  have := hf'.eq_of_left (by simp) hf (by simpa [fwdReal] using h0.symm)
  have hs' := this (a + s) ⟨by simp, by simpa using hs⟩
  simpa [fwdReal] using hs'

/-- Locality of the environment path, in terms of atoms. -/
theorem envFn_eq_of_agree {ν ν' : Measure (I × RingSpace d β)} {δ : CycData I d}
    (h : Good (cycSlice δ.copy ν)) (h' : Good (cycSlice δ.copy ν')) {r : ℝ≥0}
    (hag : ∀ x ∈ CycEntry.region β ((δ, (envPath ν δ).cut r) : CycEntry I d), ν {x} = ν' {x}) :
    ∀ s : ℝ≥0, s ≤ r → envFn ν' δ s = envFn ν δ s := by
  refine forwardPath_eq_of_agree (envFn_spec h).1 (envFn_spec h').1
    (((envFn_spec h).2).trans ((envFn_spec h').2).symm) fun s hs0 hsr z hz e he => ?_
  have hz' : z = (envPath ν δ).1.left s := by
    have := (envPath ν δ).1.eventually_left hs0
    rw [(envPath_len h).2] at this
    have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩
    obtain ⟨u, hu1, hu2⟩ := (hz.and ‹∀ᶠ u in 𝓝[<] s, envFn ν δ u = _›).exists
    exact hu1.symm.trans hu2
  subst hz'
  rw [rings_envMeasure ν δ e s, rings_envMeasure ν' δ e s]
  have hmem : (δ.copy, (e, δ.clock β s)) ∈
      CycEntry.region β ((δ, (envPath ν δ).cut r) : CycEntry I d) := by
    refine ⟨s, hs0, ?_, rfl, rfl, ?_⟩
    · simpa [CycEntry.len, CycPath.cut] using hsr
    · simp only [CycEntry.path, CycPath.cut]
      rw [CPath.left_cut _ _ hs0 (by exact_mod_cast hsr)]
      exact he
  rw [hag _ hmem]

end ElboimSly.Cyclic

end
