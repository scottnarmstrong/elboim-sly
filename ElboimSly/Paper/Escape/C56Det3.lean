/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Det2
public import Mathlib

/-!
# ES22 Claim 5.6, phase `i`: `ℬ_i` holds

ES22 Claim 5.6, "`ℬ_i` holds".  Given `thit(T) ≥ b_i`, the walk `W_v` equals
`W_v(T) + W̃(· - T)` on `[T, b_i]`; the relaxed times of `W_v` relative to `T` are those of `W̃`
relative to `0`, shifted by `T`; non-relaxed times have measure `< b_i - a_i`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- **`ℬ_i`.** -/
theorem phase_Bi {j : ℕ} {u v z : Fin (k + 2) → ℤ} {β t : ℝ} (hβ0 : 0 < β) (ht0 : 0 < t)
    (W : ℝ → Fin (k + 2) → ℤ) {i : ℕ} (hi1 : 1 ≤ i)
    (_hrc : ∀ r, 0 ≤ r → ∀ᶠ u in 𝓝[≥] r, W u = W r)
    (Wt : ℝ≥0 → Fin (k + 2) → ℤ) {thit : ℝ≥0∞}
    (hb : ENNReal.ofReal (es56B t (escPhaseM β t) i) ≤ thit)
    (hcoup : ∀ s : ℝ≥0, ENNReal.ofReal (escZeta β W t (escPhaseM β t) (i - 1) + s) ≤ thit →
      W (escZeta β W t (escPhaseM β t) (i - 1) + s) - W (escZeta β W t (escPhaseM β t) (i - 1)) =
        Wt s)
    (hEa1 : ∀ r : ℝ, 0 ≤ r → r ≤ es56B t (escPhaseM β t) i -
        escZeta β W t (escPhaseM β t) (i - 1) →
      ‖escCast (W (escZeta β W t (escPhaseM β t) (i - 1)) + Wt r.toNNReal) -
        escCurve j u v z t (escZeta β W t (escPhaseM β t) (i - 1) + r)‖ ≤
        escR t (escPhaseM β t) i)
    (hEa2 : ∀ r : ℝ, (es56B t (escPhaseM β t) i - escZeta β W t (escPhaseM β t) (i - 1)) / 2 ≤ r →
      r ≤ es56B t (escPhaseM β t) i - escZeta β W t (escPhaseM β t) (i - 1) →
      ‖escCast (W (escZeta β W t (escPhaseM β t) (i - 1)) + Wt r.toNNReal) -
        escCurve j u v z t (escZeta β W t (escPhaseM β t) (i - 1) + r)‖ ≤
        (24 / 100) * escR t (escPhaseM β t) i)
    (hEd : ENNReal.ofReal (9 / 10 * (es56B t (escPhaseM β t) i -
        escZeta β W t (escPhaseM β t) (i - 1))) ≤
      volume {s : ℝ | s ∈ Icc 0 (es56B t (escPhaseM β t) i -
          escZeta β W t (escPhaseM β t) (i - 1)) ∧
        IsRelaxedTimeWrt β (fun r => Wt r.toNNReal) 0 s}) :
    EscBi β j u v z t W i := by
  set m := escPhaseM β t with hm
  set T := escZeta β W t m (i - 1) with hT
  have hTmem := escZeta_mem β W ht0.le m (i - 1)
  have hT0 : 0 ≤ T := (escPhaseA_nonneg ht0.le m (i - 1)).trans hTmem.1
  have hi' : i - 1 + 1 = i := by omega
  have hbA : es56B t m (i - 1) ≤ escPhaseA t m i := by
    have := es56B_le_escPhaseA_succ ht0.le m (i - 1)
    rwa [hi'] at this
  have hTa : T ≤ escPhaseA t m i := hTmem.2.trans hbA
  have hAB := escA_le_B t ht0.le m i
  -- agreement on `[T, b_i]`
  have hag : ∀ r : ℝ, 0 ≤ r → r ≤ es56B t m i - T → W (T + r) = W T + Wt r.toNNReal := by
    intro r hr0 hr1
    have h := hcoup r.toNNReal (by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hb
      rw [Real.coe_toNNReal _ hr0]; linarith)
    rw [Real.coe_toNNReal _ hr0] at h
    rw [← h]; abel
  -- the relaxed times
  have hwin : T ≤ escPhaseA t m i := hTa
  have hgap := window_gap ht0 (m := m) hi1
  have hphase := phase_window ht0 hi1 hTmem.1 hTmem.2
  set Ti := es56B t m i - T with hTi
  set ai := escPhaseA t m i with hai
  have hJ : ∃ r ∈ Ico (ai - T) Ti, IsRelaxedTimeWrt β (fun r => Wt r.toNNReal) 0 r := by
    by_contra hno
    push Not at hno
    have hsub : {s : ℝ | s ∈ Icc 0 Ti ∧ IsRelaxedTimeWrt β (fun r => Wt r.toNNReal) 0 s} ⊆
        Icc 0 Ti \ Ico (ai - T) Ti := by
      rintro s ⟨hs1, hs2⟩
      refine ⟨hs1, fun hJ => hno s hJ hs2⟩
    have hJ_sub : Ico (ai - T) Ti ⊆ Icc 0 Ti := fun s hs =>
      ⟨by linarith [hs.1], hs.2.le⟩
    have hvol := (measure_mono hsub).trans
      (le_of_eq (measure_sdiff (μ := volume) hJ_sub measurableSet_Ico.nullMeasurableSet
        (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)))
    rw [Real.volume_Icc, Real.volume_Ico] at hvol
    have hTi0 : 0 ≤ Ti := by linarith [hAB]
    have hJlen : 0 ≤ Ti - (ai - T) := by linarith
    have h1 := hEd.trans hvol
    simp only [sub_zero] at h1
    have h2 : ENNReal.ofReal (9 / 10 * Ti) + ENNReal.ofReal (Ti - (ai - T)) ≤
        ENNReal.ofReal Ti := by
      calc ENNReal.ofReal (9 / 10 * Ti) + ENNReal.ofReal (Ti - (ai - T))
          ≤ (ENNReal.ofReal Ti - ENNReal.ofReal (Ti - (ai - T))) +
              ENNReal.ofReal (Ti - (ai - T)) := by gcongr
        _ = ENNReal.ofReal Ti := tsub_add_cancel_of_le
            (ENNReal.ofReal_le_ofReal (by linarith))
    rw [← ENNReal.ofReal_add (by linarith) hJlen] at h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff hTi0).1 h2
    have : Ti - (ai - T) < 1 / 10 * Ti := by
      have h4 : es56B t m i - ai = Ti - (ai - T) := by rw [hTi]; ring
      have h5 : es56B t m i - escPhaseA t m (i - 1) ≥ Ti := by
        rw [hTi]; linarith [hTmem.1]
      linarith
    linarith
  obtain ⟨r, hrJ, hrrel⟩ := hJ
  have hr0 : 0 ≤ r := by linarith [hrJ.1]
  have hrel : IsRelaxedTimeWrt β W T (T + r) := by
    have := (isRelaxedTimeWrt_shift hβ0 (w := W) (g := fun r => Wt r.toNNReal) (W T) T 0 r
      (fun s hs => by
        have := hag s hs.1 (by linarith [hrJ.2, hs.2])
        simpa using this)).2 hrrel
    simpa using this
  have hmemS : T + r ∈ relaxedSet β W T := ⟨by linarith, hrel⟩
  have hzi : escZeta β W t m i = escZetaStep β W (escPhaseA t m i) (es56B t m i) T := by
    have e : escZeta β W t m (i - 1 + 1) = escZetaStep β W (escPhaseA t m (i - 1 + 1))
        (es56B t m (i - 1 + 1)) (escZeta β W t m (i - 1)) := rfl
    rw [hi'] at e
    exact e
  have hlow : ai ≤ T + r := by linarith [hrJ.1]
  have hhigh : T + r < es56B t m i := by linarith [hrJ.2]
  obtain ⟨hlt, hle⟩ := escZetaStep_lt_of_exists hmemS hlow hhigh
  rw [← hzi] at hlt hle
  have hzmem := escZeta_mem β W ht0.le m i
  -- the three conditions
  refine ⟨hlt, fun s hs1 hs2 => ?_, ?_⟩
  · have hr1 : s - T ≤ Ti := by linarith
    have := hag (s - T) (by linarith) hr1
    rw [show T + (s - T) = s by ring] at this
    have h := hEa1 (s - T) (by linarith) hr1
    rw [show T + (s - T) = s by ring, ← this] at h
    exact h
  · have hr1 : escZeta β W t m i - T ≤ Ti := by linarith
    have hr2 : Ti / 2 ≤ escZeta β W t m i - T := by
      have := hphase.2.2
      linarith [hzmem.1]
    have := hag (escZeta β W t m i - T) (by linarith) hr1
    rw [show T + (escZeta β W t m i - T) = escZeta β W t m i by ring] at this
    have h := hEa2 (escZeta β W t m i - T) hr2 hr1
    rw [show T + (escZeta β W t m i - T) = escZeta β W t m i by ring, ← this] at h
    exact h

end ElboimSly.Paper.Escape

end
