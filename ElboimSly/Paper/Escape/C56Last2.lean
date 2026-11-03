/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Last
public import ElboimSly.Paper.Escape.C56Point2
public import Mathlib

/-!
# ES22 Claim 5.6, phase `2m+1`: the pointwise implication

ES22 Claim 5.6, "Phase `2m+1`".  On `G_{2m} ∩ E^e`, `thit(T) ≥ t` and `ℬ_{2m+1}` holds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω]

theorem norm_escCast_eq {k : ℕ} (x : Fin (k + 2) → ℤ) : ‖escCast x‖ = ‖x‖ := norm_escCast x

theorem last_pointwise {N M : Ω → Measure (CycS ℕ (k + 2) β)} {ω : Ω}
    (hωN : cycNgood N ω = N ω) {j : ℕ} {u v z : Fin (k + 2) → ℤ}
    (hgeom : EscGeom j u v z) {t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β)
    (hβj : β < 4 ^ j) (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j)
    (hm3 : 3 ≤ escPhaseM β t)
    (hcp : CoupleFacts N M ω (escZt N t (escPhaseM β t) (2 * escPhaseM β t) ω))
    (hG : EscG β j u v z t (escYv N v ω) (2 * escPhaseM β t))
    (hEz : v + escW N ω (escZt N t (escPhaseM β t) (2 * escPhaseM β t) ω) +
      escW M ω (t - ((escZt N t (escPhaseM β t) (2 * escPhaseM β t) ω : ℝ≥0) : ℝ)).toNNReal = z)
    (hEB : ∀ s : ℝ≥0, (s : ℝ) ≤ t - ((escZt N t (escPhaseM β t) (2 * escPhaseM β t) ω : ℝ≥0) : ℝ) →
      v + escW N ω (escZt N t (escPhaseM β t) (2 * escPhaseM β t) ω) + escW M ω s ∈
        escBlockMinus j u)
    (hEm : ∀ s : ℝ≥0, (s : ℝ) ≤ t - ((escZt N t (escPhaseM β t) (2 * escPhaseM β t) ω : ℝ≥0) : ℝ) →
      ‖escW M ω s‖ ≤ β ^ (0.3 : ℝ)) :
    EscBlast β j u z t (escYv N v ω) := by
  have hβ0 : 0 < β := Fact.out
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  obtain ⟨hS, hsβ, hSj⟩ := sqrt_facts (by have := hgeom.hj; omega) hβ hβj ht1
  have hbeta3 := esc_beta_pow_le hβ
  set m := escPhaseM β t with hm
  set W := escYv N v ω with hW
  set tn := escZt N t m (2 * m) ω with htn
  have hTz : (tn : ℝ) = escZeta β W t m (2 * m) := (escZeta_yv (N := N) v ht0.le ω m (2 * m)).symm
  set T := escZeta β W t m (2 * m) with hT
  have hTmem := escZeta_mem β W ht0.le m (2 * m)
  have hT0 : 0 ≤ T := (escPhaseA_nonneg ht0.le m (2 * m)).trans hTmem.1
  have hTpos : 0 < T := lt_of_lt_of_le (escPhaseA_pos ht0 m (2 * m)) hTmem.1
  have hgood : ∀ l, Good (avoidEnv N ω l) := by
    intro l; rw [avoidEnv_eq_cycSlice, ← hωN]; exact cycGood_cycNgood N ω l
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcp
  rw [hTz] at hc1 hc2 hc3 hc4 hEz hEB hEm
  have hTn : T.toNNReal = tn := by rw [← hTz]; exact Real.toNNReal_coe
  have hWT : W T = v + escW N ω tn := by
    simp only [hW, escYv, escY]; rw [hTn]
  have hα : regenStart (avoidEnv N ω) T = 0 := by
    apply regenStart_eq_zero_of_no_zero hgood hT0
    intro i0 hi0 hz
    obtain ⟨hi0a, hi0b⟩ := Finset.mem_Icc.1 hi0
    have hi0R : (1 : ℝ) ≤ i0 := by exact_mod_cast hi0a
    have hs1 : β ≤ (i0 : ℝ) * β := by nlinarith
    have hs2 : (i0 : ℝ) * β ≤ T := by
      have h1 : (i0 : ℝ) ≤ T / β :=
        le_trans (by exact_mod_cast hi0b) (Nat.floor_le (div_nonneg hT0 hβ0.le))
      rwa [le_div_iff₀ hβ0] at h1
    have hne := EscG_ne_v hgeom hβ hβj ht1 ht2 W (i := 2 * m) le_rfl hG hs1 hs2
    apply hne
    rw [hW, escYv_eq_of_nonneg v hωN (by positivity)]
    have : avoidWalk N ω ((i0 : ℝ) * β) = 0 := hz
    rw [this]; simp
  -- `‖W_v(T) - w‖` is small
  have hxz := W_zeta_near_z hgeom hβ hβj ht1 ht2 hm3 W hG
  rw [← hT] at hxz
  -- `thit ≥ t`
  have hnorm : ∀ (s s' : ℝ), 0 < s' →
      ‖W T + escW M ω (s - T).toNNReal - W s'‖ =
        ‖avoidWalk N ω T + avoidPath (cycNgood M) ω (s - T).toNNReal - avoidWalk N ω s'‖ := by
    intro s s' hs'
    rw [hW, escYv_eq_of_nonneg v hωN hT0, escYv_eq_of_nonneg v hωN hs'.le]
    congr 1
    show v + avoidWalk N ω T + avoidPath (cycNgood M) ω (s - T).toNNReal -
      (v + avoidWalk N ω s') = _
    abel
  have hb : ENNReal.ofReal t ≤ avoidThit N ω T := by
    rw [hc4]
    refine le_iInf₂ fun s hs => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hTs, s', ⟨kk, hk⟩, hs'0, hs'T, hle⟩ := hs
    rw [hα] at hs'0
    by_contra hlt
    push Not at hlt
    have hkk : kk < 0 := by
      by_contra hc
      push Not at hc
      have : (0 : ℝ) ≤ kk := by exact_mod_cast hc
      nlinarith
    have hkR : (kk : ℝ) ≤ -1 := by exact_mod_cast (by omega : kk ≤ -1)
    have hss : β ≤ s - s' := by nlinarith
    rw [← hnorm s s' hs'0] at hle
    -- `W_v(s')` is far from `w`
    have hfar := W_far_from_z hgeom hβ hβj ht1 ht2 W (i := 2 * m) le_rfl hG hs'0.le
      (by linarith) (hs'T.le.trans (le_of_eq hT.symm))
    -- `W'(s - T)` is close to `w`
    have hr0 : 0 ≤ s - T := by linarith
    have hrT : (s - T) ≤ t - T := by linarith
    have hnn : (((s - T).toNNReal : ℝ≥0) : ℝ) = s - T := Real.coe_toNNReal _ hr0
    have hm1 := hEm (s - T).toNNReal (by rw [hnn]; exact hrT)
    have hcast : escCast (W T + escW M ω (s - T).toNNReal) - escCast z =
        (escCast (W T) - escCast z) + escCast (escW M ω (s - T).toNNReal) := by
      ext c; simp [escCast]; ring
    have hn1 : ‖escCast (W T + escW M ω (s - T).toNNReal) - escCast z‖ ≤
        Real.sqrt β / 512 + Real.sqrt β / 2048 + β ^ (0.3 : ℝ) := by
      rw [hcast]
      refine (norm_add_le _ _).trans ?_
      rw [norm_escCast_eq]
      linarith
    have hfar' : ‖escCast (W s') - escCast z‖ ≤ ‖escCast (W s') - escCast (W T + escW M ω
        (s - T).toNNReal)‖ + ‖escCast (W T + escW M ω (s - T).toNNReal) - escCast z‖ := by
      calc ‖escCast (W s') - escCast z‖ = ‖(escCast (W s') -
            escCast (W T + escW M ω (s - T).toNNReal)) +
            (escCast (W T + escW M ω (s - T).toNNReal) - escCast z)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hle' : ‖escCast (W s') - escCast (W T + escW M ω (s - T).toNNReal)‖ ≤ 1 := by
      rw [c56_norm_escCast_sub, norm_sub_rev]; exact hle
    linarith
  -- agreement and the conclusion
  have hag : ∀ r : ℝ, 0 ≤ r → r ≤ t - T → W (T + r) = W T + escW M ω r.toNNReal := by
    intro r hr0 hr1
    have h := hc1 r.toNNReal (by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hb
      rw [Real.coe_toNNReal _ hr0]; linarith)
    rw [Real.coe_toNNReal _ hr0] at h
    have h1 : W (T + r) = v + avoidWalk N ω (T + r) :=
      escYv_eq_of_nonneg v hωN (by positivity)
    have h2 : W T = v + avoidWalk N ω T := escYv_eq_of_nonneg v hωN hT0
    have : avoidWalk N ω (T + r) = avoidWalk N ω T + escW M ω r.toNNReal := by
      show avoidWalk N ω (T + r) = avoidWalk N ω T + avoidPath (cycNgood M) ω r.toNNReal
      rw [← h]; abel
    rw [h1, h2, this]; abel
  have htT : T ≤ t := hTmem.2.trans (es56B_two_m_le ht0.le)
  refine ⟨fun s hs1 hs2 => ?_, ?_⟩
  · have hr0 : 0 ≤ s - T := by linarith
    have hnn : (((s - T).toNNReal : ℝ≥0) : ℝ) = s - T := Real.coe_toNNReal _ hr0
    have e := hag (s - T) hr0 (by linarith)
    rw [show T + (s - T) = s by ring] at e
    have hmem := hEB (s - T).toNNReal (by rw [hnn]; linarith)
    have hm1 := hEm (s - T).toNNReal (by rw [hnn]; linarith)
    rw [← hWT] at hmem
    refine ⟨by rw [e]; exact hmem, ?_⟩
    rw [e]
    have : escCast (W T + escW M ω (s - T).toNNReal) - escCast (W T) =
        escCast (escW M ω (s - T).toNNReal) := by
      ext c; simp [escCast]
    rw [this, norm_escCast_eq]; exact hm1
  · have hr0 : 0 ≤ t - T := by linarith
    have hnn : (((t - T).toNNReal : ℝ≥0) : ℝ) = t - T := Real.coe_toNNReal _ hr0
    have e := hag (t - T) hr0 le_rfl
    rw [show T + (t - T) = t by ring] at e
    rw [e, hWT]
    exact hEz

end ElboimSly.Paper.Escape

end
