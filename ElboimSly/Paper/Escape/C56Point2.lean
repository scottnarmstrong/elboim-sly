/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Point
public import ElboimSly.Paper.Escape.C56MeasG
public import Mathlib

/-!
# ES22 Claim 5.6, phase `i`: the pointwise implication

ES22 Claim 5.6, "On `G_{i-1} ∩ E^a ∩ E^b ∩ E^d`, `thit(T) ≥ b_i`" and "`ℬ_i` holds".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω]

theorem escPhaseA_pos {t : ℝ} (ht : 0 < t) (m i : ℕ) : 0 < escPhaseA t m i := by
  unfold escPhaseA
  split_ifs
  · positivity
  · have h1 : (1 : ℝ) ≤ 4 ^ (i - m) := one_le_pow₀ (by norm_num)
    have : t / (2 * 4 ^ (i - m)) ≤ t / 2 := by
      apply div_le_div_of_nonneg_left ht.le (by norm_num); linarith
    linarith

theorem phase_pointwise {N M : Ω → Measure (CycS ℕ (k + 2) β)} {ω : Ω}
    (hωN : cycNgood N ω = N ω) (hωM : cycNgood M ω = M ω) {j : ℕ} {u v z : Fin (k + 2) → ℤ}
    (hgeom : EscGeom j u v z) {t : ℝ} (hβ : (2 : ℝ) ^ 40 ≤ β) (hβj : β < 4 ^ j)
    (ht1 : (4 : ℝ) ^ (j - 1) ≤ t) (ht2 : t ≤ 4 ^ j) {n : ℕ} (hn : (4 : ℝ) ^ j ≤ 4 ^ n) {i : ℕ}
    (hi1 : 1 ≤ i) (him : i ≤ 2 * escPhaseM β t)
    (hcp : CoupleFacts N M ω (escZt N t (escPhaseM β t) (i - 1) ω))
    (hG : EscG β j u v z t (escYv N v ω) (i - 1))
    (hE1 : (((v + escW N ω (escZt N t (escPhaseM β t) (i - 1) ω)),
        ((escZt N t (escPhaseM β t) (i - 1) ω : ℝ≥0) : ℝ)), escCPath M ω) ∈
        gamFam β j u v z t i)
    (hE2 : ENNReal.ofReal ((4 : ℝ) ^ n) ≤
      hitTime β (escYv N v ω) (escZetaPrev β (escYv N v ω) t (escPhaseM β t) (i - 1))
        ((escZt N t (escPhaseM β t) (i - 1) ω : ℝ≥0) : ℝ)
        (fun r => escYv N v ω ((escZt N t (escPhaseM β t) (i - 1) ω : ℝ≥0) : ℝ) +
          escW M ω r.toNNReal)) :
    EscBi β j u v z t (escYv N v ω) i := by
  have hβ0 : 0 < β := Fact.out
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  set m := escPhaseM β t with hm
  set W := escYv N v ω with hW
  set tn := escZt N t m (i - 1) ω with htn
  have hTz : (tn : ℝ) = escZeta β W t m (i - 1) := (escZeta_yv (N := N) v ht0.le ω m (i - 1)).symm
  set T := escZeta β W t m (i - 1) with hT
  have hTmem := escZeta_mem β W ht0.le m (i - 1)
  have hT0 : 0 ≤ T := (escPhaseA_nonneg ht0.le m (i - 1)).trans hTmem.1
  have hTpos : 0 < T := lt_of_lt_of_le (escPhaseA_pos ht0 m (i - 1)) hTmem.1
  have hgood : ∀ l, Good (avoidEnv N ω l) := by
    intro l; rw [avoidEnv_eq_cycSlice, ← hωN]; exact cycGood_cycNgood N ω l
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcp
  rw [hTz] at hc1 hc2 hc3 hc4 hE1 hE2
  have hTn : T.toNNReal = tn := by rw [← hTz]; exact Real.toNNReal_coe
  have hWT : W T = v + escW N ω tn := by
    simp only [hW, escYv, escY]; rw [hTn]
  -- no regeneration before `T`
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
    have hne := EscG_ne_v hgeom hβ hβj ht1 ht2 W (i := i - 1) (by omega) hG hs1 hs2
    apply hne
    rw [hW, escYv_eq_of_nonneg v hωN (by positivity)]
    have : avoidWalk N ω ((i0 : ℝ) * β) = 0 := hz
    rw [this]; simp
  -- the hitting time, in terms of `W`
  have hnorm : ∀ (s s' : ℝ), 0 < s' →
      ‖W T + escW M ω (s - T).toNNReal - W s'‖ =
        ‖avoidWalk N ω T + avoidPath (cycNgood M) ω (s - T).toNNReal - avoidWalk N ω s'‖ := by
    intro s s' hs'
    rw [hW, escYv_eq_of_nonneg v hωN hT0, escYv_eq_of_nonneg v hωN hs'.le]
    congr 1
    show v + avoidWalk N ω T + avoidPath (cycNgood M) ω (s - T).toNNReal -
      (v + avoidWalk N ω s') = _
    abel
  have hthit : avoidThit N ω T = ⨅ s ∈ {s : ℝ | T < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
      0 < s' ∧ s' < T ∧ ‖W T + escW M ω (s - T).toNNReal - W s'‖ ≤ 1}, ENNReal.ofReal s := by
    rw [hc4]
    refine iInf_congr fun s => iInf_congr_Prop ?_ fun _ => rfl
    simp only [hα, mem_ofPred_eq]
    refine and_congr_right fun _ => exists_congr fun s' => and_congr_right fun _ =>
      and_congr_right fun hs'0 => and_congr_right fun _ => ?_
    rw [hnorm s s' hs'0]
  obtain ⟨hTube, hRelE⟩ := hE1
  have hTube' : escCPath M ω ∈ tubeRat (v + escW N ω tn)
      (fun r => escCurve j u v z t (T + r)) (escR t m i) (24 / 100 * escR t m i)
      (es56B t m i - T) := hTube
  have hRelE' : escCPath M ω ∈ relPathSet β (es56B t m i - T) := hRelE
  have hcont : Continuous (fun r : ℝ => escCurve j u v z t (T + r)) :=
    (continuous_escCurve j u v z t ht0.ne').comp (continuous_const.add continuous_id)
  have hreal := tubeRat_real hcont hTube'
  have hEa1 : ∀ r : ℝ, 0 ≤ r → r ≤ es56B t m i - T →
      ‖escCast (W T + escW M ω r.toNNReal) - escCurve j u v z t (T + r)‖ ≤ escR t m i := by
    intro r hr0 hr1
    have := hreal.1 r hr0 hr1
    rw [hWT]; exact this
  have hEa2 : ∀ r : ℝ, (es56B t m i - T) / 2 ≤ r → r ≤ es56B t m i - T →
      ‖escCast (W T + escW M ω r.toNNReal) - escCurve j u v z t (T + r)‖ ≤
        24 / 100 * escR t m i := by
    intro r hr0 hr1
    have := hreal.2 r hr0 hr1
    rw [hWT]; exact this
  have hb : ENNReal.ofReal (es56B t m i) ≤ avoidThit N ω T :=
    phase_thit_ge hgeom hβ hβj ht1 ht2 hn W hi1 him hG (escW M ω) hthit hEa1 hE2
  have hbT : T ≤ es56B t m i := by
    have := hTmem.2
    have hbA := es56B_le_escPhaseA_succ ht0.le m (i - 1)
    have hi' : i - 1 + 1 = i := by omega
    rw [hi'] at hbA
    linarith [escA_le_B t ht0.le m i]
  have hcoup : ∀ s : ℝ≥0, ENNReal.ofReal (T + s) ≤ avoidThit N ω T →
      W (T + s) - W T = escW M ω s := by
    intro s hs
    have h := hc1 s hs
    have h1 : W (T + s) = v + avoidWalk N ω (T + s) :=
      escYv_eq_of_nonneg v hωN (by positivity)
    have h2 : W T = v + avoidWalk N ω T := escYv_eq_of_nonneg v hωN hT0
    rw [h1, h2]
    have : v + avoidWalk N ω (T + s) - (v + avoidWalk N ω T) =
        avoidWalk N ω (T + s) - avoidWalk N ω T := by abel
    rw [this]; exact h
  have hEd : ENNReal.ofReal (9 / 10 * (es56B t m i - T)) ≤
      volume {s : ℝ | s ∈ Icc 0 (es56B t m i - T) ∧
        IsRelaxedTimeWrt β (fun r => escW M ω r.toNNReal) 0 s} := by
    have hlt : ENNReal.ofReal (es56B t m i - T) < cycTreg (avoidEnv M ω 0) := by
      have hαT : regenStart (avoidEnv N ω) T < T := by rw [hα]; exact hTpos
      have hsT : ENNReal.ofReal (T + (((es56B t m i - T).toNNReal : ℝ≥0) : ℝ)) ≤
          avoidThit N ω T := by
        rw [Real.coe_toNNReal _ (by linarith)]
        rw [show T + (es56B t m i - T) = es56B t m i by ring]; exact hb
      exact hc2 hαT _ hsT
    have hncl := not_closesBy_of_lt_treg (M := M) hωM hlt
    rcases hRelE' with hcl | hrel
    · exact absurd hcl hncl
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hrel
      have hTi : 0 ≤ es56B t m i - T := by linarith
      have : (0 : ℝ) ≤ 1 / (scaleIndex (es56B t m i - T) : ℝ) := by positivity
      nlinarith
  exact phase_Bi hβ0 ht0 W hi1 (escYv_hrc N v ω) (escW M ω) hb hcoup hEa1 hEa2 hEd

end ElboimSly.Paper.Escape

end
