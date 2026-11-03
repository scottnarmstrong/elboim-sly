/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauHatInterface
public import ElboimSly.Paper.Heavy.One

/-!
# Lemma 6.12 and Theorem 6.1, up to the interface with §5

ES22 Lemma 6.12, ES22 Theorem 6.1.

* `geoPremise_of_indH2`: the premise `P_{4^n}` of geometric domination of regenerations is (H2) at level `n - 1`
  with `t₀' = 4`, since `t_{n-1} = 4^n` and `β ≤ iβ`.
* `es6_twelve_of_interface`: `P(𝒢ᶜ) ≤ e^{-c₆ n³}`.
* `es6_one_of_interface`: Theorem 6.1.

The interface `HeavyEscInterface` (the conclusion of interface with S6) is the only extra
hypothesis; the adaptedness of the regenerated walk to `avoidFilt` is `avoidWalk_cycNgood_adapted`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
/-- The premise `P_{4^n}` of geometric domination of regenerations follows from (H2) at level `n - 1`, `t₀' = 4`. -/
theorem geoPremise_of_indH2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)} {n : ℕ} (hn : 1 ≤ n) (hβ : 1 ≤ β)
    (hH2 : IndH2 P N (n - 1) 4) : GeoPremise P N ((4 : ℝ) ^ n) := by
  intro i hi hiT
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hscale : indScale 4 (n - 1) = (4 : ℝ) ^ n := by
    unfold indScale
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]
  have hmem : (i : ℝ) * β ∈ Set.Icc 1 (indScale 4 (n - 1)) := by
    refine ⟨by nlinarith, by rw [hscale]; exact hiT⟩
  have := hH2 _ hmem 0
  have e : (-(d : ℝ) / 2 + 0.1) = (-(d : ℝ) / 2 + 1 / 10) := by norm_num
  rw [e]
  have e2 : (fun ω => regenWalk (geoSlices N ω) ((i : ℝ) * β)) =
      fun ω => regenWalk (fun k => copyEnv (N ω) k) ((i : ℝ) * β) := by
    funext ω
    have : geoSlices N ω = fun k => copyEnv (N ω) k := by
      funext k; exact (congrFun (avoidEnv_eq_cycSlice N ω) k).symm
    rw [this]
  have e3 : {ω | regenWalk (geoSlices N ω) ((i : ℝ) * β) = 0} =
      {ω | regenWalk (fun k => copyEnv (N ω) k) ((i : ℝ) * β) = 0} := by
    ext ω
    have h := congrFun e2 ω
    show regenWalk (geoSlices N ω) ((i : ℝ) * β) = 0 ↔
      regenWalk (fun k => copyEnv (N ω) k) ((i : ℝ) * β) = 0
    rw [h]
  rw [e3]
  exact this

/-- (H2) at level `n - 1`, `t₀' = 4`, for the environment `N` of an `Es4Setting`: this is the
standing assumption (SH2) at the level used by geometric domination of regenerations. -/
theorem es4_indH2_pred {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} {𝒢₀ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ d β)}
    (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') : IndH2 Pr N (n - 1) 4 := by
  have hp := S.params
  have h := (hp.ind (n - 1) (by have := hp.lt; omega) (by have := hp.lt; omega) 4
    (by norm_num) le_rfl).1 Ω Pr N S.space.ppp
  exact h.2.1

/-- ES22 Lemma 6.12, up to the interface interface with S6. -/
theorem es6_twelve_of_interface {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀) {Ω : Type} (𝒢₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ d β)}
    (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β) :
    Pr {ω | ¬ heavyGood d β t₀ n (geoSlices N ω)} ≤
      ENNReal.ofReal (Real.exp (-(heavyC6 d E * (n : ℝ) ^ 3))) := by
  have hp := S.params
  have hβ15 : 15 ≤ β := by linarith [hp.beta_sigma, (by norm_num : (15 : ℝ) ≤ 10 ^ 14)]
  have hn1 : 1 ≤ n := by have := hT.t4; omega
  exact es6_twelve_of_tauhat (E := E) S.space.ppp hp.five_le hβ15 hT.t4 hp.one_lt
    hp.le_four (geoPremise_of_indH2 hn1 (by linarith) (es4_indH2_pred S))
    (fun k => es6_tauhat_of_interface hI 𝒢₀ S hT hβ5 k) hT.t11

/-- ES22 Theorem 6.1, up to the interface interface with S6. -/
theorem es6_one_of_interface {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀) {Ω : Type} (𝒢₀ : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ d β)}
    (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β) :
    Pr {ω | ¬ ∀ t : ℝ, 0 ≤ t → t + indScale t₀ n ^ heavyEps d ≤ indScale t₀ n →
        ENNReal.ofReal ((9 / 10 + 2 / (n : ℝ)) * indScale t₀ n ^ heavyEps d) ≤
          volume ({s : ℝ | 0 ≤ s ∧ IsRelaxedTime (geoSlices N ω) s} ∩
            Icc t (t + indScale t₀ n ^ heavyEps d))} ≤
      ENNReal.ofReal (Real.exp (-(heavyC6 d E * (n : ℝ) ^ 3))) := by
  have hp := S.params
  have hβ15 : 15 ≤ β := by linarith [hp.beta_sigma, (by norm_num : (15 : ℝ) ≤ 10 ^ 14)]
  have hn1 : 1 ≤ n := by have := hT.t4; omega
  exact es6_one_of_tauhat (E := E) (n₀ := n₀) S.space.ppp hp.five_le hp.eight_le hβ15 hp.one_lt
    hp.le_four hp.beta_lt hT (geoPremise_of_indH2 hn1 (by linarith) (es4_indH2_pred S))
    (fun k => es6_tauhat_of_interface hI 𝒢₀ S hT hβ5 k)
