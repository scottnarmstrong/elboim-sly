/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Assemble
public import ElboimSly.Paper.Escape.Es55Prob
public import ElboimSly.Paper.Escape.Es55Ext
public import Mathlib

/-!
# Lemma 5.5, Step 1, from its three deterministic/null ingredients

ES22 Lemma 5.5, Step 1.

`es55Step1_of` proves `Es55Step1 k` (the lower bound `n^{-γ+1}` for `Φ_{Con_i}(ρ_{S₃})` on
`𝒦(β') ∩ 𝒜_i ∩ {r_i ≤ 4^{j-1}, W_i^←(r_i) ∈ F_B}`) from:

* `Es55DetAll`: the geometry of the entries `0` and `I+1` of the record on that set;
* `Es55Jump`: the regenerated walk of a Poisson environment a.s. does not jump at a fixed time;
* `Es55PW`: the pathwise step (agreement of the frozen continuation with the true walk, restart and
  closing: `E₅₆` for the continuation implies `Con_i`);
* the measurability facts `Es55Meas`,

by freezing at `S₃` (`es55_freeze`), ES22 Claim 5.6 (`es55_prob`) and the product-space
adjunction of the independent Poisson process `N''` (`prodExt`).  These three are conditional
helpers with distinct names; they are the remaining content of Step 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper ElboimSly.SRW
  ElboimSly.Brownian

variable {k : ℕ}

/-- The set `H = 𝒦(β') ∩ 𝒜_i ∩ {exit}` of Step 1. -/
def es55H (β : ℝ) [Fact (0 < β)] (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ)
    (hlog : 1 < Real.log β) : Set (Measure (CycS ℕ (k + 2) β)) :=
  (escKSet β tn n β' u ∩ escASet n u β' hlog i) ∩ es55Exit β n u β' i

/-- The geometry of the first and last entries on `H`. -/
def Es55DetAll (k : ℕ) : Prop :=
  ∃ b : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
    {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
    (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N'), b n₀ ≤ β →
    ∀ (u : Fin (k + 2) → ℤ), EscAdmissible (escJ n) u → ∀ (β' i : ℕ), 1 ≤ i →
      i ≤ escIstar n (escJ n) → ∀ ν ∈ es55H β n (indScale t₀ n) u β' i (hlog_of_params hS.params),
        Es55Det n (indScale t₀ n) u β' i (hlog_of_params hS.params) ν

/-- The regenerated walk of a Poisson environment does not jump at a fixed time. -/
def Es55Jump (k : ℕ) : Prop :=
  ∀ {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N'' : Ω → Measure (ℕ × RingSpace (k + 2) β)},
    IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr →
    ∀ t : ℝ, 0 < t → Pr {ω' | ¬ noJumpRat (regenW N'' ω') t} = 0

/-- The pathwise step of Step 1: on `H`, the rational `E₅₆` for the frozen continuation implies
`Con_i` (agreement on `[0, t_*)`, restart at `ξ_B`, closing by the backward walk). -/
def Es55PW (k : ℕ) : Prop :=
  ∃ b : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
    {𝒢₀ : MeasurableSpace Ω} [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)} {N'' : Ω → Measure (ℕ × RingSpace (k + 2) β)}
    (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N')
    (_hN'' : IsPoissonPointProcess N''
      ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr)
    (_hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
        cycNull Pr) Pr), b n₀ ≤ β →
    ∀ (u : Fin (k + 2) → ℤ), EscAdmissible (escJ n) u → ∀ (β' i : ℕ), 1 ≤ i →
      i ≤ escIstar n (escJ n) →
      ∀ᵐ ω ∂Pr, N ω ∈ es55H β n (indScale t₀ n) u β' i (hlog_of_params hS.params) →
        (z55 n (indScale t₀ n) u β' i (hlog_of_params hS.params) N ω,
          regenY (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N N' N''
            (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
              (escIstar n (escJ n) + 2))
            (delta55 n (indScale t₀ n) u β' i (hlog_of_params hS.params) N) ω) ∈
            d55S β (escJ n) u → N ω ∈ escConSet β n u i

/-- **Step 1 of ES22 Lemma 5.5** from the geometry, the no-jump event and the pathwise step. -/
theorem es55Step1_of (hk : 3 ≤ k) (hdet : Es55DetAll k) (hjump : Es55Jump k) (hpw : Es55PW k)
    (hm : Es55Meas k) : Es55Step1 k := by
  have hd : 5 ≤ k + 2 := by omega
  obtain ⟨bD, HD⟩ := hdet
  obtain ⟨bP, HP⟩ := hpw
  choose b56 hb56 using fun n₀ => es55_prob hd n₀
  refine ⟨fun n₀ => max (max (bD n₀) (bP n₀)) (b56 n₀), ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS hβ u hadm β' i hi1 hiI
  have hβD : bD n₀ ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hβP : bP n₀ ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hβ56 : b56 n₀ ≤ β := le_trans (le_max_right _ _) hβ
  have hPr : IsProbabilityMeasure Pr := hS.space.ppp.isProbabilityMeasure
  obtain ⟨Ω2, m2, P2, N2, hP2, hN2, -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β))
  have := hP2
  obtain ⟨hsp2, hN2', hI3⟩ := prodExt hS.space hN2
  have hS2 : Es4Setting (k + 2) β n₀ n t₀ (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω)) (Pr.prod P2)
      (N ∘ Prod.fst) (N' ∘ Prod.fst) := ⟨hS.params, hsp2⟩
  have hmN : (Pr.prod P2).map (N ∘ Prod.fst) = Pr.map N := by
    rw [← Measure.map_map hS.space.ppp.measurable measurable_fst, Measure.map_fst_prod]; simp
  set hlog := hlog_of_params hS.params with hhlog
  set P := plan5 n β (indScale t₀ n) u β' i hlog with hP
  have hPfin : PlanFin P := plan5_planFin n β (indScale t₀ n) u β' i hlog
  have hKeq : P.K = ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞) := rfl
  have hk1 : ((escIstar n (escJ n) + 1 : ℕ) : ℕ∞) < P.K := by
    rw [hKeq]; exact_mod_cast Nat.lt_succ_self _
  obtain ⟨hKm, hCm, -, hKET⟩ := hm hS2 u β' i hi1 hiI
  have hT := isStoppingTime_lam_succ (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω)) P hsp2.ppp.measurable
    hsp2.le (Pr.prod P2) hPfin hk1
  have hHT := hKET hT
  have hfreeze := es55_freeze (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω)) hsp2.ppp hsp2.ppp' hN2'
    hsp2.indep hsp2.indep' hI3 n (indScale t₀ n) u β' i hlog hsp2.le hT hCm hHT
    (fun ν hν => hν.1.1.1) (fun ν hν => HD hS hβD u hadm β' i hi1 hiI ν hν)
    (q := ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2) + 1)))
    (fun v z t hv hvm hz ht1 ht2 => hb56 n₀ β n t₀ hβ56 (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω)) hS2
      hN2' (max_le (gamma1_le_escGamma (k + 2)) (escGamma56_le_escGamma (k + 2)) :
        max (gamma1 (k + 2)) (escGamma56 (k + 2)) ≤ escGamma (k + 2)) u v z t hv hvm hz ht1 ht2
      (hjump hN2' t (lt_of_lt_of_le (by positivity) ht1)))
    (HP hS2 hN2' hI3 hβP u hadm β' i hi1 hiI)
  have key : ∀ p : Ω × Ω2, resPhi P (Pr.prod P2) (N ∘ Prod.fst)
      (lamT P (N ∘ Prod.fst) (escIstar n (escJ n) + 2)) (escConSet β n u i) p =
      resPhi P Pr N (lamT P N (escIstar n (escJ n) + 2)) (escConSet β n u i) p.1 := by
    intro p
    unfold resPhi
    rw [hmN]
    rfl
  refine prodExt_ae (P2 := P2) ?_
  filter_upwards [hfreeze] with p hp hmem
  rw [← key p]
  exact hp hmem

/-- **ES22 Lemma 5.5** from the ingredients of Step 1 (geometry, no-jump event, pathwise step) and the
measurability facts: Step 1 followed by Step 2 (tower property and ES22 Claim 5.7). -/
theorem es5_5_of_ingredients (hk : 3 ≤ k) (hdet : Es55DetAll k) (hjump : Es55Jump k)
    (hpw : Es55PW k) (hm : Es55Meas k) : Es55Concl k :=
  es5_5_of_step1 hk (es55Step1_of hk hdet hjump hpw hm) hm

end ElboimSly.Paper.Escape
