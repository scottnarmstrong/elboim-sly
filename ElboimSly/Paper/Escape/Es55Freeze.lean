/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Data
public import ElboimSly.Paper.Escape.Es55Resample
public import ElboimSly.Paper.Escape.PlanFreeze
public import ElboimSly.Paper.Escape.C57Rec
public import ElboimSly.Paper.Escape.Plan5Entries
public import Mathlib

/-!
# Lemma 5.5, Step 1: freezing at `S₃`

ES22 Lemma 5.5, Step 1 ("Apply the plan coupling, form used in S5 at `S₃` with the
`ℱ_{S₃}`-measurable datum `δ_c = (1, v, ξ_B, +1)`").

`es55_freeze`: let `H` be a set of environments with `{N ∈ H} ∈ ℱ_{S₃}`.  Assume

* `Es55Det`: on `H` the entries `e₀ = ent5 0` and `e_B = ent5 (I+1)` have the geometry needed by
  ES22 Claim 5.6 (`v ∈ ∂B ∩ B⁻`, exit through `F_B`, `t_* ∈ [4^{j-1}, 4^j]`);
* the probability bound `hprob` for the regenerated walk of `N''` (from ES22 Claim 5.6);
* the pathwise step `hpw` (agreement with the true walk on `E₅₆`, restart and closing).

Then `Φ_{Con}(ρ_{S₃}) ≥ q` a.s. on `{N ∈ H}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The geometry of the first and last entries of the record at `S₃` on a good environment. -/
def Es55Det (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (ν : Measure (CycS ℕ (k + 2) β)) : Prop :=
  ∃ a : ℕ, D55Exit (escJ n) u (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)) a ∧
    entEnd (ent5 n tn u β' i hlog ν 0) ∈ escBoundary (escJ n) u ∧
    entEnd (ent5 n tn u β' i hlog ν 0) ∈ escBlockMinus (escJ n) u ∧
    (4 : ℝ) ^ (escJ n - 1) ≤
      d55T β (escJ n) (ent5 n tn u β' i hlog ν 0)
        (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)) a ∧
    d55T β (escJ n) (ent5 n tn u β' i hlog ν 0)
        (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1)) a ≤ (4 : ℝ) ^ escJ n

variable {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)} {N'' : Ω → Measure (ℕ × RingSpace (k + 2) β)}
  (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity ℕ (k + 2) β) Pr)
  (hN'' : IsPoissonPointProcess N''
    ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
  (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
      cycNull Pr) Pr)

/-- The pair of entries `(e₀, e_B)` of the record at `S₃`. -/
noncomputable def z55 (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (ω : Ω) : CycEntry ℕ (k + 2) × CycEntry ℕ (k + 2) :=
  ((cycRecStop (plan5 n β tn u β' i hlog) (cycNgood N)
      (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 2)) ω).coord
        (plan5 n β tn u β' i hlog).junk 0,
   (cycRecStop (plan5 n β tn u β' i hlog) (cycNgood N)
      (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 2)) ω).coord
        (plan5 n β tn u β' i hlog).junk (escIstar n (escJ n) + 1))

/-- The datum `δ_c = (0, v, ξ_B, +1)` of the continuation, read off the record. -/
noncomputable def delta55 (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (ω : Ω) : CycData ℕ (k + 2) :=
  ((0 : ℕ), entEnd (z55 n tn u β' i hlog N ω).1, (z55 n tn u β' i hlog N ω).1.len.toReal, true)

omit mΩ in
theorem z55_eq {n : ℕ} {tn : ℝ} {u : EscV k} {β' i : ℕ} {hlog : 1 < Real.log β}
    {ω : Ω} (hω : CycGood (N ω)) :
    z55 n tn u β' i hlog N ω =
      (ent5 n tn u β' i hlog (N ω) 0, ent5 n tn u β' i hlog (N ω) (escIstar n (escJ n) + 1)) := by
  have hng : cycNgood N ω = N ω := by unfold cycNgood; rw [ite_eq_left hω]
  have hPfin := plan5_planFin n β tn u β' i hlog
  have hKle : ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞) ≤ (plan5 n β tn u β' i hlog).K := le_rfl
  unfold z55
  refine Prod.ext ?_ ?_
  · show (cycRecStop _ (cycNgood N) _ ω).coord _ 0 = _
    rw [← hng]
    exact coord_trunc_lam hPfin (cycGood_cycNgood N ω) hKle (by omega)
  · show (cycRecStop _ (cycNgood N) _ ω).coord _ _ = _
    rw [← hng]
    exact coord_trunc_lam hPfin (cycGood_cycNgood N ω) hKle (by omega)

include hN hN' hI1 hI2 in
/-- The record entries at `S₃` and the datum `δ_c` are `ℱ_{S₃}`-measurable. -/
theorem measurable_z55 (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (hK0 : 0 < (plan5 n β tn u β' i hlog).K) (h𝒢 : 𝒢₀ ≤ mΩ)
    {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt (plan5 n β tn u β' i hlog) 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hTeq : T = lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 2)) :
    Measurable[hT.measurableSpace] (z55 n tn u β' i hlog N) ∧
      Measurable[hT.measurableSpace] (delta55 n tn u β' i hlog N) := by
  have h1 := (cyc_multi_exploration_a (plan5 n β tn u β' i hlog) 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT).2.1
  subst hTeq
  have hc : ∀ m : ℕ, Measurable[hT.measurableSpace] fun ω =>
      (cycRecStop (plan5 n β tn u β' i hlog) (cycNgood N)
        (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 2)) ω).coord
          (plan5 n β tn u β' i hlog).junk m :=
    fun m => (CycRec.measurable_coord _ m).comp h1
  have hz : Measurable[hT.measurableSpace] (z55 n tn u β' i hlog N) :=
    (hc 0).prodMk (hc _)
  refine ⟨hz, ?_⟩
  unfold delta55
  have h0 : Measurable[hT.measurableSpace] fun ω => (z55 n tn u β' i hlog N ω).1 :=
    measurable_fst.comp hz
  refine measurable_const.prodMk ((measurable_entEnd.comp h0).prodMk
    ((ENNReal.measurable_toReal.comp (measurable_entry_len'.comp h0)).prodMk measurable_const))

include hN hN' hN'' hI1 hI2 hI3 in
/-- **Freezing at `S₃`.**  If on `H` the geometry (`Es55Det`) holds, the regenerated walk satisfies
the rational `E₅₆` with probability `≥ q` (`hprob`), and `E₅₆` for the continuation implies `Con`
(`hpw`), then `Φ_{Con}(ρ_{S₃}) ≥ q` almost surely on `{N ∈ H}`. -/
theorem es55_freeze (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (h𝒢 : 𝒢₀ ≤ mΩ)
    (hT : IsStoppingTime (cycMultiFilt (plan5 n β tn u β' i hlog) 𝒢₀ hN.measurable h𝒢 Pr)
      (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 2)))
    {H C : Set (Measure (CycS ℕ (k + 2) β))} (hC : MeasurableSet C)
    (hHT : MeasurableSet[hT.measurableSpace] (N ⁻¹' H))
    (hHgood : ∀ ν ∈ H, CycGood ν) (hDet : ∀ ν ∈ H, Es55Det n tn u β' i hlog ν) {q : ℝ≥0∞}
    (hprob : ∀ v z : Fin (k + 2) → ℤ, ∀ t : ℝ, v ∈ escBoundary (escJ n) u →
      v ∈ escBlockMinus (escJ n) u → z ∈ escFace (escJ n) u → (4 : ℝ) ^ (escJ n - 1) ≤ t →
      t ≤ (4 : ℝ) ^ escJ n →
      q ≤ Pr {ω' | EscRat β (escJ n) u v z t (regenW N'' ω') ∧ noJumpRat (regenW N'' ω') t})
    (hpw : ∀ᵐ ω ∂Pr, N ω ∈ H →
      (z55 n tn u β' i hlog N ω, regenY (plan5 n β tn u β' i hlog) N N' N''
        (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 2))
        (delta55 n tn u β' i hlog N) ω) ∈ d55S β (escJ n) u → N ω ∈ C) :
    ∀ᵐ ω ∂Pr, N ω ∈ H →
      q ≤ resPhi (plan5 n β tn u β' i hlog) Pr N
        (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 2)) C ω := by
  have := hN.isProbabilityMeasure
  set P := plan5 n β tn u β' i hlog with hP
  have hPfin : PlanFin P := plan5_planFin n β tn u β' i hlog
  have hKeq : P.K = ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞) := rfl
  have hK0 : 0 < P.K := by rw [hKeq]; exact_mod_cast Nat.succ_pos _
  have hfinall : ∀ ω, lamT P N (escIstar n (escJ n) + 2) ω ≠ ⊤ := fun ω =>
    lamT_ne_top P hPfin ω (by rw [hKeq])
  have hfin : Pr {ω | lamT P N (escIstar n (escJ n) + 2) ω ≠ ⊤} = 1 := by
    have : {ω | lamT P N (escIstar n (escJ n) + 2) ω ≠ ⊤} = univ := by
      ext ω; exact ⟨fun _ => trivial, fun _ => hfinall ω⟩
    rw [this, measure_univ]
  obtain ⟨hz, hδ⟩ := measurable_z55 𝒢₀ hN hN' hI1 hI2 n tn u β' i hlog hK0 h𝒢 hT rfl
  refine resPhi_ge_of_forall P 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT hfin hC hHT fun A hA => ?_
  have hA' : MeasurableSet[hT.measurableSpace] (A ∩ N ⁻¹' H) := hA.inter hHT
  have hq : ∀ ω ∈ A ∩ N ⁻¹' H,
      q ≤ Pr {ω' | (z55 n tn u β' i hlog N ω, regenW N'' ω') ∈ d55S β (escJ n) u} := by
    rintro ω ⟨-, hωH⟩
    have hωH' : N ω ∈ H := hωH
    have hgood := hHgood _ hωH'
    obtain ⟨a, hex, hv1, hv2, ht1, ht2⟩ := hDet _ hωH'
    have e : {ω' | (z55 n tn u β' i hlog N ω, regenW N'' ω') ∈ d55S β (escJ n) u} =
        {ω' | ((ent5 n tn u β' i hlog (N ω) 0,
          ent5 n tn u β' i hlog (N ω) (escIstar n (escJ n) + 1)), regenW N'' ω') ∈
            d55S β (escJ n) u} := by
      rw [z55_eq hgood]
    rw [e]
    refine le_trans (hprob _ _ _ hv1 hv2 hex.2.1 ht1 ht2) (measure_mono fun ω' hω' => ?_)
    exact ⟨a, hex, hω'.1, hω'.2⟩
  have hfr := plan_regen_freeze P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hK0 h𝒢 hT hfinall hδ hz hA'
    (measurableSet_d55S β (escJ n) u) hq
  refine hfr.trans (measure_mono_ae ?_)
  filter_upwards [hpw] with ω hω hmem
  exact ⟨hmem.1.1, hω hmem.1.2 hmem.2⟩

end ElboimSly.Paper.Escape
