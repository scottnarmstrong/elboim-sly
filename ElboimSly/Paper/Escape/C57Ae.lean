/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Env
public import ElboimSly.Paper.Escape.C57Slice
public import ElboimSly.Paper.Escape.PlanCoupling
public import ElboimSly.Paper.Escape.PlanFreeze
public import Mathlib

/-!
# ES22 Claim 5.7: the sample-point implication

ES22 Claim 5.7, "On `E₅₇ ∩ E_far ∩ E_av`".

`c57_ae`: almost surely, if the pair (random set `A₇`, regenerated continuation `Y' - p_i`) lies in
the event `setS`, then the true backward walk leaves `𝒬` before `4^{j-1}` at a point of `F_B`
(`N ω ∈ exitSet`).  This combines the plan coupling (`es5_plan_coupling` (b), (c)), the region of
the record at `S₂` (`cycRegionStop_lamT_subset`), the properties of the entries
(`Plan5Entries`) and the deterministic core `c57_core`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

theorem envWalk_of_good {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (CycS ℕ d β)}
    (h : CycGood ν) (δ : CycData ℕ d) : envWalk ν δ = envFn ν δ := by
  unfold envWalk
  rw [ite_eq_left h]

section

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} (𝒢₀ : MeasurableSpace Ω)
  [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' N'' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem c57_ae
    (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)
    (hN' : IsPoissonPointProcess N' (cycIntensity ℕ (k + 2) β) Pr)
    (hN'' : IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr)
    (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
    (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
    (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
        cycNull Pr) Pr)
    (h𝒢 : 𝒢₀ ≤ mΩ) {n : ℕ} (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (hi : 1 ≤ i ∧ i ≤ escIstar n (escJ n)) (_hn : 2 ≤ n) (hj4 : 4 ≤ escJ n)
    (hIlam : 16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n)
    {S : ℝ≥0} (_hS : (S : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2 / 4) (hS0 : 0 < S) (hS4 : (S : ℝ) ≤ 4 ^ n)
    {t7 L7 : ℝ} (ht7 : 0 ≤ t7) (hL7 : max (Real.log β) 10 ≤ L7 + 1)
    (hβ : t7 + 4 * (L7 + 1) ^ 2 * Real.log (L7 + 1) ^ 2 < β)
    (hnL : L7 + 1 < (n : ℝ) ^ 17 / 6 - 2) :
    let P := plan5 n β tn u β' i hlog
    let δ : Ω → CycData ℕ (k + 2) := fun _ => ((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false)
    ∀ᵐ ω ∂Pr,
      ((recAvoid P.junk (escPoint n (escJ n) u i) L7 (escIstar n (escJ n))
          (cycRecStop P (cycNgood N) (lamT P N (escIstar n (escJ n) + 1)) ω)),
        regenY P N N' N'' (lamT P N (escIstar n (escJ n) + 1)) δ ω) ∈
          setS β n (escJ n) u i S t7 L7 → N ω ∈ exitSet (β := β) (escJ n) u S (δ ω) := by
  intro P δ
  have := hN.isProbabilityMeasure
  set I := escIstar n (escJ n) with hI
  have hPfin : PlanFin P := plan5_planFin n β tn u β' i hlog
  have hKeq : P.K = ((I + 2 : ℕ) : ℕ∞) := rfl
  have hKpos : 0 < P.K := by rw [hKeq]; exact_mod_cast Nat.succ_pos _
  have hk1 : ((I + 1 : ℕ) : ℕ∞) < P.K := by rw [hKeq]; exact_mod_cast Nat.lt_succ_self _
  have hk1' : ((I + 1 : ℕ) : ℕ∞) ≤ P.K := hk1.le
  have hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) (lamT P N (I + 1)) :=
    isStoppingTime_lam 𝒢₀ P hN.measurable h𝒢 Pr hPfin hk1
  have hfin : ∀ ω, lamT P N (I + 1) ω ≠ ⊤ := fun ω => lamT_ne_top P hPfin ω hk1'
  have hδ : Measurable[hT.measurableSpace] δ := measurable_const
  obtain ⟨⟨hfresh, -⟩, -, -, hb, hc1, -⟩ :=
    es5_plan_coupling.{0, 0, 0} P 𝒢₀ hN hN' hN'' hI1 hI2 hI3 hKpos h𝒢 hT hδ
  have hgoodN : ∀ᵐ ω ∂Pr, CycGood (N ω) := by
    filter_upwards [ae_cycNgood_eq hN] with ω h
    rw [← h]; exact cycGood_cycNgood N ω
  have hgoodT : ∀ᵐ ω ∂Pr, CycGood (tildeMeasure N N'
      (cycRegionStop P (cycNgood N) (lamT P N (I + 1))) ω) := by
    have hF : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν} :=
      measurableSet_cycGood.compl
    have h := hfresh (A := univ) MeasurableSet.univ hF
    have e : {ω | lamT P N (I + 1) ω ≠ ⊤} = univ := by ext ω; simp [hfin ω]
    simp only [e, univ_inter, measure_univ, one_mul, Measure.map_apply hN.measurable hF] at h
    have h0 : Pr (N ⁻¹' {ν : Measure (CycS ℕ (k + 2) β) | ¬ CycGood ν}) = 0 := ae_iff.1 hgoodN
    rw [h0] at h
    exact ae_iff.2 h
  filter_upwards [hb, hgoodN, hgoodT, ae_cycNgood_eq hN] with ω hbω hgN hgT hNg
  intro hmem
  obtain ⟨hZ57, hZfar, hZav⟩ := hmem
  set ν := cycNgood N ω with hν
  have hνgood : CycGood ν := cycGood_cycNgood N ω
  set R := cycRegionStop P (cycNgood N) (lamT P N (I + 1)) ω with hRdef
  set Ñ := tildeMeasure N N' (cycRegionStop P (cycNgood N) (lamT P N (I + 1))) ω with hÑ
  set q := envPath Ñ (δ ω) with hq
  set w := envPath (N ω) (δ ω) with hw
  set Z := regenY P N N' N'' (lamT P N (I + 1)) δ ω with hZ
  have hqfn : ∀ s, q.1.fn s = envWalk Ñ (δ ω) s := fun s => by
    rw [(envPath_len (hgT (δ ω).copy)).2, envWalk_of_good hgT]
  have hwfn : ∀ s, w.1.fn s = envWalk (N ω) (δ ω) s := fun s => by
    rw [(envPath_len (hgN (δ ω).copy)).2, envWalk_of_good hgN]
  have hpf : planFirst P N N' (lamT P N (I + 1)) δ ω =
      fun s => q.1.fn s - escPoint n (escJ n) u i := by
    funext s
    simp only [planFirst, hqfn]
    rfl
  have hR : R ⊆ ⋃ m ∈ Finset.range (I + 1), (ent5 n tn u β' i hlog ν m).region β :=
    cycRegionStop_lamT_subset hPfin N hk1' ω
  have hq0 : q.1.fn 0 = escPoint n (escJ n) u i := envPath_zero (hgT (δ ω).copy)
  have hpQ : escPoint n (escJ n) u i ∈ escQ (escJ n) u := escPoint_mem_escQ hj4
    (le_trans (Nat.mul_le_mul_left 16 (Nat.mul_le_mul_right _ hi.2)) hIlam)
  have Hb : ∀ r : ℝ≥0, Disjoint (CycEntry.region β
      ((((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2)),
        q.cut (r : ℝ≥0∞))) R → ∀ s : ℝ≥0, s ≤ r → q.1.fn s = w.1.fn s := by
    intro r hdis s hs
    have := hbω (hfin ω) r (Or.inr hdis) s hs
    rw [hqfn, hwfn]; exact this
  have Hc : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ pathTreg β.toNNReal (fun s => q.1.fn s - escPoint n (escJ n) u i) →
      Z r = q.1.fn r - escPoint n (escJ n) u i := by
    intro r hr
    have h := hc1 ω (r := r) (by rw [hpf]; exact hr)
    have h' : Z r = planFirst P N N' (lamT P N (I + 1)) δ ω r := h
    rw [h', hpf]
  have hσ : cycRecStop P (cycNgood N) (lamT P N (I + 1)) ω =
      CycRec.trunc (lam P ν (I + 1)).toNNReal (P.envFinal ν) := rfl
  have hE : ∀ m, 1 ≤ m → m ≤ I →
      (cycRecStop P (cycNgood N) (lamT P N (I + 1)) ω).coord P.junk m = ent5 n tn u β' i hlog ν m := by
    intro m _ hm
    rw [hσ]
    exact coord_trunc_lam hPfin hνgood hk1' (Nat.lt_succ_of_le hm)
  have hZav' : ∀ τ ∈ qSet 0 ((4 : ℝ≥0) ^ n),
      escPoint n (escJ n) u i + Z τ ∉ avoidSet (escPoint n (escJ n) u i) L7
        (ent5 n tn u β' i hlog ν) I := fun τ hτ hmem =>
    hZav τ hτ ((recAvoid_iff P.junk _ _ _ _ _ hE _).2 hmem)
  have hcore := c57_core (j := escJ n) hj4 (u := u) (I := I) (i := i) hi
    (ent5 n tn u β' i hlog ν) (escPoint n (escJ n) u) (β' : ℝ) n L7 t7 ht7
    (fun r hr hl => ent5_walk1_left n tn u β' i hlog ν hr hl)
    (fun m hm1 hmI => ent5_data_mid n tn u β' i hlog ν hm1 hmI)
    (fun R hR r hr hl hin => ent5_HV n tn u β' i hlog ν hi.1 hi.2 hR hr hl hin)
    (fun m hm1 hmI hmi r hr hl => ent5_HD n tn u β' i hlog ν hm1 hmI hi.1 hi.2 hmi hr hl)
    R hR q w Z hq0 hpQ Hb Hc S hS0 hS4 hZ57.1 hZ57.2 hZfar hZav' hL7 hβ hnL
  have hng : cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) (N ω) = N ω := by
    simp [cycNgood, hgN]
  have hew : exitPath (δ ω) (N ω) = w := by
    unfold exitPath
    rw [hng]
  show ExitJ (escQ (escJ n) u) (escFace (escJ n) u) (S : ℝ≥0∞) (exitPath (δ ω) (N ω)).1
  rw [hew]
  exact hcore

end

end ElboimSly.Paper.Escape
