/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncNth
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import ElboimSly.Foundations.Cyclic.CycRingMeasure
public import ElboimSly.Foundations.Cyclic.CycRecMeasA
public import Mathlib

/-!
# Several walks explored one after another (a), Step 2 (III): `N|_{R_T} = cycRM(cycRec^𝒫(T))` almost surely

Several walks explored one after another (a), Step 2, last sentences, using basic properties of world-lines (b)
(`restrict_region_eq_rm`). Every entry of `Trunc_s(ρ^𝒫(ν))` is an initial piece of an environment
world-line (`trunc_envFinal_initial`), so for good `ν`, `ν|_{R^𝒫_s} = RM(Trunc_s ρ^𝒫(ν))`, for all
`s` simultaneously. Consequently, almost surely, `N|_{R_T} = RM(cycRec^𝒫(T))` on `{T < ∞}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
/-- Every entry of `Trunc_s(ρ^𝒫(ν))` is an initial piece of an environment world-line. -/
theorem trunc_envFinal_initial (ν : Measure (CycS I d β)) (s : ℝ≥0) :
    ∀ e, (CycRec.trunc s (P.envFinal ν)).IsEntry e →
      ∃ ℓ : ℝ≥0∞, e = (e.1, (envPath ν e.1).cut ℓ) := by
  classical
  rintro e ⟨k, hk⟩
  rw [CycSchemeEnv.trunc_envFinal_nth (P := P) (ν := ν) P.junk s k] at hk
  split_ifs at hk with hc
  have he := Option.some.inj hk
  subst he
  unfold CycSchemeEnv.tgt
  split_ifs with hl
  · exact ⟨_, rfl⟩
  · push Not at hl
    refine ⟨(s : ℝ≥0∞) - CycSchemeEnv.lam P ν k, ?_⟩
    have hle : (s : ℝ≥0∞) - CycSchemeEnv.lam P ν k ≤ (P.E (CycSchemeEnv.rule P ν) k).len := by
      rw [tsub_le_iff_left]
      exact hl.le
    show CycEntry.cut (CycSchemeEnv.dat P ν k, (CycSchemeEnv.pth P ν k).cut
        (sInf (CycSchemeEnv.cand P ν k))) ((s : ℝ≥0∞) - CycSchemeEnv.lam P ν k) = _
    refine Prod.ext rfl (Subtype.ext ?_)
    show ((CycSchemeEnv.pth P ν k).1.cut (sInf (CycSchemeEnv.cand P ν k))).cut
        ((s : ℝ≥0∞) - CycSchemeEnv.lam P ν k) =
      ((envPath ν (CycSchemeEnv.dat P ν k)).1.cut ((s : ℝ≥0∞) - CycSchemeEnv.lam P ν k))
    have hlen : (P.E (CycSchemeEnv.rule P ν) k).len = sInf (CycSchemeEnv.cand P ν k) := by
      rw [CycSchemeEnv.E_eq]
      exact CPath.cut_len _ _
    exact CPath.cut_cut _ (hlen ▸ hle)

section ae

variable {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} {N : Ω → Measure (CycS I d β)}

/-- Almost surely, for all `s`, `N|_{R^𝒫_s} = RM(cycRec^𝒫(s))`. -/
theorem ae_restrict_cycRegionAt (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr) :
    ∀ᵐ ω ∂Pr, ∀ s : ℝ≥0, (N ω).restrict (cycRegionAt P N s ω) =
      (CycRec.trunc s (P.envFinal (N ω))).rm β := by
  filter_upwards [CycSchemeEnv.ae_cycGood' hN] with ω hω s
  exact restrict_region_eq_rm hω (trunc_envFinal_initial P (N ω) s)

/-- Several walks explored one after another (a), Step 2: almost surely, on `{T < ∞}`,
`N|_{R_T} = cycRM(cycRec^𝒫(T))`. -/
theorem ae_restrict_cycRegionStop (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
    (T : Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂Pr, T ω ≠ ⊤ → (N ω).restrict (cycRegionStop P N T ω) =
      (cycRecStop P N T ω).rm β := by
  filter_upwards [ae_restrict_cycRegionAt P hN] with ω hω hT
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hT
  have e1 : ElboimSly.SRW.stopReal T ω = a := by
    unfold ElboimSly.SRW.stopReal; rw [← ha]; rfl
  have e2 : cycRegionStop P N T ω = cycRegionAt P N a ω := by
    unfold cycRegionStop; rw [← ha]; rfl
  rw [e2, hω a]
  unfold cycRecStop
  rw [e1]

end ae

omit [Fact (0 < β)] in
/-- `ω ↦ RM(cycRec^𝒫(T))` is `ℱ_T`-measurable; with `ae_restrict_cycRegionStop` this says that
`N|_{R_T}` is a.s. equal to an `ℱ_T`-measurable random measure. -/
theorem measurable_rm_cycRecStop {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Filtration ℝ≥0 mΩ}
    {T : Ω → WithTop ℝ≥0} {N : Ω → Measure (CycS I d β)}
    (hR : ∀ s, Measurable[f s] fun ω => CycRec.trunc s (P.envFinal (N ω)))
    (hT : IsStoppingTime f T) :
    Measurable[hT.measurableSpace] fun ω => (cycRecStop P N T ω).rm β :=
  CycRec.measurable_rm.comp (measurable_cycRecStop hR hT)

end ElboimSly.Cyclic

end
