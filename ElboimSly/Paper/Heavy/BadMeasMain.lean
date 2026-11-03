/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.BadMeasV3c
public import ElboimSly.Paper.Heavy.BadAttained

/-!
# Properties of discovered bad blocks: measurability

Properties of discovered bad blocks (c), (d); the stopping time heavyBad.

* `AdaptedCyclic.measurableSet_badByTime`: "`B` bad by time `t`" is `ℱ_t`-measurable; `b_t` is
  adapted (`AdaptedCyclic.measurable_badCount`).
* `heavyBadTime`: `inf {t ≥ 0 : b_t ≥ ℓ}`; `AdaptedCyclic.isStoppingTime_heavyBadTime`.
* `heavyTauBad` (the stopping time heavyBad) and `AdaptedCyclic.isStoppingTime_heavyTauBad`.
* The same statements on the path space `CycPathSpace` (with `ℓ = n + 1`, respectively `ℓ = 1`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m}
  {W : Ω → ℝ → Fin d → ℤ} {β t₀ : ℝ} {n : ℕ} {ι : Fin d → ℤ}

/-- Properties of discovered bad blocks (c): badness by time `t` is `ℱ_t`-measurable. -/
theorem AdaptedCyclic.measurableSet_badByTime (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | BadByTime d β t₀ n (W ω) ι t} := by
  have hset : {ω | BadByTime d β t₀ n (W ω) ι t} =
      {ω | BadV1 d β t₀ n (W ω) ι t} ∪ ({ω | BadV2 d β t₀ n (W ω) ι t} ∪
        {ω | BadV3 d β t₀ n (W ω) ι t}) := by
    ext ω; simp only [badByTime_iff, mem_ofPred_eq, mem_union]
  rw [hset]
  exact (h.measurableSet_badV1 hβ htk t).union ((h.measurableSet_badV2 hβ htk t).union
    (h.measurableSet_badV3 hβ htk t))

theorem le_badCount_iff_finset {w : ℝ → Fin d → ℤ} (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ) (ℓ : ℕ) :
    ℓ ≤ badCount d β t₀ n w t ↔
      ∃ F : Finset (Fin d → ℤ), F.card = ℓ ∧ ∀ ι ∈ F, BadByTime d β t₀ n w ι t := by
  have hfin := badSet_finite (w := w) hβ htk t
  constructor
  · intro hℓ
    obtain ⟨T, hTs, hTn⟩ := Set.exists_subset_card_eq hℓ
    have hTfin : T.Finite := hfin.subset hTs
    refine ⟨hTfin.toFinset, ?_, fun ι hι => hTs (hTfin.mem_toFinset.1 hι)⟩
    rw [← hTn, Set.ncard_eq_toFinset_card T hTfin]
  · rintro ⟨F, hF, hFb⟩
    have : (F : Set (Fin d → ℤ)) ⊆ {ι | BadByTime d β t₀ n w ι t} := fun ι hι => hFb ι hι
    have := Set.ncard_le_ncard this hfin
    rw [Set.ncard_coe_finset] at this
    unfold badCount
    omega

/-- `{ℓ ≤ b_t}` is `ℱ_t`-measurable. -/
theorem AdaptedCyclic.measurableSet_le_badCount (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ≥0) (ℓ : ℕ) :
    MeasurableSet[f t] {ω | ℓ ≤ badCount d β t₀ n (W ω) t} := by
  have hset : {ω | ℓ ≤ badCount d β t₀ n (W ω) t} =
      ⋃ F : Finset (Fin d → ℤ), ⋃ _ : F.card = ℓ,
        ⋂ ι ∈ F, {ω | BadByTime d β t₀ n (W ω) ι t} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
    exact le_badCount_iff_finset hβ htk t ℓ
  rw [hset]
  exact MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ =>
    Finset.measurableSet_biInter F fun ι _ => h.measurableSet_badByTime hβ htk t

/-- Properties of discovered bad blocks (c): `b_t` is adapted. -/
theorem AdaptedCyclic.measurable_badCount (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (t : ℝ≥0) :
    Measurable[f t] (fun ω => badCount d β t₀ n (W ω) t) := by
  let : MeasurableSpace Ω := f t
  refine measurable_to_nat fun ω => ?_
  have : (fun ω' => badCount d β t₀ n (W ω') t) ⁻¹' {badCount d β t₀ n (W ω) t} =
      {ω' | badCount d β t₀ n (W ω) t ≤ badCount d β t₀ n (W ω') t} \
        {ω' | badCount d β t₀ n (W ω) t + 1 ≤ badCount d β t₀ n (W ω') t} := by
    ext ω'
    simp only [mem_preimage, mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
    omega
  rw [this]
  exact (h.measurableSet_le_badCount hβ htk t _).diff (h.measurableSet_le_badCount hβ htk t _)

/-- `inf {t ≥ 0 : b_t ≥ ℓ}`. -/
noncomputable def heavyBadTime (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (ℓ : ℕ) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ | 0 ≤ t ∧ ℓ ≤ badCount d β t₀ n w t}, ENNReal.ofReal t

/-- The stopping time heavyBad. `τ_bad = inf {t ≥ 0 : b_t > n}` if `t_n^{5δ} > β`, and
`inf {t ≥ 0 : b_t ≥ 1}` otherwise. -/
noncomputable def heavyTauBad (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  if β < indScale t₀ n ^ (5 * indDelta d) then heavyBadTime d β t₀ n w (n + 1)
  else heavyBadTime d β t₀ n w 1

theorem heavyBadTime_le_iff {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (ℓ : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    heavyBadTime d β t₀ n w ℓ ≤ ENNReal.ofReal T ↔ ℓ ≤ badCount d β t₀ n w T := by
  rcases badCount_dichotomy hw hβ htk ℓ with hno | ⟨m, hm0, hm⟩
  · have hempty : {t : ℝ | 0 ≤ t ∧ ℓ ≤ badCount d β t₀ n w t} = ∅ :=
      Set.eq_empty_of_forall_notMem fun t ht => hno t ht.1 ht.2
    have : heavyBadTime d β t₀ n w ℓ = ⊤ := by
      unfold heavyBadTime; rw [hempty]; simp
    rw [this]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h (hno T hT)⟩
  · have hset : {t : ℝ | 0 ≤ t ∧ ℓ ≤ badCount d β t₀ n w t} = Ici m := by
      ext t
      simp only [mem_ofPred_eq, mem_Ici]
      exact ⟨fun h => (hm t h.1).1 h.2, fun h => ⟨hm0.trans h, (hm t (hm0.trans h)).2 h⟩⟩
    have : heavyBadTime d β t₀ n w ℓ = ENNReal.ofReal m := by
      unfold heavyBadTime; rw [hset]
      exact le_antisymm (iInf₂_le m le_rfl)
        (le_iInf₂ fun t ht => ENNReal.ofReal_le_ofReal ht)
    rw [this, ENNReal.ofReal_le_ofReal_iff hT]
    exact (hm T hT).symm

theorem AdaptedCyclic.isStoppingTime_heavyBadTime (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (ℓ : ℕ) :
    IsStoppingTime f (fun ω => heavyBadTime d β t₀ n (W ω) ℓ) := by
  intro i
  have hset : {ω | heavyBadTime d β t₀ n (W ω) ℓ ≤ (i : WithTop ℝ≥0)} =
      {ω | ℓ ≤ badCount d β t₀ n (W ω) i} := by
    ext ω
    have := heavyBadTime_le_iff (h.path ω) hβ htk ℓ (T := (i : ℝ)) (NNReal.coe_nonneg i)
    simp only [ENNReal.ofReal_coe_nnreal] at this
    exact this
  exact (congrArg (MeasurableSet[f i]) hset).mpr (h.measurableSet_le_badCount hβ htk i ℓ)

/-- The stopping time heavyBad: `τ_bad` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_heavyTauBad (h : AdaptedCyclic f W) (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) :
    IsStoppingTime f (fun ω => heavyTauBad d β t₀ n (W ω)) := by
  unfold heavyTauBad
  split_ifs
  · exact h.isStoppingTime_heavyBadTime hβ htk _
  · exact h.isStoppingTime_heavyBadTime hβ htk _

/-- The stopping time heavyBad: `w ↦ τ_bad(w)` is measurable. -/
theorem measurable_heavyTauBad_cycPath (hβ : 0 < β) (htk : 0 ≤ heavyTkPrime d t₀ n) :
    Measurable (fun p : CycPathSpace d => heavyTauBad d β t₀ n p.1) :=
  (adaptedCyclic_cycPathSpace.isStoppingTime_heavyTauBad hβ htk).measurable'

end ElboimSly.Paper
