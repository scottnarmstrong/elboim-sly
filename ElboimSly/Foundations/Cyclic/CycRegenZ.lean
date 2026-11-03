/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenRecordTrunc
public import ElboimSly.Foundations.Cyclic.CycRegenShiftEnv
public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import Mathlib

/-!
# ES22 Lemma 2.1: the record-to-piece identification `Z = (k_T, W(T), L_T)`

ES22 Lemma 2.1, proof, "Freezing": `Z = (k_T, W(T), L_T)` is the number of
entries of `cycRec^{𝒫_reg}(T)` (minus one), and the endpoint and length of its last entry, so it
is a measurable function `recZ` of the record (`measurable_recZ`), hence `ℱ_T`-measurable; and for
a good environment `recZ` of the truncated record at `t` is `(k_t, W(t), t - α(t))`
(`recZ_trunc_regPlan`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open CycSchemeEnv

variable {d : ℕ}

/-- The endpoint of a path of finite length, read at the integer `⌈ℓ⌉`, where the path is
constant. -/
noncomputable def entryEnd (e : CycEntry ℕ d) : Fin d → ℤ :=
  e.path.fn (⌈e.len.toNNReal⌉₊ : ℝ≥0)

/-- `Z(ρ) = (number of entries - 1, endpoint of the last entry, length of the last entry)`. -/
noncomputable def recZ (junk : CycEntry ℕ d) (ρ : CycRec ℕ d) : ShiftPar d :=
  (ρ.num.toNat - 1, entryEnd (ρ.coord junk (ρ.num.toNat - 1)),
    ((ρ.coord junk (ρ.num.toNat - 1)).len.toNNReal : ℝ))

theorem measurable_entryEnd : Measurable (entryEnd (d := d)) := by
  have h1 : Measurable fun e : CycEntry ℕ d => (⌈e.len.toNNReal⌉₊ : ℕ) := by
    refine (Nat.measurable_ceil (R := ℝ≥0)).comp ?_
    exact ENNReal.measurable_toNNReal.comp
      (CPath.measurable_len.comp (measurable_subtype_coe.comp measurable_snd))
  have h2 : Measurable fun q : CycEntry ℕ d × ℕ => q.1.path.fn (q.2 : ℝ≥0) :=
    measurable_from_prod_countable_left fun n =>
      (CPath.measurable_eval (n : ℝ≥0)).comp (measurable_subtype_coe.comp measurable_snd)
  exact h2.comp (measurable_id.prodMk h1)

theorem measurable_recZ (junk : CycEntry ℕ d) : Measurable (recZ junk) := by
  have hn : Measurable fun ρ : CycRec ℕ d => ρ.num.toNat - 1 :=
    (measurable_of_countable (fun n : ℕ => n - 1)).comp
      ((measurable_of_countable (ENat.toNat)).comp CycRec.measurable_num)
  have hcoord : Measurable fun ρ : CycRec ℕ d => ρ.coord junk (ρ.num.toNat - 1) := by
    have : Measurable fun q : CycRec ℕ d × ℕ => q.1.coord junk q.2 :=
      measurable_from_prod_countable_left fun n => CycRec.measurable_coord junk n
    exact this.comp (measurable_id.prodMk hn)
  refine hn.prodMk ((measurable_entryEnd.comp hcoord).prodMk ?_)
  exact measurable_coe_nnreal_real.comp (ENNReal.measurable_toNNReal.comp
    (CPath.measurable_len.comp (measurable_subtype_coe.comp (measurable_snd.comp hcoord))))

variable {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace d β)}

theorem recZ_trunc_regPlan (hν : CycGood ν) (t : ℝ≥0) :
    recZ ((regPlan d β).junk) (CycRec.trunc t ((regPlan d β).envFinal ν)) =
      (ElboimSly.regenCount (slices ν) (t : ℝ),
        ElboimSly.regenWalk (slices ν) (t : ℝ), (regLast ν t : ℝ)) := by
  set N := ElboimSly.regenCount (slices ν) (t : ℝ) with hN
  have hnum := num_trunc_regPlan hν t
  have hn : (CycRec.trunc t ((regPlan d β).envFinal ν)).num.toNat - 1 = N := by
    rw [hnum, ENat.toNat_natCast]; omega
  have hc := coord_trunc_regPlan_last hν t ((regPlan d β).junk)
  unfold recZ
  rw [hn, hc]
  have hlen : (((regPlan d β).E (rule (regPlan d β) ν) N).cut (regLast ν t : ℝ≥0∞)).len =
      (regLast ν t : ℝ≥0∞) := CycEntry.len_cut _ _
  have hLt : (regLast ν t : ℝ≥0∞) ≤ ElboimSly.cycTreg (cycSlice N ν) := regLast_le_treg t
  have hw : ElboimSly.regenWalk (slices ν) (t : ℝ) =
      ElboimSly.cycWalk (cycSlice N ν) 0 0 (regLast ν t : ℝ) := by
    unfold ElboimSly.regenWalk
    rw [← regLast_coe]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · dsimp only
    unfold entryEnd
    rw [hlen, ENNReal.toNNReal_coe, hw]
    show ((((regPlan d β).E (rule (regPlan d β) ν) N).path.cut (regLast ν t : ℝ≥0∞)).fn _) = _
    rw [CPath.cut_fn]
    have hmin : min ((⌈regLast ν t⌉₊ : ℝ≥0) : ℝ≥0∞) (regLast ν t : ℝ≥0∞) = (regLast ν t : ℝ≥0∞) :=
      min_eq_right (by exact_mod_cast Nat.le_ceil _)
    rw [hmin, ENNReal.toNNReal_coe]
    exact (regPlan_E_env hν N).2 _ hLt
  · dsimp only
    rw [hlen, ENNReal.toNNReal_coe]

end ElboimSly.Cyclic

end
