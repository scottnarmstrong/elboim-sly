/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Tusnady
public import ElboimSly.Foundations.StrongApprox.Quantile

/-!
# The dyadic tree (recursive form)

The dyadic tree of depth 2L (Part I). The tree is built by
recursion on the depth `n`: the Gaussian data `DT n` of a depth-`n` tree is a root coordinate and two
subtrees of depth `n - 1`. A node of level `n + 1` with Poisson count `m` and Gaussian value `g`
splits with the coordinate `y` into the children `(saq m y, g/2 + √(2^(n+1)) y / 2)` and
`(m - saq m y, g/2 - √(2^(n+1)) y / 2)`. This is the construction of the written proof, with nodes
addressed by their position in the recursion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ElboimSly
namespace StrongApprox

/-- Gaussian data of a dyadic tree of depth `n` (one coordinate per internal node). -/
def DT : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × DT n × DT n

instance instMeasurableSpaceDT : (n : ℕ) → MeasurableSpace (DT n)
  | 0 => (inferInstance : MeasurableSpace Unit)
  | n + 1 =>
    letI := instMeasurableSpaceDT n
    (inferInstance : MeasurableSpace (ℝ × DT n × DT n))

/-- The law of the Gaussian data: all coordinates are independent standard normal. -/
noncomputable def muDT : (n : ℕ) → Measure (DT n)
  | 0 => Measure.dirac ()
  | n + 1 => saN.prod ((muDT n).prod (muDT n))

instance isProbabilityMeasure_saN : IsProbabilityMeasure saN := by
  unfold saN; infer_instance

theorem isProbabilityMeasure_muDT : (n : ℕ) → IsProbabilityMeasure (muDT n)
  | 0 => by
    change IsProbabilityMeasure (Measure.dirac ())
    infer_instance
  | n + 1 => by
    have := isProbabilityMeasure_muDT n
    change IsProbabilityMeasure (saN.prod ((muDT n).prod (muDT n)))
    infer_instance

instance (n : ℕ) : IsProbabilityMeasure (muDT n) := isProbabilityMeasure_muDT n

section Coordinates

theorem measurable_dt_fst (n : ℕ) : Measurable (fun d : DT (n + 1) => d.1) :=
  measurable_fst

theorem measurable_dt_left (n : ℕ) : Measurable (fun d : DT (n + 1) => d.2.1) :=
  measurable_fst.comp measurable_snd

theorem measurable_dt_right (n : ℕ) : Measurable (fun d : DT (n + 1) => d.2.2) :=
  measurable_snd.comp measurable_snd

end Coordinates

/-- The scale `√(2^(n+1))` of the Gaussian split at a node of level `n + 1`. -/
noncomputable def sc (n : ℕ) : ℝ := √((2 : ℝ) ^ (n + 1))

/-- Gaussian value of the left child. -/
noncomputable def gL (n : ℕ) (g y : ℝ) : ℝ := g / 2 + sc n * y / 2

/-- Gaussian value of the right child. -/
noncomputable def gR (n : ℕ) (g y : ℝ) : ℝ := g / 2 - sc n * y / 2

/-- Poisson leaf variables of the tree of depth `n` started from the count `m`
(The dyadic tree of depth 2L, the variables `ξ_i`, with leaf index starting at `0`). -/
noncomputable def LP : (n : ℕ) → ℕ → DT n → ℕ → ℕ
  | 0, m, _, _ => m
  | n + 1, m, d, i =>
    if i < 2 ^ n then LP n (saq m d.1) d.2.1 i else LP n (m - saq m d.1) d.2.2 (i - 2 ^ n)

/-- Gaussian leaf variables of the tree of depth `n` started from the value `g`
(The dyadic tree of depth 2L, the variables `z_i`). -/
noncomputable def LG : (n : ℕ) → ℝ → DT n → ℕ → ℝ
  | 0, g, _, _ => g
  | n + 1, g, d, i =>
    if i < 2 ^ n then LG n (gL n g d.1) d.2.1 i else LG n (gR n g d.1) d.2.2 (i - 2 ^ n)

/-- The dyadic tree of depth 2L, the error `Δ_v` of a node of level `n + 1` with count `m`. -/
noncomputable def Delta (n : ℕ) (m : ℕ) (y : ℝ) : ℝ := saq m y - m / 2 - sc n * y / 2

/-- Pathwise error bounds(e): `Ψ(j)`, the sum of `|Δ_v|` along the path of the leaf `j`. -/
noncomputable def Psi : (n : ℕ) → ℕ → DT n → ℕ → ℝ
  | 0, _, _, _ => 0
  | n + 1, m, d, j =>
    |Delta n m d.1| +
      if j < 2 ^ n then Psi n (saq m d.1) d.2.1 j else Psi n (m - saq m d.1) d.2.2 (j - 2 ^ n)

/-- The constant `c_T = C_T + 1/4`. -/
noncomputable def cT : ℝ := 2000000000 + 1 / 4

/-- Exponential moments along a path, Step 1: the sum of `3 β_ℓ² + c_T η_ℓ²` along the path. -/
noncomputable def Theta : (n : ℕ) → ℕ → DT n → ℕ → ℝ
  | 0, _, _, _ => 0
  | n + 1, m, d, j =>
    if j < 2 ^ n then
      3 * (√(saq m d.1 : ℝ) - √((m : ℝ) / 2)) ^ 2 + cT * d.1 ^ 2 + Theta n (saq m d.1) d.2.1 j
    else
      3 * (√((m - saq m d.1 : ℕ) : ℝ) - √((m : ℝ) / 2)) ^ 2 + cT * d.1 ^ 2 +
        Theta n (m - saq m d.1) d.2.2 (j - 2 ^ n)

/-- The dyadic tree of depth 2L: the partial sums `S_j = Σ_{i<j} (ξ_i - 1 - z_i)` (0-based). -/
noncomputable def Spart (n : ℕ) (m : ℕ) (g : ℝ) (d : DT n) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, ((LP n m d i : ℝ) - 1 - LG n g d i)

section Measurability

theorem measurable_LP (n : ℕ) (i : ℕ) : Measurable (fun p : ℕ × DT n => LP n p.1 p.2 i) := by
  induction n generalizing i with
  | zero => exact measurable_fst
  | succ n ih =>
    have hq : Measurable (fun p : ℕ × DT (n + 1) => saq p.1 p.2.1) :=
      measurable_saq.comp (measurable_fst.prodMk ((measurable_dt_fst n).comp measurable_snd))
    have hl : Measurable (fun p : ℕ × DT (n + 1) => (saq p.1 p.2.1, p.2.2.1)) :=
      hq.prodMk ((measurable_dt_left n).comp measurable_snd)
    have hr : Measurable (fun p : ℕ × DT (n + 1) => (p.1 - saq p.1 p.2.1, p.2.2.2)) :=
      (measurable_fst.sub hq).prodMk ((measurable_dt_right n).comp measurable_snd)
    simp only [LP]
    by_cases h : i < 2 ^ n
    · simp only [h, ite_true]; exact (ih i).comp hl
    · simp only [h, ite_false]; exact (ih (i - 2 ^ n)).comp hr

theorem measurable_LG (n : ℕ) (i : ℕ) : Measurable (fun p : ℝ × DT n => LG n p.1 p.2 i) := by
  induction n generalizing i with
  | zero => exact measurable_fst
  | succ n ih =>
    have hy : Measurable (fun p : ℝ × DT (n + 1) => p.2.1) :=
      (measurable_dt_fst n).comp measurable_snd
    have hl : Measurable (fun p : ℝ × DT (n + 1) => (gL n p.1 p.2.1, p.2.2.1)) :=
      (by unfold gL; fun_prop : Measurable (fun p : ℝ × DT (n + 1) => gL n p.1 p.2.1)).prodMk
        ((measurable_dt_left n).comp measurable_snd)
    have hr : Measurable (fun p : ℝ × DT (n + 1) => (gR n p.1 p.2.1, p.2.2.2)) :=
      (by unfold gR; fun_prop : Measurable (fun p : ℝ × DT (n + 1) => gR n p.1 p.2.1)).prodMk
        ((measurable_dt_right n).comp measurable_snd)
    simp only [LG]
    by_cases h : i < 2 ^ n
    · simp only [h, ite_true]; exact (ih i).comp hl
    · simp only [h, ite_false]; exact (ih (i - 2 ^ n)).comp hr

theorem measurable_Delta (n : ℕ) : Measurable (fun p : ℕ × ℝ => Delta n p.1 p.2) := by
  have hq : Measurable (fun p : ℕ × ℝ => (saq p.1 p.2 : ℝ)) :=
    (measurable_from_top (f := (Nat.cast : ℕ → ℝ))).comp measurable_saq
  have hm : Measurable (fun p : ℕ × ℝ => (p.1 : ℝ)) :=
    (measurable_from_top (f := (Nat.cast : ℕ → ℝ))).comp measurable_fst
  unfold Delta; fun_prop

theorem measurable_abs_Delta (n : ℕ) : Measurable (fun p : ℕ × ℝ => |Delta n p.1 p.2|) := by
  have := (measurable_Delta n).norm
  simpa only [Real.norm_eq_abs] using this

theorem measurable_Psi (n : ℕ) (j : ℕ) : Measurable (fun p : ℕ × DT n => Psi n p.1 p.2 j) := by
  induction n generalizing j with
  | zero => simp only [Psi]; exact measurable_const
  | succ n ih =>
    have hy : Measurable (fun p : ℕ × DT (n + 1) => p.2.1) :=
      (measurable_dt_fst n).comp measurable_snd
    have hq : Measurable (fun p : ℕ × DT (n + 1) => saq p.1 p.2.1) :=
      measurable_saq.comp (measurable_fst.prodMk hy)
    have hl : Measurable (fun p : ℕ × DT (n + 1) => (saq p.1 p.2.1, p.2.2.1)) :=
      hq.prodMk ((measurable_dt_left n).comp measurable_snd)
    have hr : Measurable (fun p : ℕ × DT (n + 1) => (p.1 - saq p.1 p.2.1, p.2.2.2)) :=
      (measurable_fst.sub hq).prodMk ((measurable_dt_right n).comp measurable_snd)
    have h2 : Measurable (fun p : ℕ × DT (n + 1) => ((p.1, p.2.1) : ℕ × ℝ)) :=
      measurable_fst.prodMk hy
    have hD := (measurable_abs_Delta n).comp h2
    simp only [Psi]
    by_cases h : j < 2 ^ n
    · simp only [h, ite_true]; exact hD.add ((ih j).comp hl)
    · simp only [h, ite_false]; exact hD.add ((ih (j - 2 ^ n)).comp hr)

end Measurability

end StrongApprox
end ElboimSly
