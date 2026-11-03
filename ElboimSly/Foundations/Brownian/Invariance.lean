/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Law
import Mathlib

/-!
# Invariances of Brownian motion

Invariances.

All four statements are derived from one criterion, `isStandardBrownianMotion_of_twoTerms`: a
process whose real coordinates are fixed two-term linear combinations of coordinates of a standard
Brownian motion, with the correct covariance, is a standard Brownian motion
(gaussian-process characterization).

* `IsStandardBrownianMotion.scaling`: (a), `t ↦ a B(c t)` with `a² c = 1`;
  `IsStandardBrownianMotion.scaling_lambda` is the form `λ B(t / λ²)`.
* `IsStandardBrownianMotion.shift`: (b), `B(a + t) - B(a)`.
* `IsStandardBrownianMotion.signedSubvector`: (c) and (d), `t ↦ (ε_k B(t)_{ι k})_k`;
  `signedPerm` and `subvector` are the two special cases and `coord` is the 1-dimensional case.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d d' : ℕ}

/-- A linear combination of two coordinates (with a fixed coefficient pair) of a Gaussian process
is a Gaussian process. -/
lemma isGaussianProcess_twoTerms {S T : Type*} {X : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    (u v : S → T) (α β : S → ℝ) :
    IsGaussianProcess (fun s ω => α s * X (u s) ω + β s * X (v s) ω) P := by
  classical
  refine hX.of_isGaussianProcess fun s => ⟨{u s, v s}, ?_⟩
  refine ⟨{ toFun := fun x => α s * x ⟨u s, by simp⟩ + β s * x ⟨v s, by simp⟩
            map_add' := fun x y => by simp only [Pi.add_apply]; ring
            map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
                                       ring }, ?_⟩
  intro ω
  rfl

lemma covariance_twoTerms [IsFiniteMeasure P] {Y1 Y2 Z1 Z2 : Ω → ℝ} (hY1 : MemLp Y1 2 P)
    (hY2 : MemLp Y2 2 P) (hZ1 : MemLp Z1 2 P) (hZ2 : MemLp Z2 2 P) (a b a' b' : ℝ) :
    cov[fun ω => a * Y1 ω + b * Y2 ω, fun ω => a' * Z1 ω + b' * Z2 ω; P] =
      a * a' * cov[Y1, Z1; P] + a * b' * cov[Y1, Z2; P] + b * a' * cov[Y2, Z1; P] +
        b * b' * cov[Y2, Z2; P] := by
  have m1 : MemLp (fun ω => a * Y1 ω) 2 P := hY1.const_mul a
  have m2 : MemLp (fun ω => b * Y2 ω) 2 P := hY2.const_mul b
  have n1 : MemLp (fun ω => a' * Z1 ω) 2 P := hZ1.const_mul a'
  have n2 : MemLp (fun ω => b' * Z2 ω) 2 P := hZ2.const_mul b'
  have e1 : (fun ω => a * Y1 ω + b * Y2 ω) = (fun ω => a * Y1 ω) + (fun ω => b * Y2 ω) := rfl
  have e2 : (fun ω => a' * Z1 ω + b' * Z2 ω) = (fun ω => a' * Z1 ω) + (fun ω => b' * Z2 ω) := rfl
  rw [e1, e2, covariance_add_left m1 m2 (n1.add n2), covariance_add_right m1 n1 n2,
    covariance_add_right m2 n1 n2]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- The covariance kernel of the coordinates `δ_{ij} min(s,t)`. -/
def bmKernel (p q : Σ _ : Fin d, ℝ≥0) : ℝ := if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0

/-- Criterion for standard Brownian motion: a process of two-term linear combinations of the
coordinates of a standard Brownian motion with the right covariance. Used for
Invariances. -/
theorem isStandardBrownianMotion_of_twoTerms [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P)
    (B' : ℝ≥0 → Ω → (Fin d' → ℝ)) (h0 : ∀ t, Measurable (B' t))
    (h1 : ∀ ω, Continuous (fun t => B' t ω) ∧ B' 0 ω = 0)
    (u v : (Σ _ : Fin d', ℝ≥0) → Σ _ : Fin d, ℝ≥0) (α β : (Σ _ : Fin d', ℝ≥0) → ℝ)
    (hdef : ∀ p ω, B' p.2 ω p.1 = α p * B (u p).2 ω (u p).1 + β p * B (v p).2 ω (v p).1)
    (hcov : ∀ p q : Σ _ : Fin d', ℝ≥0,
      α p * α q * bmKernel (u p) (u q) + α p * β q * bmKernel (u p) (v q) +
        β p * α q * bmKernel (v p) (u q) + β p * β q * bmKernel (v p) (v q) =
        if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0) :
    IsStandardBrownianMotion d' B' P := by
  have hfun : (fun (p : Σ _ : Fin d', ℝ≥0) ω => B' p.2 ω p.1) =
      fun p ω => α p * B (u p).2 ω (u p).1 + β p * B (v p).2 ω (v p).1 := by
    funext p ω; exact hdef p ω
  have hmem : ∀ p : Σ _ : Fin d, ℝ≥0, MemLp (fun ω => B p.2 ω p.1) 2 P := fun p =>
    ((hB.isPreBrownianReal p.1).isGaussianProcess.hasGaussianLaw_eval p.2).memLp_two
  refine isStandardBrownianMotion_of_gaussian h0 h1 ?_ ?_ ?_
  · rw [hfun]
    exact isGaussianProcess_twoTerms hB.isGaussianProcess u v α β
  · intro p
    simp_rw [hdef]
    have i1 := (hmem (u p)).integrable (by norm_num)
    have i2 := (hmem (v p)).integrable (by norm_num)
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      hB.integral_eval, hB.integral_eval]
    simp
  · intro p q
    have e : (fun ω => B' p.2 ω p.1) = fun ω => α p * B (u p).2 ω (u p).1 +
        β p * B (v p).2 ω (v p).1 := funext fun ω => hdef p ω
    have e' : (fun ω => B' q.2 ω q.1) = fun ω => α q * B (u q).2 ω (u q).1 +
        β q * B (v q).2 ω (v q).1 := funext fun ω => hdef q ω
    rw [e, e', covariance_twoTerms (hmem _) (hmem _) (hmem _) (hmem _)]
    rw [← hcov p q]
    simp only [bmKernel, hB.covariance_eval]

/-! ### Scaling -/

/-- Invariances (a), scaling. If `a² c = 1`, then `t ↦ a B(c t)` is a standard
Brownian motion. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.scaling [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {a : ℝ} {c : ℝ≥0}
    (_hc : c ≠ 0) (hac : a ^ 2 * c = 1) :
    IsStandardBrownianMotion d (fun t ω => a • B (c * t) ω) P := by
  refine isStandardBrownianMotion_of_twoTerms hB _ ?_ ?_
    (fun p => ⟨p.1, c * p.2⟩) (fun p => ⟨p.1, c * p.2⟩) (fun _ => a) (fun _ => 0) ?_ ?_
  · intro t
    exact (hB.measurable (c * t)).const_smul a
  · intro ω
    refine ⟨?_, by simp [(hB.continuous_zero ω).2]⟩
    exact ((hB.continuous_zero ω).1.comp (continuous_const.mul continuous_id)).const_smul a
  · intro p ω; simp
  · intro p q
    simp only [bmKernel, zero_mul, mul_zero, add_zero]
    split_ifs with h
    · have hm : (min (c * p.2) (c * q.2) : ℝ≥0) = c * min p.2 q.2 :=
        (mul_min_of_nonneg _ _ zero_le).symm
      rw [hm, NNReal.coe_mul, show a * a * ((c : ℝ) * ((min p.2 q.2 : ℝ≥0) : ℝ)) =
        (a ^ 2 * c) * ((min p.2 q.2 : ℝ≥0) : ℝ) by ring, hac, one_mul]
    · simp

/-- Invariances (a), scaling, in the form `t ↦ λ B(t / λ²)`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.scaling_lambda [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {lam : ℝ≥0}
    (hl : lam ≠ 0) :
    IsStandardBrownianMotion d (fun t ω => (lam : ℝ) • B (t / lam ^ 2) ω) P := by
  have hl2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have h := hB.scaling (a := (lam : ℝ)) (c := (lam ^ 2)⁻¹) (inv_ne_zero hl2) (by
    rw [NNReal.coe_inv, NNReal.coe_pow]
    have : (lam : ℝ) ≠ 0 := by exact_mod_cast hl
    field_simp)
  simpa only [div_eq_inv_mul] using h

/-! ### Shift -/

/-- Invariances (b), shift. `t ↦ B(a + t) - B(a)` is a standard Brownian
motion. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.shift [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (a : ℝ≥0) :
    IsStandardBrownianMotion d (fun t ω => B (a + t) ω - B a ω) P := by
  refine isStandardBrownianMotion_of_twoTerms hB _ ?_ ?_
    (fun p => ⟨p.1, a + p.2⟩) (fun p => ⟨p.1, a⟩) (fun _ => 1) (fun _ => -1) ?_ ?_
  · intro t
    exact (hB.measurable (a + t)).sub (hB.measurable a)
  · intro ω
    refine ⟨?_, by simp⟩
    exact ((hB.continuous_zero ω).1.comp (continuous_const.add continuous_id)).sub continuous_const
  · intro p ω; simp [sub_eq_add_neg]
  · intro p q
    simp only [bmKernel]
    split_ifs with h
    · have e1 : min (a + p.2) (a + q.2) = a + min p.2 q.2 := min_add_add_left _ _ _
      have e2 : min (a + p.2) a = a := min_eq_right (by simp)
      have e3 : min a (a + q.2) = a := min_eq_left (by simp)
      rw [e1, e2, e3, min_self]
      push_cast
      ring
    · simp

/-! ### Signed sub-vectors, permutations -/

/-- Invariances (c), (d). For an injective `ι : Fin d' → Fin d` and signs
`ε_k = ±1`, `t ↦ (ε_k B(t)_{ι k})_k` is a standard `d'`-dimensional Brownian motion. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.signedSubvector [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {ι : Fin d' → Fin d}
    (hι : Function.Injective ι) (ε : Fin d' → ℝ) (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    IsStandardBrownianMotion d' (fun t ω k => ε k * B t ω (ι k)) P := by
  refine isStandardBrownianMotion_of_twoTerms hB _ ?_ ?_
    (fun p => ⟨ι p.1, p.2⟩) (fun p => ⟨ι p.1, p.2⟩) (fun p => ε p.1) (fun _ => 0) ?_ ?_
  · intro t
    exact measurable_pi_iff.2 fun k => (((measurable_pi_apply (ι k)).comp (hB.measurable t))).const_mul _
  · intro ω
    refine ⟨continuous_pi fun k => continuous_const.mul
      (((continuous_apply (ι k)).comp (hB.continuous_zero ω).1)), ?_⟩
    funext k
    simp [(hB.continuous_zero ω).2]
  · intro p ω; simp
  · intro p q
    simp only [bmKernel, zero_mul, mul_zero, add_zero]
    by_cases h : p.1 = q.1
    · have h' : ι p.1 = ι q.1 := by rw [h]
      simp only [h, ite_true]
      have hsq : ε q.1 * ε q.1 = 1 := by
        rcases hε q.1 with h1 | h1 <;> rw [h1] <;> norm_num
      rw [hsq, one_mul]
    · have h' : ¬ ι p.1 = ι q.1 := fun e => h (hι e)
      simp [h, h']

/-- Invariances (c), signed permutations. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.signedPerm [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (π : Equiv.Perm (Fin d))
    (ε : Fin d → ℝ) (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    IsStandardBrownianMotion d (fun t ω k => ε k * B t ω (π k)) P :=
  hB.signedSubvector π.injective ε hε

/-- Invariances (c), reflection. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.neg [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) :
    IsStandardBrownianMotion d (fun t ω k => -B t ω k) P := by
  have := hB.signedSubvector (ι := id) Function.injective_id (fun _ => -1) (fun _ => Or.inr rfl)
  simpa using this

/-- Invariances (d), sub-vectors. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.subvector [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) {ι : Fin d' → Fin d}
    (hι : Function.Injective ι) :
    IsStandardBrownianMotion d' (fun t ω k => B t ω (ι k)) P := by
  simpa using hB.signedSubvector hι (fun _ => 1) (fun _ => Or.inl rfl)

/-- Invariances (d), coordinates: each coordinate of a standard Brownian
motion is a standard `1`-dimensional Brownian motion. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.coord [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (i : Fin d) :
    IsStandardBrownianMotion 1 (fun t ω (_ : Fin 1) => B t ω i) P :=
  hB.subvector (ι := fun _ => i) fun _ _ _ => Subsingleton.elim _ _

end ElboimSly.Brownian
