/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.PiBij
import Mathlib

/-!
# Agreement with the source definition of `π_s`

Agreement with the source definition.

With `π_{s-}(x) = γ_{x,0}(s-)`: if an edge `{u, v}` rings at `s` then `π_s = (u v) ∘ π_{s-}`;
otherwise `π_s = π_{s-}`. Moreover `π_{s-}` is a bijection and `π_{s'} = π_{s-}` pointwise for `s' < s`
close enough to `s`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

theorem interchangePi_eq_fn (hν : Good ν) (s : ℝ≥0) (x : Fin d → ℤ) :
    interchangePi ν s x = fwdTrajFn hν x 0 s := by
  simp [interchangePi, fwdTrajFn, hν]

theorem exists_isLeftLimit (hν : Good ν) {s : ℝ≥0} (hs : 0 < s) (x : Fin d → ℤ) :
    ∃ z, IsLeftLimit (fwdTrajFn hν x 0) s z :=
  (fwdTrajFn_spec hν x 0).1.2.1 s hs

open scoped Classical in
/-- `π_{s-}(x) = γ_{x,0}(s-)`, the left limit of the trajectory (and `x` if `s = 0`). -/
noncomputable def interchangePiLeft (hν : Good ν) (s : ℝ≥0) (x : Fin d → ℤ) : Fin d → ℤ :=
  if hs : 0 < s then Classical.choose (exists_isLeftLimit hν hs x) else x

theorem interchangePiLeft_isLeftLimit (hν : Good ν) {s : ℝ≥0} (hs : 0 < s) (x : Fin d → ℤ) :
    IsLeftLimit (fwdTrajFn hν x 0) s (interchangePiLeft hν s x) := by
  simp only [interchangePiLeft, hs, ↓reduceDIte]
  exact Classical.choose_spec (exists_isLeftLimit hν hs x)

theorem swapRule_piLeft (hν : Good ν) {s : ℝ≥0} (hs : 0 < s) (x : Fin d → ℤ) :
    SwapRule ν (s : ℝ) (interchangePiLeft hν s x) (interchangePi ν s x) := by
  have := (fwdTrajFn_spec hν x 0).1.2.2.2 s hs _ (interchangePiLeft_isLeftLimit hν hs x)
  rw [interchangePi_eq_fn hν]
  simpa using this

/-- If no edge rings at `s`, then `π_s = π_{s-}`. Agreement with the source definition. -/
theorem interchangePi_eq_left_of_not_rings (hν : Good ν) {s : ℝ≥0} (hs : 0 < s)
    (h : ∀ e : Edge d, ¬ Rings ν e (s : ℝ)) (x : Fin d → ℤ) :
    interchangePi ν s x = interchangePiLeft hν s x :=
  ((swapRule_piLeft hν hs x).2 fun ⟨e, _, he⟩ => h e he)

/-- If the edge `{u, v}` rings at `s`, then `π_s = (u v) ∘ π_{s-}`.
Agreement with the source definition. -/
theorem interchangePi_eq_swap_left (hν : Good ν) {s : ℝ≥0} (hs : 0 < s) (e : Edge d)
    {u v : Fin d → ℤ} (he : e.1 = s(u, v)) (hr : Rings ν e (s : ℝ)) (x : Fin d → ℤ) :
    interchangePi ν s x = Equiv.swap u v (interchangePiLeft hν s x) := by
  have hsw := swapRule_piLeft hν hs x
  set z := interchangePiLeft hν s x
  by_cases hz : e.Mem z
  · have h1 := hsw.1 e hz hr
    rw [he] at h1
    have hz' : z ∈ s(u, v) := by unfold Edge.Mem at hz; rwa [he] at hz
    rcases Sym2.mem_iff.mp hz' with rfl | rfl
    · rw [Equiv.swap_apply_left]
      exact Sym2.congr_right.mp h1.symm
    · rw [Equiv.swap_apply_right]
      rw [Sym2.eq_swap] at h1
      exact (Sym2.congr_right.mp h1).symm
  · have hnone : ¬ ∃ e' : Edge d, e'.Mem z ∧ Rings ν e' (s : ℝ) := by
      rintro ⟨e', he', hr'⟩
      exact hz (edge_unique hν hr' hr ▸ he')
    rw [hsw.2 hnone]
    have hzu : z ≠ u := fun h => hz (by unfold Edge.Mem; rw [he, h]; exact Sym2.mem_mk_left _ _)
    have hzv : z ≠ v := fun h => hz (by unfold Edge.Mem; rw [he, h]; exact Sym2.mem_mk_right _ _)
    exact (Equiv.swap_apply_of_ne_of_ne hzu hzv).symm

/-- `π_{s-}` is a bijection. Agreement with the source definition. -/
theorem interchangePiLeft_bijective (hν : Good ν) {s : ℝ≥0} (hs : 0 < s) :
    Function.Bijective (interchangePiLeft hν s) := by
  by_cases hr : ∃ e : Edge d, Rings ν e (s : ℝ)
  · obtain ⟨e, he⟩ := hr
    obtain ⟨u, v, huv, -⟩ := e.2
    have : interchangePiLeft hν s = Equiv.swap u v ∘ interchangePi ν s := by
      funext x
      rw [Function.comp_apply, interchangePi_eq_swap_left hν hs e huv he x, Equiv.swap_apply_self]
    rw [this]
    exact (Equiv.swap u v).bijective.comp (interchangePi_bijective hν s)
  · push Not at hr
    have : interchangePiLeft hν s = interchangePi ν s :=
      funext fun x => (interchangePi_eq_left_of_not_rings hν hs hr x).symm
    rw [this]
    exact interchangePi_bijective hν s

/-- `π_{s'} = π_{s-}` pointwise for `s' < s` close enough to `s`.
Agreement with the source definition. -/
theorem eventually_interchangePi_eq_left (hν : Good ν) {s : ℝ≥0} (hs : 0 < s)
    (x : Fin d → ℤ) : ∀ᶠ s' in 𝓝[<] s, interchangePi ν s' x = interchangePiLeft hν s x := by
  filter_upwards [interchangePiLeft_isLeftLimit hν hs x] with s' hs'
  rw [interchangePi_eq_fn hν]
  exact hs'

end ElboimSly.Interchange
