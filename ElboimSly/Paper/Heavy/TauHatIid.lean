/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauHatFast
public import ElboimSly.Paper.Heavy.MeasPath
public import ElboimSly.Paper.Heavy.BadMeasMain
public import ElboimSly.Foundations.Cyclic.CycStationary
public import Mathlib

/-!
# The pieces are identically distributed

Regenerated cyclic walk (the pieces `W^{(i)} = W^{N^{i-1}}_{0,0}` are i.i.d.), used in
mathbbP(𝒢(i))ge1-e^-cn^3.

* `measurableSet_gammaSet`: `Γ_n` is a measurable subset of the space of cyclic paths
  (measurability).
* `heavyGamma_iid`: the events `{W^{(k)} ∉ Γ_n}` all have the same probability, for a Poisson
  environment on `ℕ × S_β`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- `Γ_n` as a subset of the space of cyclic paths. -/
def gammaSet (d : ℕ) (β t₀ : ℝ) (n : ℕ) : Set (CycPathSpace d) :=
  {p | heavyGamma d β t₀ n p.1}

theorem measurableSet_gammaSet {t₀ : ℝ} (ht0 : 0 < t₀) {n : ℕ} (hn : 1 ≤ n) :
    MeasurableSet (gammaSet d β t₀ n) := by
  have hβ : 0 < β := Fact.out
  have htk : 0 ≤ heavyTkPrime d t₀ n := by
    unfold heavyTkPrime indScale; positivity
  have hL : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have e : gammaSet d β t₀ n = {p : CycPathSpace d |
      min (cycClosingTime β p.1) (ENNReal.ofReal (indScale t₀ n)) <
        min (pathTfastCube p.1 n) (min (pathTjumpCube p.1 n)
          (min (heavyTauPrime d t₀ n p.1) (heavyTauBad d β t₀ n p.1)))} := by
    ext p
    simp only [gammaSet, heavyGamma, mem_ofPred_eq, p.2, true_and]
  rw [e]
  refine measurableSet_lt ?_ ?_
  · exact (measurable_cycClosingTime_cycPath hβ).min measurable_const
  · exact (measurable_pathTfast_cycPath hL).min ((measurable_pathTjump_cycPath hL).min
      ((measurable_heavyTauPrime_cycPath t₀ hn).min (measurable_heavyTauBad_cycPath hβ htk)))

/-- A measurable set of the space of cyclic paths is the preimage of a measurable set of
`ℝ≥0 → ℤᵈ` under restriction. -/
theorem exists_measurableSet_val {X : Set (CycPathSpace d)} (hX : MeasurableSet X) :
    ∃ S : Set (ℝ≥0 → Fin d → ℤ), MeasurableSet S ∧
      (fun (p : CycPathSpace d) (s : ℝ≥0) => p.1 (s : ℝ)) ⁻¹' S = X := by
  have : (inferInstance : MeasurableSpace (CycPathSpace d)) =
      MeasurableSpace.comap (fun (p : CycPathSpace d) (s : ℝ≥0) => p.1 (s : ℝ))
        MeasurableSpace.pi := by
    unfold MeasurableSpace.pi
    rw [MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    rfl
  have hX' : MeasurableSet[MeasurableSpace.comap
      (fun (p : CycPathSpace d) (s : ℝ≥0) => p.1 (s : ℝ)) MeasurableSpace.pi] X := by
    rw [← this]; exact hX
  obtain ⟨S, hS, h⟩ := MeasurableSpace.measurableSet_comap.1 hX'
  exact ⟨S, hS, h⟩

variable {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}

/-- Regenerated cyclic walk. The events `{W^{(k)} ∉ Γ_n}` have the same probability for all `k`. -/
theorem heavyGamma_iid {t₀ : ℝ} (ht0 : 0 < t₀) {n : ℕ} (hn : 1 ≤ n)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (k : ℕ) :
    Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} =
      Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) 0)} := by
  obtain ⟨S, hS, hSX⟩ := exists_measurableSet_val (measurableSet_gammaSet (d := d) (β := β) ht0 hn)
  set B : Set (Measure (RingSpace d β)) := (fun ν => trajProc ν 0 0) ⁻¹' Sᶜ with hB
  have hBm : MeasurableSet B := (measurable_trajProc 0 0) hS.compl
  have hae : ∀ j : ℕ, {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) j)} =ᵐ[Pe]
      (fun ω => cycSlice j (N ω)) ⁻¹' B := by
    intro j
    filter_upwards [ae_cycGood hN] with ω hω
    have hg : Good (cycSlice j (N ω)) := hω j
    have hcyc := isCyclicPath_cycWalk hg
    have hmem : (⟨fun s : ℝ => cycWalk (cycSlice j (N ω)) 0 0 s, hcyc⟩ : CycPathSpace d) ∈
        gammaSet d β t₀ n ↔ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) j) := Iff.rfl
    have hval : (fun (p : CycPathSpace d) (s : ℝ≥0) => p.1 (s : ℝ))
        ⟨fun s : ℝ => cycWalk (cycSlice j (N ω)) 0 0 s, hcyc⟩ = trajProc (cycSlice j (N ω)) 0 0 := by
      funext s; exact cycWalk_eq_trajProc hg 0 0 s
    have key : (trajProc (cycSlice j (N ω)) 0 0 ∈ S) ↔
        heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) j) := by
      rw [← hval, ← hmem, ← hSX]; rfl
    show ((¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) j)) = (cycSlice j (N ω) ∈ B))
    rw [hB]
    simp only [mem_preimage, mem_compl_iff, key]
  rw [measure_congr (hae k), measure_congr (hae 0)]
  have h0 := isPoissonPointProcess_slice hN 0
  have hj := isPoissonPointProcess_slice hN k
  have hlaw : Pe.map (fun ω => cycSlice k (N ω)) = Pe.map (fun ω => cycSlice 0 (N ω)) :=
    h0.map_eq_map hj
  rw [← Measure.map_apply hj.measurable hBm, ← Measure.map_apply h0.measurable hBm, hlaw]

/-- mathbbP(𝒢(i))ge1-e^-cn^3, conditional only on `hprime` (corollary after Lemma 6.2) and `hbad`
(eq. (tau.bad)): `P(𝒢(i)ᶜ) ≤ A_n e^{-c_♭ n³}`.  The bounds on `τ_fast` and `τ_jump`
(eq. (taufast)) and the identical distribution of the pieces are proved. -/
theorem es6_tauhat_given_prime_bad {E : HeavyEscConsts} {n : ℕ} {t₀ : ℝ} (hd : 5 ≤ d)
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 2 ≤ β) (hn : 1 ≤ n)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hprime : Pe {ω | heavyTauPrime d t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        (n + 1) * 5 ^ (d * (n + 1)) *
          (Real.exp (-((n : ℝ) ^ 3 / 17)) + Real.exp (-(E.c5 * (n : ℝ) ^ 3)))))
    (hbad : Pe {ω | heavyTauBad d β t₀ n (fun s : ℝ => cycWalk (cycSlice 0 (N ω)) 0 0 s) ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (cycSlice 0 (N ω)))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2)) +
        max (Real.exp (-(indDelta d ^ 2 * (n : ℝ) ^ 3 / (2 * 33 ^ d))))
          (Real.exp (-(indDelta d ^ 3 * (n : ℝ) ^ 3 / 2))))) (k : ℕ) :
    Pe {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) k)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3))) :=
  es6_tauhat_of_prime_bad (E := E) hd ht1 ht4 hβ hN hprime hbad
    (fun j => heavyGamma_iid (by linarith) hn hN j) k

end ElboimSly.Paper.Heavy
