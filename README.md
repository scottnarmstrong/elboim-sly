# Infinite cycles in the interchange process in five dimensions, in Lean

[![Build and verify](https://github.com/scottnarmstrong/elboim-sly/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/elboim-sly/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/elboim-sly/actions/workflows/comparators.yml/badge.svg)](https://github.com/scottnarmstrong/elboim-sly/actions/workflows/comparators.yml)

A complete Lean 4 and Mathlib formalization of

> D. Elboim and A. Sly, *Infinite cycles in the interchange process in five dimensions*,
> [arXiv:2211.17023](https://arxiv.org/abs/2211.17023) (v3, 2024).

In the interchange process on $\mathbb Z^d$, every edge carries an independent Poisson clock of
rate 1, and whenever an edge rings, the particles at its two endpoints swap places. Running the
process for time $\beta$ produces a random permutation $\pi_\beta$ of $\mathbb Z^d$. Tóth conjectured
that $\pi_\beta$ has infinite cycles when $d\ge3$ and $\beta$ is large; Elboim and Sly proved this for
$d\ge5$. This repository proves their theorem in Lean, from Mathlib alone:

- **Theorem 1** (`root_R2`). For $d\ge5$ and $\beta$ large enough, $\pi_\beta$ almost surely has an
  infinite cycle.
- **The quantitative form** (`root_R1`). The cycle of the origin is finite with probability less
  than $2/\beta$.
- **Theorem 3.2** (`ind_main`). The multiscale induction behind both: the hypotheses (H1)–(H5) on the
  cyclic random walk hold at every scale.

None of the results the paper cites is assumed; each is proved in the library. These include:
- the construction of the process on the infinite lattice;
- Poisson point processes and their exploration;
- the zero-one law;
- estimates for continuous-time random walk;
- Brownian motion, constructed from scratch, with the hitting and escape estimates of Section 9;
- Freedman's inequality;
- the strong approximation of random walk by Brownian motion.

The paper's one external theorem, Zaitsev's multidimensional version of the Komlós–Major–Tusnády
(KMT) coupling, is replaced by two couplings proved here. This raises the exponent in (H4) from $2/5$
to $41/100$ and leaves Theorem 1 unchanged. The library contains no `sorry` and uses only Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). It has about 180,000 lines of Lean in
1,323 files.

## Main results

Results are cited as [ES22] (the paper, with the numbering of arXiv:2211.17023v3) and [KMT]
(J. Komlós, P. Major and G. Tusnády, *An approximation of partial sums of independent RV'-s, and the
sample DF. I*, Z. Wahrscheinlichkeitstheorie verw. Gebiete 32 (1975)). Each theorem is in its own
file in [`ElboimSly/Frozen/Theorems/`](ElboimSly/Frozen/Theorems), in the namespace `ElboimSly`. The 57
definitions they use are in [`ElboimSly/Frozen/Defs/`](ElboimSly/Frozen/Defs), one per file.

| Result | Lean theorem |
|---|---|
| [ES22, Theorem 1]: almost surely an infinite cycle, for $d\ge5$ and $\beta$ large | `root_R2` |
| [ES22, proof of Theorem 1]: the cycle of the origin is finite with probability less than $2/\beta$ | `root_R1` |
| [ES22, Theorem 3.2]: (H1)–(H5) at every scale $n\ge n_0$ | `ind_main` |
| Particle trajectories exist and are unique for almost every clock configuration | `existsUnique_trajectories` |
| $\pi_s$ is a bijection of $\mathbb Z^d$ | `interchangePi_bijective` |
| [KMT, Theorem 1] for centred Poisson increments | `poisson_kmt_coupling` |
| Strong approximation of sums of bounded sign-symmetric vectors, replacing [ES22, Theorem 7.5] | `x1theta_coupling` |

Theorem 1 reads as follows:

```lean
theorem root_R2 (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          ∀ᵐ ω ∂P, N ω ∈ infEvent d β
```

Here is what the statement means.
- **The clocks.** The edge clocks are a Poisson point process `N` on `RingSpace d β`, the set of
  edges of $\mathbb Z^d$ times the circle $\mathbb R/\beta\mathbb Z$. Its intensity, `ringIntensity d β`,
  is counting measure times Lebesgue measure.
- **Good configurations.** A clock configuration is `Good` if every edge rings finitely often, no two
  rings coincide, and swap paths of unbounded length do not occur. Almost every configuration is good.
- **The permutation.** For a good configuration every particle has a unique trajectory.
  `interchangePi ν s` sends $x$ to the position at time $s$ of the particle that starts at $x$.

The event

```lean
def infEvent : Set (Measure (RingSpace d β)) :=
  {ν | Good ν ∧ ∃ x : Fin d → ℤ, ∀ k : ℕ, 1 ≤ k → (interchangePi ν β.toNNReal)^[k] x ≠ x}
```

says that some point never returns to itself under $\pi_\beta$, so that it lies on an infinite cycle.
`root_R1` has the same hypotheses and the conclusion
`P {ω | N ω ∈ finZeroEvent d β} < ENNReal.ofReal (2 / β)`.

Theorem 3.2 is stated at the scales $t_n=t_0 4^n$, for every $t_0\in(1,4]$:

```lean
theorem ind_main (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, ∃ n₀ : ℕ, 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        IndHyp d β n t₀
```

`IndHyp d β n t₀` is the conjunction of (H1)–(H5):
- **(H1)–(H4)** concern the regenerated cyclic random walk, built from independent copies of the
  clock process. Its relaxed times have positive density, it satisfies local probability bounds, it
  does not travel far, and it is close to a Brownian motion.
- **(H5)** bounds the time that two cyclic walks in the same environment spend close to each other.

The Brownian coupling of (H4) is a probability measure on pairs of paths whose marginals are the law
of the walk and Wiener measure.

## What is formalized

**[ES22], Sections 2–9.** Every result of the paper that the three theorems above depend on is
proved, in the paper's order:
- **Section 2:** the cyclic walk and its regeneration (Lemmas 2.1 and 2.2, Claim 2.3);
- **Section 3:** the induction hypothesis and Theorem 3.2;
- **Section 4:** avoiding the past from relaxed times (Lemma 4.1, Claims 4.2 and 4.3);
- **Section 5:** the escape algorithm (Theorem 5.1, Proposition 5.2, Lemma 5.3, Corollary 5.4,
  Lemma 5.5, Claims 5.6 and 5.7);
- **Section 6:** heavy blocks and the density of relaxed times (Theorem 6.1 with the results 6.2–6.12);
- **Section 7:** concatenation and the induction step (Lemma 7.1, Corollary 7.2, Lemmas 7.3, 7.4 and
  7.6–7.8, and the step);
- **Section 8:** the base of the induction;
- **Section 9:** the Brownian estimates (Lemmas 9.1–9.3, Claim 9.4).

These are in [`ElboimSly/Paper/`](ElboimSly/Paper), with one directory per section. Theorem 1 follows from the
quantitative bound by a zero-one law for translation-invariant events, which is proved too.

**The model.** The process is constructed on the infinite lattice:
- the Poisson clocks;
- almost-sure goodness;
- existence and uniqueness of trajectories;
- $\pi_s$ and its bijectivity;
- the symmetries and the invariance in law that the paper uses.

**The inputs**, proved from Mathlib in [`ElboimSly/Foundations/`](ElboimSly/Foundations):
- **Poisson point processes.** Existence and uniqueness in law, restriction, superposition, images,
  simplicity, the Mecke formula, and an exploration theorem for point processes revealed along a
  stopping rule.
- **Cyclic walks.** Their environments and driving processes, regeneration, and the law of the
  regenerated walk.
- **Continuous-time simple random walk.** The strong Markov property, reversal, local bounds, Lévy
  and maximal inequalities, hitting and transience.
- **Brownian motion.** The Lévy–Ciesielski construction, Wiener measure, and the estimates of
  Section 9.
- **Concentration.** Chernoff bounds, Bernoulli domination and Freedman's inequality.
- **Strong approximation.** Two couplings:
  - [KMT, Theorem 1] for centred Poisson increments, with error $C\log N$. It is built from a dyadic
    coupling and a Tusnády-type quantile bound for $\mathrm{Bin}(m,\frac12)$.
  - A coupling of sums of $\ell$ bounded, sign-symmetric vectors with Gaussian sums, with error
    $\ell^{1/4}(\log\ell)^{12}$ except on an event of probability $e^{-(\log\ell)^3}$. It is proved
    through a sign-symmetric Skorokhod embedding.

**Further results.** Ten statements that the main theorems do not use are also proved:
- Lemma 4.1 in the paper's own form;
- the Markov property of the cyclic walk;
- the mean and covariance of the cyclic walk;
- the Brownian form of Claim 5.6;
- the left limits of $\pi_s$;
- five auxiliary random-walk and Brownian-motion facts.

## Errata and deviations

The formalized statements follow the paper, with three exceptions:
- **(H4).** The exponent is $41/100$ instead of $2/5$. The paper's Theorem 7.5 is taken from Zaitsev's
  multidimensional KMT theorem, which is not formalized. The induction step uses the strong
  approximation above instead, and the parts of Sections 4–8 that use (H4) are re-tuned to the new
  exponent. Theorem 1 and the bound $2/\beta$ are unchanged.
- **The index range** $n_0\ge10$ of Theorem 3.2 is stated explicitly.
- **Norms.** On $\mathbb Z^d$ and $\mathbb R^d$ the norm is the sup norm, and Euclidean balls appear
  only inside the Brownian hitting estimates.

The formalization found errors in the printed text: misprints, wrong constants, false intermediate
inclusions and missing hypotheses. None of them affects Theorem 1.
[`docs/ERRATA-AND-DEVIATIONS.md`](docs/ERRATA-AND-DEVIATIONS.md) lists each erratum, and each place
where the formalization departs from the printed text.

| Source | Errata | Deviations |
|---|---:|---:|
| Elboim–Sly | 38 | 24 |
| Komlós–Major–Tusnády | 0 | 1 |

## Verification

Two independent checks accompany the build:

- **Axiom audit.** `scripts/check_axioms.py` checks that each of the seven theorems above depends only
  on `propext`, `Classical.choice` and `Quot.sound`.
- **Comparator.** [`ElboimSlyChallenges/ElboimSly/Challenge.lean`](ElboimSlyChallenges/ElboimSly/Challenge.lean)
  restates the seven theorems from Mathlib alone, together with the 57 definitions they use, in a
  single file whose only import is Mathlib. Each definition has the text of the library's definition
  of the same name; all are in the namespace `ElboimSly.Challenge`. `Solution.lean` repeats the
  definitions and proves each theorem from the library's theorem of the same name.
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the solution proves
  exactly the challenge's statements. It compares the statements together with their whole
  dependency closure, checks the axioms, and replays the proofs in the Lean kernel and in the
  independent NanoDa kernel.

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.35.0` is
selected by `lean-toolchain`, and Mathlib is pinned at `56a0058` in `lake-manifest.json`.

```bash
lake exe cache get              # Mathlib build artifacts
lake build                      # the library and the seven theorems
lake build ElboimSlyChallenges  # the comparator challenge, its solution and the axiom audit
```

Then the checks:

```bash
lake env lean ElboimSlyChallenges/ElboimSly/AxiomsAudit.lean > axioms.log 2>&1
python3 scripts/check_axioms.py axioms.log ElboimSlyChallenges/ElboimSly/AxiomsAudit.lean
scripts/verify_comparator.sh    # needs landrun and nanoda_bin; see the script header
```

On a 16-core machine, `lake build` takes about 25 minutes after `lake exe cache get`.

## Repository layout

- `ElboimSly/Frozen/`: the seven theorems (`Theorems/`) and the definitions they use (`Defs/`), one
  declaration per file.
- `ElboimSly/Provider/`: the proofs of the seven theorems, each assembled from the results below.
- `ElboimSly/Paper/`: [ES22], by section.
  - `Roots/`: Theorem 3.2 implies the bound $2/\beta$, which implies Theorem 1.
  - `Induction/`: the induction hypothesis and Theorem 3.2.
  - `Avoid/`: Section 4.
  - `Escape/`: Section 5.
  - `Heavy/`: Section 6.
  - `Step/`: Section 7.
  - `Base/`: Section 8.
  - `Bridge/`: Wiener measure.
- `ElboimSly/Foundations/`: the inputs. These are Poisson point processes (`PPP/`), the interchange
  process (`Interchange/`), the zero-one law (`Ergodic/`), cyclic walks (`Cyclic/`), random walk
  (`SRW/`), Brownian motion (`Brownian/`), concentration (`Concentration/`) and strong approximation
  (`StrongApprox/`).
- `ElboimSlyChallenges/ElboimSly/`: the comparator challenge, its solution and the axiom audit.
- `docs/`: the errata and deviations.

## Authors, AI use and acknowledgements

The formalization is by **Scott Armstrong** and **Ahmed Bou-Rabee**. The Lean code was written by AI
agents (Claude Opus 5.5 and Claude Sonnet 5.5 in Claude Code) under their supervision:
- Claude Opus 5.5 expanded the paper into a statement-by-statement outline, drafted the statements
  and coordinated the proofs, and parallel Claude Sonnet 5.5 agents wrote most of the proofs.
- The authors approved each of the seven statements and the definitions behind them before it was
  proved, after a separate agent audit against the paper.

This is not external peer review. The Lean kernel checks every proof; see
[`formalization.yaml`](formalization.yaml) for details.

To cite this formalization, use [`CITATION.cff`](CITATION.cff). Scott Armstrong was supported by the
European Research Council (ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828.

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The paper is
not included in this repository.
