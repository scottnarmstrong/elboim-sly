# Errata and deviations

This list separates printed errors in the sources from choices made in the formalization. Elboim–Sly is cited in the numbering of arXiv:2211.17023v3 (2 February 2024). Its main result is Theorem 1; within Sections 2–9, theorems, lemmas, propositions, corollaries, definitions, claims and remarks share one counter, so Claim 5.6 is the sixth numbered item of Section 5. Equations are numbered within sections, but only the displays that the paper cites carry a number, so an unnumbered display is located by its position in a proof. The five inductive hypotheses of Section 3, printed as (1)–(5), are written (H1)–(H5); the stopping conditions of the escape algorithm in Section 5 are its conditions (1)–(7). Komlós–Major–Tusnády is cited in the numbering of Part I, Z. Wahrscheinlichkeitstheorie verw. Gebiete 32 (1975), 111–131.

An erratum is a printed statement, definition, display or proof step that is false or misprinted as written: a misprint, a wrong constant, a missing hypothesis, or an intermediate claim (an inclusion, an inequality, a bound) that fails. A deviation is a choice made in the formalization: an encoding or convention, a changed exponent, a re-routed proof, or the scope. A gap counts as an erratum when the printed argument asserts something false. It counts as a deviation (a proof supplement) when the paper omits or sketches the argument for a true step, or reaches a true conclusion from a cited result whose hypotheses are not met as stated. A grouped entry may cover several slips in one proof, and counts refer to entries. The tags in square brackets, such as [F26] or [D11], are the identifiers used in the docstrings of the Lean files; an entry without a tag has no counterpart there.

The stated theorems are Theorem 1 (`ElboimSly.root_R2`); the bound $\mathbb P(\text{the cycle of the origin is finite})\lt2/\beta$ from its proof (`ElboimSly.root_R1`); Theorem 3.2 (`ElboimSly.ind_main`); and four foundations theorems: existence and uniqueness of particle trajectories (`ElboimSly.existsUnique_trajectories`), bijectivity of $\pi_s$ (`ElboimSly.interchangePi_bijective`), and the two strong approximations used in place of Theorem 7.5 (`ElboimSly.poisson_kmt_coupling`, `ElboimSly.x1theta_coupling`). No erratum affects Theorem 1 or the bound from its proof. The formalized Theorem 3.2 differs from the printed one in the exponent of (H4) (Deviation 10), and it states the index range explicitly (Deviation 9).

| Source | Errata | Deviations |
|---|---:|---:|
| Elboim–Sly | 38 | 24 |
| Komlós–Major–Tusnády | 0 | 1 |

## Elboim–Sly

### Errata

1. **Lemma 2.2, proof, first display.** The display reads $\mathbb P(s_{10LT}\le t)\le\mathbb P(\mathrm{Poisson}(t)\ge10LT)$; $T$ is a misprint for $t$. The domination of the record times by a Poisson variable is made precise in Deviation 5. No effect on the stated theorems. [F02]

2. **Claim 2.3, proof, "By the triangle inequality, $\hat{\mathcal C}_1\subset\bigcup_{i=1}^{\lceil\beta\rceil}\mathcal A_i$".** The inclusion is false. For $s\in[i-1,i]$ and $s'\in[i,i+1]$, the triangle inequality through $\hat W(i-1)$ and $\hat W(i)$ bounds $\|\hat W(s)-\hat W(s')\|$ by three terms, each less than $L/4$ off $\mathcal A_i\cup\mathcal A_{i+1}$, so only by $3L/4$. For an integer $a$ with $L/6\le a\lt L/4$, a path with $\hat W(i-1)=0$, $\hat W(s)=-ae_1$, $\hat W(i)=ae_1$ and $\hat W(s+1)=2ae_1$, and quiet elsewhere, lies in $\hat{\mathcal C}_1$ and in no $\mathcal A_k$. Claim 2.3 holds as printed: the library proves it with windows of length 2, that is, with the events $\{\max_{u\in[0,2]}\|\hat W(i+u)-\hat W(i)\|\ge L/4\}$ (`ElboimSly.Cyclic.cyc_fast`). No effect on the stated theorems. [F01]

3. **Claim 4.3, proof, the event $\mathcal C$ and the bound on $\mathbb P(\mathcal C^c)$.** Both sums bound probabilities of the events $\{\inf_{s\gt4^{\ell-1}}\|\sigma_\ell B_\ell(s)\|\ge2L\}$ and $\{\inf_{s\gt4^{\ell-1}}\|\sigma_\ell B_\ell(s)\|\ge2\cdot4^{2\ell/5}\}$. These are the probabilities of coming close, so $\le$ is meant in both events. In the definition of $\mathcal C$ the interval $[4^{\ell-1},\le4^\ell]$ has a stray $\le$. No effect on the stated theorems. [F25]

4. **Lemma 4.1, proof, the bound $|A\cap B(W(t),r)|\le2d\cdot|\{u\in B(W(t),2r):\exists s\le t,\ W(s)=u\}|$.** The set $A$ consists of points within sup-norm distance 1 of the history, and a sup-norm unit ball contains $3^d$ lattice points. So the factor is $3^d$, not $2d$. The final bound $Cr^{5/2}$ is unaffected. No effect on the stated theorems. [F74]

5. **Section 5, the points $p_i$ (display after the definition of $B^\pm$), with Claim 5.7 and (5.5).** The points are $p_i=u+2^{j-2}(3,2,\dots,2)+i\lfloor n^{17}/3\rfloor e_2$, $i\le n^3$. In Claim 5.7, $\zeta_i$ refers to the box $u+[2^{j-1},7\cdot2^{j-3}]\times[2^{j-2},3\cdot2^{j-2}]^{d-1}$, and $p_i$ lies outside this box when $i\lfloor n^{17}/3\rfloor\gt2^{j-2}$. That happens for some $i\le n^3$ for infinitely many $n$, roughly when $2^j\lt\frac43n^{20}$. For such $i$ we have $\zeta_i=0$ and $W_i(\zeta_i^-)=p_i\notin B^-$, so the event of Claim 5.7 has probability 0. Yet the proof of Proposition 5.2 sums Lemma 5.5, which rests on Claim 5.7, over all $i\le n^3$. Correction: run the escape algorithm with $p_1,\dots,p_{I_*}$ only, where $I_*$ is the largest $i\le n^3$ with $i\lfloor n^{17}/3\rfloor\le3\cdot2^{j-4}$, so that $I_*\ge\lfloor9n^3/16\rfloor$ (`ElboimSly.Paper.escIstar`). Corollary 5.4 then holds with $I_*$ in place of $n^3$, which gives $1-e^{-c\lfloor9n^3/16\rfloor}$, and Lemma 5.3 is unaffected. Separately, in (5.5) the factor $[2^{j-2},3\cdot2^{j-2}]$ lacks the exponent $d-1$. No effect on the stated theorems. [F26]

6. **Section 5, escape algorithm, condition (6): $d(W(t),B^-)\le2^{j-3}$.** The condition concerns the walk being exposed, so $W_i(t)$ is meant (`ElboimSly.Paper.EscStopCond`). No effect on the stated theorems. [F43]

7. **Lemma 5.3, proof, second paragraph: "by conditions (2) and (3), for each $\ell\lt i$, the number of vertices visited by the walk $W_\ell$ in the block $p_\ell+[-r,r]^d$ is at most $r^2\log^Cr$ for all $r\ge\log\beta$".** Conditions (2) and (3) act only from time $\log\beta$ on. Before that time a walk $W_\ell$ may make arbitrarily many jumps, so the bound fails for some histories. Lemma 5.3 bounds a probability conditional on the histories of $W_1,\dots,W_{i-1}$ and needs the bound for all of them. Correction: use the threshold $\log^2\max(t,\log\beta)$ in condition (3) for every $t\gt0$ (`ElboimSly.Paper.EscStopCond`). The event $\mathcal D$ of the proof still excludes stopping by this condition, and no other step uses it. No effect on the stated theorems. [F64]

8. **Lemma 5.3, proof, paragraph defining $\mathcal H$ and $\mathcal I$: "We clearly have that $\mathbb P(\mathcal H)\ge c$".** $\mathbb P(\mathcal H)$ was bounded in the preceding sentence; $\mathbb P(\mathcal I)\ge c$ is meant. In $\mathcal I$ the Brownian position is read as $p_i+\sigma B_j(s)$, since $W_i'$ starts at $p_i$ and $B_j$ at $0$. The argument for $\mathbb P(\mathcal I)\ge c$ is supplied (Deviation 13). No effect on the stated theorems. [F06]

9. **Lemma 5.3, proof, paragraph defining $\mathcal H$ and $\mathcal I$: "on $\mathcal H\cap\mathcal I\cap\mathcal B$ we will not stop because of conditions (4) and (6)".** The events $\mathcal H$ and $\mathcal I$ control $W_i'$ only up to time $j4^j$. After that only $\mathcal B$ applies. At $s$ slightly above $j4^j$ it gives $\|W_i'(s)-p_i\|\ge2^{m+3}/m$ with $4^m\le s$, that is, about $8\cdot2^j/\sqrt j$. Since $N(B^-,2^{j-3})$ reaches distance $7\cdot2^{j-3}$ from $p_i$, this lower bound does not exclude condition (6) once $j\ge84$. Correction: add the event $\{\forall s\in[j4^j,4^n]:\ \|W_i'(s)-p_i\|\ge2^j\}$, whose probability is bounded by Claim 4.3 with $t=j4^j$ and $L=2^j$. The statement of Lemma 5.3 is unchanged. No effect on the stated theorems. [F37]

10. **Claim 5.6, proof, the events $\mathcal B_0$ and $\mathcal B_{2m+1}$.** Condition (2) of $\mathcal B_0$ reads "for all $s\le\zeta_1$"; $s\le\zeta_0$ is meant, since the interval $[\zeta_0,\zeta_1]$ is controlled by $\mathcal B_1$. In the paragraph on $\mathcal B_{2m+1}$, "on $\bigcup_{i\le2m}\mathcal B_i$" (twice) should read $\bigcap_{i\le2m}\mathcal B_i$. No effect on the stated theorems. [F31, F32]

11. **Claim 5.6, proof, after (5.3): "it is easy to check that on the event in (5.3) and $\bigcap_{i'\lt i}\mathcal B_i$, the walk $\tilde W$ will not intersect $(W_v(s),s\le\zeta_{i-2})$ before $0.6\cdot4^{i-m}t$".** False with the printed tube radii $2^{i-m-5}\sqrt t$ and $2^{m-i-3}\sqrt t$. Take $v=u+(2^{j-1}-1,0,2^{j-1},\dots)$, $w=u+(2^{j-1}-1,2^{j-2},2^{j-1},\dots)$ and $t=4^j$. Then the centres of the tubes of phases $m$ and $m+2$ are $2^j/24$ apart, while their radii add up to $2^j/16$. Claim 5.6 is true. The library shrinks the radii near the centre $q$ of $B^-$ by fixed factors and proves the non-intersection (`ElboimSly.Paper.es5_sep`, `ElboimSly.Paper.Escape.es5_6`). No effect on the stated theorems. [F63]

12. **Claim 5.6, proof, the sentence quoted in Erratum 11.** The intersection is printed $\bigcap_{i'\lt i}\mathcal B_i$; read $\bigcap_{i'\lt i}\mathcal B_{i'}$. No effect on the stated theorems.

13. **Lemma 6.2, proof, first display: $\mathbb P(s_{i+1}\ge s_i+4^n\mid\mathcal F_{s_i})\ge\mathbb P(\mathcal E(s_i)\mid\mathcal F_{s_i})$.** The escape event $\mathcal E(s_i)$ does not imply $s_{i+1}\ge s_i+4^n$. On $\mathcal E(s_i)$ the displacement at time $s_i+s$ is only at least $\sqrt s/n$, which is less than the side $2^m$ of $B$ for $s\lt n^24^m$. So after the spacing $n4^m$ in the definition of $s_{i+1}$, the walk may still be in $B$ and enter a new block of $\mathcal B_j$ there. Correction: space the stopping times by $n^24^m$ (`ElboimSly.Paper.heavySi`); then $\mathcal E(s_i)\subseteq\{s_{i+1}\ge s_i+4^n\}$. Lemma 6.4 and Claim 6.9 are rechecked with this spacing, and their counts change by powers of $n$. No effect on the stated theorems. [F39]

14. **Lemma 6.4, proof.** In the second paragraph, "$(s_{i'},s_{i'}+m4^n)$" and "$n^C4^n$" have $m$ and $n$ interchanged; read $(s_{i'},s_{i'}+n4^m)$ and $n^C4^m$. In the last paragraph, with $m:=\lceil\log_2r\rceil$ the box $B(x,r)$ may need $3^d$ blocks of $\mathcal B_m$, not $2^d$. If $2^m=r$, the box spans $2^{m+1}+1$ lattice points in each coordinate, and these can meet three dyadic intervals of length $2^m$. The library takes $m:=\lceil\log_2(2r+1)\rceil$, for which $2^d$ blocks suffice and $4^m\lt36r^2$ (`ElboimSly.Paper.es6_four`). Only constants change. No effect on the stated theorems. [F10, F73]

15. **Definition 6.5, condition (2): $\max_{s\le t_k'}\|W_1(s)\|\le2^{k-1}$.** The walk $W_1$ starts at $u_1\in N(B,2^{k+2})$, not at the origin, so as printed the condition fails for almost every block. All uses need the displacement $\max_{s\le t_k'}\|W_1(s)-u_1\|\le2^{k-1}$, which is what the library uses (`ElboimSly.Paper.Heavy.HeavyBlockGood`). No effect on the stated theorems. [F09]

16. **Lemma 6.6, proof, the counts.** The number of pairs of starting points and starting times is $(9\cdot2^k)^{2d}(\lfloor\beta\rfloor+1)^2$, not $2^{2dk}\beta^2$, and bounding it by $e^{Cn}$ uses $\beta\lt t_n$, which holds in the induction step. A subset of $n/20^d$ bad blocks at mutual distance at least 20 cannot be extracted greedily, since in the sup norm one chosen block excludes up to $39^d$ others. The library uses distance 17, which suffices for independence, and $n/33^d$ blocks (`ElboimSly.Paper.Heavy.es6_six`). No effect on the stated theorems. [F60]

17. **Section 6, (6.3), definition of $\tau_{\rm bad}$: $\inf\{t:|\Lambda_t|\gt n2^k\}$.** $\Lambda_t$ is a union of blocks of $2^{dk}$ vertices each, and the proof of Corollary 6.10 uses $|\Lambda_t|\le n2^{dk}$. Read $n2^{dk}$, that is, more than $n$ bad blocks (`ElboimSly.Paper.heavyTauBad`). No effect on the stated theorems. [F56]

18. **Claim 6.9, statement and proof: $\ell\le n^{\gamma+7}$.** The proof says that $T$ "is contained in at most $n^\gamma$ intervals of length $n4^k$". But $\tau'(B')=s_{n^{\gamma+3}}(B')$ allows up to $n^{\gamma+3}$ such intervals for each of the $3^d$ blocks $B'$, so about $3^dn^{\gamma+8}$ covering intervals are needed, and $3^{d+2}n^{\gamma+9}$ with the spacing of Erratum 13. The factor $(3.9/4)^k$ in the proof of Lemma 6.8 absorbs the difference (`ElboimSly.Paper.claim69`). No effect on the stated theorems. [F11]

19. **Claim 6.9, proof, and Lemma 6.8.** The proof of Claim 6.9 asserts that every $s\le t$ with $W(s)\in B'$ satisfies $\|W(s)-W(s')\|\le n^{41}$ for some $s'\in T:=[0,t-2]\cap\bigcup_i(s_i(B'),s_i(B')+n4^k)$. This fails for sub-blocks first entered during $(t-2,t]$. The library adds a tail segment ending within three time units of $t$, and the claim then requires $t\ge t_k'+3$. Lemma 6.8, stated for $t_k'\le t\lt\hat\tau$, is proved for $t\ge2t_k'+4$ (`ElboimSly.Paper.es6_eight`). For $t\lt2t_k'$ the history before $t-t_k'$ contains no full segment disjoint in time from $[t-t_k',t]$, so condition (3) of Definition 6.5 gives nothing; and the cover of Claim 6.9, applied at time about $t-t_k'$, needs $t-t_k'\ge t_k'+3$ up to rounding. The excluded times are absorbed in Corollary 6.10. No effect on the stated theorems. [F58]

20. **Corollary 6.10, statement.** False for $t\lt0.9\,t_n^{\epsilon/2}$: since $\mathcal T\subseteq[0,\infty)$, the left side is at most $t\lt(0.9+3/n)t_n^{\epsilon/2}$. The hypothesis $t\ge t_n^{\epsilon/2}$ is needed, and the only use, in the proof of Theorem 6.1, satisfies it (`ElboimSly.Paper.Heavy.es6_ten`). No effect on the stated theorems. [F59]

21. **Corollary 6.10, proof, the set $U:=\{s\in[t-t_n^{\epsilon/2},t]:W(s)\notin\Lambda_s\}$.** The bound $|U|\le\beta|\Lambda_t|$ counts time spent in discovered bad blocks; read $W(s)\in\Lambda_s$. No effect on the stated theorems. [F12]

22. **Lemma 7.1, proof, definition of $\tilde\tau_{\rm hit}(t)$.** The display uses $\|W(s)-W(s')\|$ and the range $\alpha(t)\vee s_1\le s'\lt t$. But $\tilde\tau_{\rm hit}(t)$ is meant to be the first time the concatenated walk $\tilde W$ meets the relevant history of $W_2$: read $\tilde W$ for $W$, and read the last regeneration time of $W_2$, shifted by $s_1$, for $\alpha(t)$. No effect on the stated theorems. [F67]

23. **Lemma 7.3, proof.** The event $\mathcal B_i:=\{\max_{s\le t^{1/3}}|W_i(s)-\sigma B_i(s)|\ge t^{2/15}\}$ is described as the event that the coupling was successful, and it is used as such; read $\le$. The claimed bound $\mathbb E\|X_i\|^2\le2dt^{1/3}$ is followed by a derivation that gives $6dt^{1/3}$, and the term $(n^5t^{1/3})^2$ should be $(n^3t^{1/3})^2$, the truncation level in $\mathcal A_i$. The library keeps the terms that the derivation drops and obtains $7dh$ for block length $h$ (`ElboimSly.Paper.step_second_moment`). The application of Freedman's inequality is unaffected. No effect on the stated theorems. [F13, F40]

24. **Lemma 7.3, proof, the display after "we can now use Freedman's inequality".** The sum inside the probability is printed $\sum_{i=1}^jX_j$; read $\sum_{i=1}^jX_i$. No effect on the stated theorems.

25. **Lemma 7.4, proof.** The truncated variables are defined as $X_i:=\mathbb 1_{\mathcal A_i}W(t^{2/3})$; read $W_i(t^{2/3})$, the endpoint of the $i$-th walk. The Freedman display that follows repeats the slip of Erratum 24, $\sum_{i=1}^jX_j$ for $\sum_{i=1}^jX_i$. No effect on the stated theorems.

26. **Theorem 7.5, last sentence.** "The constant $C_d$ depends on the dimension $d$" refers to the constant $c_d$ of the display. No effect on the stated theorems, since Theorem 7.5 is not used (Deviation 11). [F15]

27. **Lemma 7.6, proof.** (a) In (7.6) the inequality inside the probability is reversed; read $\max_{s\le t_n}\|W(s)-\tilde W(s)\|\ge t_n^{1/3+2\epsilon}$. (b) In (7.7), $t_n^{-2/60}$ should be $(t_n^{2/3})^{-1/16}=t_n^{-1/24}$. (c) From the application of Theorem 7.5 to the event $\mathcal C$, $j\le k$ should be $j\le\ell$. (d) In $\mathcal C$ the interval $[(j-1)t_n^{2/3},(j-1)t_n^{2/3}]$ should be $[(j-1)t_n^{2/3},jt_n^{2/3}]$. No effect on the stated theorems; the proof is re-tuned in any case (Deviations 10 and 11). [F16]

28. **Lemma 7.7, proof.** "with probability at least $1-e^{cn^3}$" should read $1-e^{-cn^3}$. No effect on the stated theorems. [F17]

29. **Lemma 7.7, proof, the sentence after the definition of $\mathcal B_1$.** $\mathcal B_1$ is defined as the event that the coupling of $W_1$ with its Brownian motion was successful, but the bound that follows is printed $\mathbb P(\mathcal B)\ge1-e^{-cn^2}$; read $\mathbb P(\mathcal B_1)$. No effect on the stated theorems.

30. **Lemma 7.8, proof, the display $\mathbb P(\zeta_i'\ge\zeta_i+4^n\mid\mathcal F^+_{\zeta_i})\ge1/2$ before (7.9).** By definition $\zeta_i'\le t_n'\lt4^n$, so the event is empty. Read $\{\zeta_i'\ge(\zeta_i+4^n)\wedge t_n'\}=\{\zeta_i'=t_n'\}$. A success then ends the procedure, at most one of the first $n^3-1$ trials succeeds, and (7.9) holds with $\mathrm{Bin}(n^3-1,1/2)$ (`ElboimSly.Paper.Step.step78_excursion`, `ElboimSly.Paper.Step.step78_few_excursions`). No effect on the stated theorems. [F50]

31. **Section 8, (8.3), and the proof of Lemma 8.1.** (8.3) couples $W$ with $B$. But the walk with rate 1 per edge has coordinate variance $2t$, and (H4) is stated with $\sigma B$, where $\sigma=\sqrt2$ in the base case. Read $\max_{t\le t_n}\|W(t)-\sqrt2B(t)\|\le n^{10}$. The proof of Lemma 8.1 must then use $\sqrt2B$ in $\mathcal A_2$, in the bound $|B(\lfloor t\rfloor)-u|\le2n^{10}$ and in $T'$. Accordingly the rescaling is $B^*(u)=(2\beta^{2\delta})^{-1/2}B(2\beta^{2\delta}u)$ with lag $\beta^\delta/2$, instead of $(2\beta^\delta)^{-1}B(4\beta^{2\delta}u)$ with lag $\beta^\delta/4$ (`ElboimSly.StrongApprox.sa_base_coupling`, `ElboimSly.Paper.es8_lemma_8_1`). No effect on the stated theorems. [F18, F41]

32. **Lemma 8.1, proof, (8.4).** The number of lattice points within distance $2n^{10}$ of a point is $(4n^{10}+1)^d$, not $(4n^{10})^d$. No effect on the stated theorems. [F47]

33. **Lemma 8.2, proof, misprints.** The time window in the bound on the number of contact intervals and in the event $\mathcal D$ is $[0,2t_n']$, not $[0,2t_n]$. The stopping times are printed "Let $\zeta_i=0$ and $\zeta_i:=\inf\{t\ge\zeta_i+3.89,\ d(X(t),V)\le1.9^{n+1}\}$"; read $\zeta_0:=0$ and $\zeta_i:=\inf\{t\ge\zeta_{i-1}+3.89^n:\ d(X(t),V)\le1.9^{n+1}\}$. The set bounded by $J\cdot3.89^n$ is $\mathfrak P^*(v)$, not $\mathcal B^*(v)$. No effect on the stated theorems. [F19, F34]

34. **Lemma 8.2, proof, final union bound.** The display $\mathbb P(|\mathfrak P_n(0,u,0,q)|\ge3.9^n)\le\mathbb P(\mathcal A)+\sum_{\|v\|\le4^n}\mathbb P(|\mathfrak P^*(v)|\ge3.9^n)$ is false as written. The left side must be restricted to $\Omega$: for $u=0$ and $q=0$ the two walks coincide and $|\mathfrak P_n|=t_n'\ge3.9^n$ for large $n$. Also $\mathbb P(\mathcal A)$ should be $\mathbb P(\mathcal A^c)$, and the sum must exclude $v=0$, whose term equals 1 (`ElboimSly.Paper.es8_lemma82`). No effect on the stated theorems. [F33, F45]

35. **Lemma 9.1.** The hypothesis "$|v-u|\gt r$" should read $|x-y|\gt r$. No effect on the stated theorems. [F20]

36. **Lemma 9.2, proof, display.** The first equality applies Lemma 9.1 to $\{z:\|z\|\le r\}$. But $\|\cdot\|$ is the sup norm, while the hitting probability $(r/|x-y|)^{d-2}$ of Lemma 9.1 is for Euclidean balls, so for sup-norm balls the equality becomes an inequality with a constant depending on $d$. The left side omits the starting point $y$. The first inequality ("expectation being maximized at $y=0$") needs an argument, such as Anderson's inequality. Lemma 9.2 itself holds; the library proves it directly by time discretization, without Lemma 9.1 or the radial integral (`ElboimSly.Brownian.far_hit_le`). No effect on the stated theorems. [F20, F29]

37. **Lemma 9.3.** False for small $r$. If the motion starts in $D$ then $N\ge1$, while $xr^2\lt1$ for $r\lt x^{-1/2}$, so $\mathbb P(N\gt xr^2)=1\gt2e^{-cx}$ for large $x$. The hypothesis $r\ge1$ is needed, and it covers the use in the proof of Lemma 8.1, where $r\ge\beta^\delta$ (`ElboimSly.Brownian.occupation_le`). No effect on the stated theorems. [F27]

38. **Claim 9.4, proof.** Several steps fail as printed:
    - The repeated-trials argument gives (9.1) only with $\exp(-ct^{\zeta^2/2})$ on the right, not $\exp(-Ct^\zeta)$, since about $r^\zeta=t^{\zeta^2/2}$ returns are needed.
    - (9.2) is false: an oscillation of size $r^{1/20}=t^{\zeta/40}$ within unit time has probability of order $\exp(-t^{\zeta/20}/2)$, which is much larger than $\exp(-ct^\zeta)$.
    - In the next display $r^{2+3\zeta}(2r^{1/20})^5=32r^{2.25+3\zeta}$, which exceeds $r^{2.1}$; and the radii $r^{1/20}$ (in the definition of heavy) and $r^\zeta$ (in the display) are mixed.
    - (9.3) requires $Cr^{2.1}r^{-5(1-\zeta)}\le r^{-2.8}$, that is, $\zeta\lt1/50$.
    - $W(s_j)$ is written for $B(s_j)$.
    - The last step requires $\zeta\le\sqrt{0.1}$.

    The library proves Claim 9.4 for $0\lt\zeta\le1/100$ with $c=\zeta^2/4$, replacing $\tau_{\rm hea}$ by good events measurable at the times $s_j$ (`ElboimSly.Brownian.selfIntersection`). This covers the only use, $\zeta=\delta/2$ in the proof of Lemma 8.1. Whether the claim holds for every $\zeta\gt0$ was not examined. No effect on the stated theorems. [F28]

### Deviations

1. **Scope.** The library formalizes Theorem 1 (`ElboimSly.root_R2`), and, as a separate theorem, the bound $\mathbb P(\text{the cycle of the origin is finite})\lt2/\beta$ for $\beta\ge\beta_0$ from its proof (`ElboimSly.root_R1`). It also formalizes Theorem 3.2 (`ElboimSly.ind_main`), with every result of Sections 2–9 that these depend on. No cited result is assumed. Freedman's inequality, the zero-one law, Brownian motion and its estimates, the random-walk estimates and the strong approximations are all proved from Mathlib, and Theorem 7.5 is replaced (Deviation 11). The introduction (Tóth's conjecture, previous work, open problems) is not formalized. Intermediate statements are formalized in the form their uses need; the changes are listed in the errata and below. [D1, D2, D15]

2. **Sections 1 and 2, the interchange permutation on $\mathbb Z^d$.** The paper does not construct $\pi_\beta$ on the infinite lattice.
    - The clocks are a Poisson point process $N$ on $S_\beta=E\times\mathbb R/\beta\mathbb Z$ with intensity counting measure $\otimes$ Lebesgue measure. It is characterized by Poisson counts and by independence over disjoint sets (`ElboimSly.IsPoissonPointProcess`, `ElboimSly.ringIntensity`). Rings repeat with period $\beta$, which is the cyclic structure of Section 2.
    - A configuration is good if every edge rings finitely often, no two rings coincide, and no vertex starts or ends ring paths of unbounded length inside a time window of length $\beta/2$ (`ElboimSly.Good`). The process is almost surely good (`ElboimSly.Interchange.ae_good`).
    - On good configurations each particle has a unique trajectory (`ElboimSly.existsUnique_trajectories`). $\pi_s$ maps a vertex to the position at time $s$ of the particle that starts there (`ElboimSly.interchangePi`), and it is a bijection (`ElboimSly.interchangePi_bijective`).
    - "Infinite cycle" means $\exists x\ \forall k\ge1:\ \pi_\beta^k(x)\neq x$ (`ElboimSly.infEvent`), and the cycle of the origin is finite when $\pi_\beta^k(0)=0$ for some $k\ge1$ (`ElboimSly.finZeroEvent`).
    - R1 and R2 are stated for every Poisson point process of this intensity on every probability space, and $\beta\gt0$ is the instance `[Fact (0 < β)]`.

    No effect on the stated theorems. [F04, D3, D4, D16, D19]

3. **Proof of Theorem 1, "the zero-one law".** The paper concludes from $\mathbb P(\tau_{\rm reg}\lt\infty)\lt2/\beta$ by a zero-one law that it does not state. The library proves the following: every translation-invariant measurable set of ring configurations has probability 0 or 1 under the Poisson point process (`ElboimSly.ringLaw_eq_zero_or_one`, `ElboimSly.prob_mem_eq_zero_or_one`); $\pi_\beta$ is covariant under lattice translations; and the set of configurations with an infinite cycle is measurable and translation invariant (`ElboimSly.Roots.root_R2_of_R1`). The bound $\sum_{i\ge1}(i\beta)^{-d/2+0.1}\lt2/\beta$ is used as printed (`ElboimSly.Roots.root_R1_of_indMain`). No effect on the stated theorems. [F04]

4. **Norms and readings: Section 2 ("$\|\cdot\|$ will be the $L^\infty$ norm"), (2.4), (H4), (8.3) and (H5).**
    - The sup norm is used throughout. This includes (H4) and (8.3), where the coupling error is printed with $|\cdot|$ while Lemma 7.6 and the uses have $\|\cdot\|$, and the set $\mathfrak P^*(v)$ in the proof of Lemma 8.2. The two norms differ by a factor of at most $\sqrt d$. Euclidean norms occur only inside Brownian hitting estimates, with explicit conversion constants.
    - In (2.4), where $s$ may be negative, $W(s):=W(0)$ for $s\lt0$ (`ElboimSly.cycTfast`).
    - In (H5) the start times are $q_i\in[0,\beta]$, and "$W_i$ closes" means $W_i(s)=W_i(0)$ for some $s\in\beta\mathbb Z\cap(0,t_n']$. For a set of times $|\cdot|$ is Lebesgue measure, and for a set of vertices it is cardinality (`ElboimSly.IndH5`).

    No effect on the stated theorems. [D5, F22, F36, F44]

5. **Section 2, the cyclic, driven and regenerated walks.**
    - The equality in law of the walk driven by a simple random walk and the cyclic walk ("It is clear that the walk $W$ defined in the above way has the same law ...") is proved (`ElboimSly.Cyclic.cyc_driven_law`).
    - So is an exploration theorem for several walks in one environment, by which the unexplored part of the environment at a stopping time is a fresh Poisson process. It underlies each "we can couple" in Sections 4–8; for Lemma 2.1 and the regenerated walk see `ElboimSly.Cyclic.cyc_hit_couple_regen`.
    - Sections 4 and 5 are written with the filtration of explored rings rather than the driving $\sigma$-algebra $\sigma(X(s):s\le t)$, because Section 5 runs several walks in one environment. The laws coincide.
    - The regenerated walk is built from i.i.d. copies of the environment: the restrictions to $\{k\}\times S_\beta$ of a Poisson point process on $\mathbb N\times S_\beta$ (`ElboimSly.regenWalk`, `ElboimSly.copyEnv`).
    - In the proof of Lemma 2.2, "each new step further along in direction $e_1$ corresponds to a new Poisson clock ring" is made precise: a new record in a direction is a jump of the driving walk in that direction. The lemma holds with $C=1$ (`ElboimSly.Cyclic.cyc_far`).

    No effect on the stated theorems. [F05, F02]

6. **"Standard" random-walk estimates: proof of Claim 2.3, Section 8, proofs of Claim 5.6 and Lemma 8.2.** Facts about the continuous-time simple random walk that the paper calls standard are proved with explicit constants:
    - (H2) in the base case, through the bound $\mathbb P(X(t)=u)\le t^{-d/2}$ for $t\ge1$ (`ElboimSly.SRW.IsSRW.prob_eq_le_H2`); (8.1); and the case $t\le\beta$ of Claim 2.3.
    - The confined point-to-point lower bounds behind the events $\mathcal B_0$ and $\mathcal B_{2m+1}$ in the proof of Claim 5.6, uniform in the starting point and the remaining time (`ElboimSly.SRW.box`).
    - In the proof of Lemma 8.2, the description of the two walks within one period ("Recall that $Y_v$ are simple random walks in this time scale", `ElboimSly.Paper.one_lap_a`).
    - Also in Lemma 8.2, the transience step ("in each unit interval of time there is a positive probability ..."): a fixed escape scenario has conditional probability at least $c_1$ at each contact (`ElboimSly.Paper.prob_kap_le`).

    No effect on the stated theorems. [F21]

7. **Section 9 and the Brownian estimates.** Mathlib provides neither Brownian motion in $\mathbb R^d$ nor the strong Markov property. The library constructs Brownian motion by the Lévy–Ciesielski series (`ElboimSly.Brownian.isStandardBrownianMotion_levyCiesielski`). It proves the estimates of Section 9 by time discretization, without optional stopping or the harmonic function $|x|^{2-d}$:
    - Lemma 9.1, as an upper bound for sup-norm cubes with a Euclidean corollary (`ElboimSly.Brownian.hit_ball_unit`);
    - Lemma 9.2, in the sup norm for all $r,s,\sigma\gt0$ (`ElboimSly.Brownian.far_hit_le`);
    - Lemma 9.3, for $r\ge1$, with the repeated trials made explicit by integer-valued stopping times (`ElboimSly.Brownian.occupation_le`);
    - Claim 9.4, for $\zeta\le1/100$ (`ElboimSly.Brownian.selfIntersection`).

    See Errata 35–38. The Brownian facts used in Sections 4, 5, 7 and 8 are stated for $\sigma B$, uniformly in the parameters that the couplings vary; for instance, the separation set $T^*$ of Lemma 8.1 involves $\sqrt2$ times a standard Brownian motion. No effect on the stated theorems. [F20, F27, F28, F29]

8. **Section 3, the inductive hypotheses.** The hypotheses at level $n$ form one proposition $H(\beta,n,t_0)$ (`ElboimSly.IndHyp`). It consists of (H1)–(H4) for the regenerated walk built from the copies of a Poisson point process on $\mathbb N\times S_\beta$, and (H5) for two cyclic walks in a single environment, each required on every probability space carrying such a process. In (H4), "There is a coupling of $W$ and a Brownian motion $B$" is encoded as a joint law: a probability measure on the product of the path space of $W|_{[0,t_n]}$ and $C([0,\infty),\mathbb R^d)$. Its first marginal is the law of $W|_{[0,t_n]}$, its second marginal is Wiener measure, and it satisfies $\mathbb P(\sup_{t\le t_n}\|W(t)-\sigma B(t)\|\ge t_n^{\theta_H})\le p_n$ (`ElboimSly.AdmitsBMCoupling`, `ElboimSly.IsWienerMeasure`, `ElboimSly.IndH4`). The bound $p_n$ is `ElboimSly.indFailBound`, and the relaxed-path property is `ElboimSly.IsRelaxedPath`. No effect on Theorem 1 or R1. [D17, D21]

9. **Theorem 3.2 and the opening of Section 4, the index range of the induction.** (H1) requires $0.9+1/n\le1$, which is impossible for $n\le9$. Theorem 3.2 does not record $n_0\ge10$, and `ElboimSly.ind_main` states it. The induction step assumes the hypothesis "for all $n'\lt n$", which can only mean $n_0\le n'\lt n$. The library proves the step uniformly in a base level $n_1\ge8d$, with $\beta$ large depending on $n_1$, so that every use of the hypothesis lands at a level $\ge n_1$ (`ElboimSly.Paper.Induction.ind_step_of`). The low-level uses are checked:
    - Claim 4.2 is used for $L\ge4^{n_0+1}$; its proof sums from $\ell_0=\lfloor\log_4L\rfloor$ and uses (H3) from level $\ell_0-1$ on (`ElboimSly.Paper.es4_claim2`).
    - Claim 4.3 is used for $t\ge4^{n_0+1}$ (`ElboimSly.Paper.es4_claim3`).
    - The proof of Claim 5.6 uses (H1) at time about $\sqrt\beta$, which needs $\sqrt\beta\ge2\cdot4^{n_0+1}$.
    - The base case uses $n_0\ge20$, so that $0.9+1/n\le0.95$.

    No effect on Theorem 1 or R1. [F03]

10. **(H4), the exponent of the coupling error.** (H4) is formalized with error $t_n^{\theta_H}$, $\theta_H=41/100$, instead of $t_n^{2/5}$ (`ElboimSly.indThetaH`, `ElboimSly.IndH4`). This changes Theorem 3.2 as printed. It does not change Theorem 1 or R1, which use only (H2). With the exponent $2/5$, the induction step in Lemma 7.6 needs a multidimensional KMT-type theorem such as Theorem 7.5. With an exponent in the window $(2+2\epsilon)/5\lt\theta_H\lt17/40$, a coupling with error of order $\ell^{1/4}$ up to logarithms suffices (Deviation 11). The change forces the following re-tunings:
    - Claim 4.3 holds for $t^{\theta_H}\le L\le t^{1/2}$, with errors $4^{\theta_H\ell}$; its geometric series needs only $\theta_H\lt1/2$ (`ElboimSly.Paper.es4_claim3`). Lemma 4.1 applies it with $L=t^{\theta_H}=\beta^{3\delta\theta_H}\ge\beta^\delta$, and the exponent becomes $c=\delta/30$ (`ElboimSly.Paper.es4_1`). This also repairs the printed application with $t=\beta^{3\delta}$ and $L=\beta^\delta\lt t^{2/5}$, which lies outside the stated range of Claim 4.3.
    - Lemma 5.3 needs $(j4^j)^{\theta_H}\lt n^{17}/30$, which holds for $n\ge37201$; this is where $\theta_H\lt17/40$ is used. Claims 5.6 and 5.7 need $T^{\theta_H}\le\rho_i/240$ for windows $T\le500\rho_i^2$, true for large $\beta$, and $2^{0.82j}\lt2^{j-6}$, true for $j\ge34$.
    - Lemmas 7.3 and 7.4 use the coupling radius $h^{\theta_H}$ at block length $h$.
    - Lemma 7.6 uses $\ell=\lceil t_n^{0.395}\rceil$ blocks of length $T=t_n/\ell\approx t_n^{0.605}$, instead of $t_n^{1/3}$ blocks of length $t_n^{2/3}$. When $T\le3^{-16}\beta$, the printed estimate of $\sigma$ through $\sigma'=\sigma(T)$ fails at these parameters, since $0.605(1/2-\theta_H)\lt1/16$; $\sigma$ is then computed directly from the simple random walk.
    - Lemma 7.7 uses a second walk of length $t^{2\theta_H}$ instead of $t^{4/5}$, and a ball of radius $n^2t^{\theta_H}$. With length $t^{4/5}$ the argument needs $\theta_H\lt2/5+1/(75d)$.
    - Lemma 7.8 needs $4^{\theta_H}\lt1.9$ in two places.
    - In Section 8, deducing (H4) from (8.3) needs $n\ge77$ (Deviation 24).

    No effect on Theorem 1 or R1. [D11, F24]

11. **Theorem 7.5 and Lemma 7.6, the coupling with Brownian motion in the induction step.** Theorem 7.5, quoted as a special case of Zaitsev's Theorem 1.3, is not used. As printed it follows from Zaitsev's theorem only for $\ell\ge\ell_0(d)$. It produces Gaussian partial sums at integer times rather than a Brownian motion, so Brownian bridges are needed in between. It also rests on a class membership for bounded laws that Zaitsev states as an example and cites from his 1986 paper.

    The proof of Lemma 7.6 uses X1θ instead (`ElboimSly.x1theta_coupling`). Take i.i.d. vectors $X_i$ with $\|X_i\|\le M\le(\log\ell)^3$, a law invariant under coordinate sign changes, and unit coordinate variances. Then for $\ell\ge\ell_0(d)$ there is a coupling with i.i.d. standard Gaussian vectors $G_i$ such that $\max_{j\le\ell}\|\sum_{i\le j}(X_i-G_i)\|\ge\ell^{1/4}(\log\ell)^{12}$ has probability at most $\exp(-(\log\ell)^3)$. It is proved by a Skorokhod embedding of the whole walk, coordinatewise given the moduli. Its rate $\ell^{1/4}$ forces the exponent change of Deviation 10.

    The proof also fixes what the paper leaves implicit: integer parts ($\ell=\lceil t_n^{0.395}\rceil$, $T=t_n/\ell$), and a single probability space carrying the natural coupling, the block variables and the Brownian motion (`ElboimSly.StrongApprox.sa_lemma76`, `ElboimSly.Paper.Step.step_lemma76_of_cor72_sigma`). No effect on Theorem 1 or R1. [D2a, D13, F15]

12. **Section 8, (8.3), the coupling at the base.** (8.3) is obtained "by KMT embedding from Theorem 7.5". But Theorem 7.5 assumes bounded increments with identity covariance, while the unit-time increments of the simple random walk are unbounded with covariance $2I$; after truncation and normalization it would give $1-e^{-cn^4}$. The library derives (8.3), with $\sqrt2B$ (Erratum 31) and the sup norm, from A1 (`ElboimSly.poisson_kmt_coupling`). A1 is a one-dimensional KMT coupling for centred Poisson increments with an exponential tail, and it is applied to the $2d$ counting processes of the jumps in each direction. The failure probability is $e^{-n^4}$ for $n\ge n_1(d)$ (`ElboimSly.StrongApprox.sa_base_coupling`, `ElboimSly.Paper.admitsBMCoupling_of_srw_law`). The proof of A1 is described under Komlós–Major–Tusnády below. No effect on the stated theorems. [D10, D12, F18, F23]

13. **Section 5, the escape stopping time, Lemma 5.3 and Proposition 5.2.**
    - The definition of $\tau_{\rm esc}$ involves conditional probabilities at uncountably many times. Only the countably many first entrance times into blocks of $\mathcal B_j$ matter, and at each of them the conditional probability is a fixed version, so $\tau_{\rm esc}$ is well defined (`ElboimSly.Paper.escTauEsc`).
    - In the proof of Lemma 5.3, $\mathbb P(\mathcal I)\ge c$ is not clear without an argument: a union bound over the points $p_\ell$ is inconclusive for $d=5$. The library first carries the motion away from the line of the points, then uses the transience of the $(d-1)$-dimensional projection orthogonal to $e_2$ (`ElboimSly.Brownian.es53_main`).
    - The inclusion $\mathcal K(\beta')\cap\{W(t')=p_i\}\cap\mathcal A_i(\beta')\subseteq\mathcal E(\xi_B)$ in the proof of Proposition 5.2 is proved, for $n\ge2000$ (`ElboimSly.Paper.Escape.es5_inclusion`).

    No effect on the stated theorems. [F05, F30, F38]

14. **Lemma 5.5 and Claims 5.6–5.7, conditioning on the explored walks.** The paper flags "a subtle point" in the proof of Lemma 5.5 and justifies the coupling informally. The library makes it rigorous with an explicit exploration plan for the walks involved, the Markov property at stopping times, and a coupling of the continuation in a resampled environment with the true one. The two agree until the continuation reads an explored ring where they differ (`ElboimSly.Paper.es5_plan_coupling`). Three further supplements are needed:
    - Claim 5.6 gains the conditions $W_v(s)\neq v$ for $s\in[\beta,t]$ and $W_v(s)\neq w$ for $s\in[0,t-\beta]$. The proof of Lemma 5.5 uses them ("$W_v$ does not return to $v$ at a cyclic time ..."), but Claim 5.6 does not state them. They hold on the paper's events once the walk on $[0,\zeta_0]$ is localized near $v$, which is added to $\mathcal B_0$ (`ElboimSly.Paper.Escape.es5_6`).
    - The proof of Claim 5.7 drops $\mathcal F_{\xi_B}$ from the conditioning without comment. The library proves Claim 5.7 conditionally on $\mathcal F_{\xi_B}\vee\mathcal G(\beta')$.
    - The omitted details of (5.4) are supplied. The coupling holds with probability at least $1-C(\log\beta)^{-1/30}$ rather than $1-\beta^{-c}$, which suffices.

    No effect on the stated theorems. [F07, F08, F65, F66]

15. **Section 6, counting jumps instead of visited vertices.** The proof of Lemma 6.4 bounds the number of vertices visited in a time window by means of $\tau_{\rm fast}$. This is correct: before $\tau_{\rm fast}$ a unit time window visits at most $(2n^3)^d$ vertices. The library counts jumps instead, with a stopping time $\tau_{\rm jump}\le\tau_{\rm fast}$ at which some unit window contains $n^3$ jumps (`ElboimSly.Paper.pathTjump`), and adds it to $\hat\tau$. Since $\mathbb P(\tau_{\rm jump}\le t_n)\le e^{-cn^3}$ this costs nothing, and it gives a smaller polynomial in Lemma 6.4. The pathwise results of Section 6 are stated under the weaker hypothesis $t\lt\check\tau$, which the application between regenerations in the proof of Theorem 6.1 needs (`ElboimSly.Paper.heavyTauCheck`). Two readings are fixed: the stopping times $s_i$ minimize over $x\ge s_{i-1}+n^24^m$ (the infimum is attained either way), and (6.4) is proved for the non-strict event $\{\tau_{\rm bad}\le t_n\wedge\tau_{\rm reg}\}$. No effect on the stated theorems. [F53, D6]

16. **Definition 6.5 and the proof of Lemma 6.6, the walk length $t_k'$ and condition (2).** Definition 6.5 sets $t_k':=4^k/k^4$, which is the (H5) length at level $k$ only for $t_0=1\notin(1,4]$. The library uses $t_k'=t_k/k^4$, the (H5) length at level $k$ for the current $t_0$ (`ElboimSly.Paper.heavyTkPrime`), and writes condition (3) as $\lt3.9^k$, the complement of the event in (H5). In the proof of Lemma 6.6, the failure probability of condition (2) does not follow "directly" from the induction hypothesis. (H3) at level $k'$ bounds the displacement only by $k'^2\sqrt{t_k'}=(k'/k)^2\sqrt{t_0}\,2^k$, which exceeds $2^{k-1}$. The library uses (H4) at level $k'$ and a Gaussian tail, which adds $4de^{-k^4/3200}$ to the bound (`ElboimSly.Paper.Heavy.es6_six`). No effect on the stated theorems. [F54, F55]

17. **Section 6, further supplements.**
    - The definition of blocks "bad by time $t$" (before (6.3)) uses walks started in $N(B,2^k)$, whereas Claim 6.9 and the proof of Lemma 6.8 apply conditions (2)–(3) to segments started in $N(B,2^{k+1})$. The library uses $N(B,2^{k+2})$, as in Definition 6.5, and also counts segments that are only partly exposed by time $t$ (`ElboimSly.Paper.BadByTime`).
    - In the proof of Lemma 6.2, the trial at $s_0$ is not covered by $\tau_{\rm esc}$ when $s_0=0$, since $\tau_{\rm esc}$ considers only positive entrance times. The library uses the trials at $s_1,s_2,\dots$, which changes nothing.
    - In the proof of Lemma 6.8, the assumption "for simplicity" that $t-t_k'$ is a cyclic integer is removed by rounding down, at a cost of one time unit in each estimate (`ElboimSly.Paper.heavyU1`).

    No effect on the stated theorems. [F57, F61, F62]

18. **Lemma 6.12, the number of regenerations.** The proof refers to "the same arguments as in the proof of Theorem 1" for a geometric domination. That proof bounds $\mathbb P(\tau_{\rm reg}\lt\infty)$ by (H2) at all times, which is not available inside the induction step. The library bounds $\mathbb P(\tau_{\rm reg}\le4^n)$ instead, which needs (H2) only up to time $4^n$. It counts the pieces longer than a fixed length directly, without the decomposition into windows $[(i-1)4^n,i4^n]$ (`ElboimSly.Paper.Heavy.es6_twelve_of_tauhat`). No effect on the stated theorems. [F52]

19. **Corollary 7.2, "follows immediately by induction".** Induction on Lemma 7.1 gives the failure probability $(\ell-1)e^{-cn^3}$, not $e^{-cn^3}$ for every $\ell$. This is the printed form with $c/2$ whenever $\ell\le t_n$, which covers every use: $\ell\le2t_n^{0.395}$ in Lemma 7.6 and $\ell\le2t^{1/3}$ in Lemmas 7.3 and 7.4 (`ElboimSly.Paper.Step.stepCor72_of_lem71`). No effect on the stated theorems. [F68]

20. **Lemmas 7.3 and 7.4, Freedman's inequality and omitted details.** The paper applies Theorem 18 of Chung–Lu (Internet Math. 3 (2006)), a bound for the terminal value of a martingale, to the maximum over $j\le k$ of the partial sums. The library proves Freedman's inequality in maximal form with predictable variance bounds, together with its corollary for independent bounded summands (`ElboimSly.concFreedman_max_abs_ge`, `ElboimSly.concFreedman_indep`). The details of Lemma 7.4 that the paper omits are supplied (`ElboimSly.Paper.Step.step_lemma74_of_cor72`). No effect on the stated theorems. [F14, F51]

21. **Lemma 7.7, proof, the event $\mathcal B_1$.** The event "that the coupling of $W_1$ with its Brownian motion $B$ was successful" refers to a coupling at the length of $W_1$, up to $t_n$, which lies beyond what the induction hypothesis covers. The coupling used is that of Lemma 7.6 at the current level $n$ (`ElboimSly.Paper.Step.step_lemma77_of_cor72_bm`). No effect on the stated theorems. [F69]

22. **Lemma 7.8, proof, the definitions.** The definitions are adjusted as follows; none of the changes affects the event estimated (`ElboimSly.Paper.Step.step78_assemble`).
    - The far threshold in $\zeta_i$ and in (7.11) is $1.9^k/2$ instead of $1.9^k$. The cover of Claim 6.9 has radius $n^{41}$, so proximity $1.9^k$ to $V$ gives only proximity $1.9^k+n^{41}$ to the covering segments, whereas condition (3) of Definition 6.5 controls proximity $1.9^k$.
    - The closing time $\tau^{(2)}_{\rm reg}$ is added to $\zeta_i'$, so that the walk coupled with $W_2$ after $\zeta_i$ has not closed. This matters when $\zeta_i=0$.
    - $\zeta_i$ and $J$ stop at $t_n'$. The paper also stops at $\tau_{\rm merge}\wedge\tau^{(2)}_{\rm reg}$, which exceeds $t_n'$ on $\Omega$.
    - The set $\Lambda_t'$ of bad blocks discovered by both walks is made explicit. The blocks and integer cyclic times of $W_2$ are taken in its own frame, cross violations between the two walks are included, starting points range over $N(B,2^{k+2})$, and the threshold is $2n$ blocks.

    No effect on the stated theorems. [F70, F71, F72]

23. **Lemma 8.2 and the sentence before it, time reversal and the number of contacts.** The paper reduces to $q_2\le\beta/2$ "by reversibility in time". Reversal turns the walks into backward walks started from random points, so the union bound over starting points does not apply directly. The library avoids the reduction. With $q\equiv q_2-q_1$ in $[0,\beta)$, the cases $q\le t_n'$ and $t_n'\lt q\lt\beta-t_n'$ are the paper's, and the case $q\ge\beta-t_n'$ is handled by exchanging the roles of the two walks (`ElboimSly.Paper.es8_lemma82`). The proof allows fewer than $n^4$ contact intervals and couples with precision $n^{10}$. These tolerances are valid, but with the transience constant obtained they would require $n\gtrsim e^{7.8\cdot10^5}$. The library allows up to about $1.9^n/(4n^5)$ contact intervals with precision $1.9^n/2$, which suffices (`ElboimSly.Paper.es8_decoupling`, `ElboimSly.Paper.es8_pair`). No effect on the stated theorems. [F46, F49]

24. **Section 8, explicit thresholds and the union bound in Lemma 8.1.** Several steps of Section 8 hold only for large $n$; the formalization makes the thresholds explicit and folds them into $n_0$:
    - $n^4\cdot3.89^n\le3.9^n$ in the proof of Lemma 8.2 holds for $n\ge14980$ and fails at $n=14979$ (`ElboimSly.Paper.es8_threshold`).
    - $\mathbb P(\mathcal C)\ge1-e^{-n^4}$ needs $(1.9^2/3.6)^n\ge64n^4$, about $n\ge1.5\cdot10^4$ for $d=5$.
    - Deducing (H4) from (8.3) needs $n^{10}\le t_n^{41/100}$, that is, $n\ge77$ ($n\ge79$ with the exponent $2/5$).
    - (H1) at the base needs $0.9+1/n\le0.95$, that is, $n\ge20$.

    With the contact count of Deviation 23, $n_0(5)\approx1.2\cdot10^6$. In the proof of Lemma 8.1, the union bound in $\mathcal A_2$ is taken over integer radii rather than over all real $r\ge\beta^\delta$. No effect on the stated theorems. [F19, F35, F42, F48]

## Komlós–Major–Tusnády

### Errata

None recorded.

### Deviations

1. **Theorem 1, the case of centred Poisson increments, and its proof.** The library proves a special case of Theorem 1, called A1 (`ElboimSly.poisson_kmt_coupling`). For i.i.d. Poisson(1) variables $\xi_i$ there is a coupling with i.i.d. standard normal $\eta_i$ such that $\mathbb P(\max_{j\le N}|\sum_{i\le j}(\xi_i-1-\eta_i)|\ge C\log N+x)\le Ke^{-\lambda x}$ for all $N$ and all $x\ge0$. The law of $\xi_1-1$ satisfies the hypotheses of Theorem 1 (mean 0, variance 1, a finite moment generating function near 0, lattice values), so A1 is a special case. The proof does not follow KMT's. KMT's Lemma 1 rests on large-deviation theorems with Cramér series that are quoted without proof, and the error analysis truncates at a level depending on $x$. The library uses the dyadic scheme of Sections 2–3 with three simplifications that are available for Poisson increments:
    - Given a total count $m$, the split is exactly $\mathrm{Bin}(m,\frac12)$. So the only quantile estimate needed is a Tusnády-type bound for $\mathrm{Bin}(m,\frac12)$ against $\mathcal N(m/2,m/4)$, uniform in $m$ and in the quantile. It is proved from the ratio of consecutive binomial coefficients and the Robbins–Stirling bounds (`ElboimSly.StrongApprox.tusnady`).
    - The root count is drawn independently at double depth, which removes the second quantile lemma.
    - The mismatch between the Poisson and Gaussian scales at a node is controlled through $\sqrt m-\sqrt r$, whose increments along root-to-leaf paths are uniformly sub-Gaussian, so no truncation is needed.

    This is a route choice; the statement is the special case. [D10, D12]

## Other sources

Zaitsev, *Multidimensional version of the results of Komlós, Major and Tusnády for vectors with finite exponential moments* (ESAIM: P&S 2 (1998)), is the source of Theorem 7.5 of Elboim–Sly. It is not formalized and not used (Elboim–Sly, Deviation 11), and no errata were recorded. Theorem 18 of Chung–Lu, *Concentration inequalities and martingale inequalities: a survey* (Internet Math. 3 (2006)), which Elboim–Sly cite for Freedman's inequality, was not consulted. The library proves the maximal form it needs (Elboim–Sly, Deviation 20). Lawler–Limic, *Random Walk: A Modern Introduction* (2010), Chapter 7, was consulted for the dyadic coupling scheme. Its strong approximation theorems give polynomial tails at a single threshold and are not used. The Brownian-motion and random-walk facts that Elboim–Sly cite as standard are proved from Mathlib (Elboim–Sly, Deviations 6 and 7); no textbook statement is assumed.
