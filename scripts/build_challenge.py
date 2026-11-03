#!/usr/bin/env python3
"""Generate the comparator challenge from the frozen files.

Usage, from the repository root: python3 -I scripts/build_challenge.py

For every file under ElboimSly/Frozen/ this writes a mirror under
ElboimSlyChallenges/ElboimSly/ (Defs/ and Theorems/) with the same text and the same Mathlib imports,
so that every definition elaborates exactly as in the library (a single file importing the union of
the imports can resolve instances along different paths, which comparator rightly rejects). In the
mirrors, imports of frozen files point to their mirrors, imports of the library's proofs are
dropped, and each theorem's proof is `sorry`. Challenge.lean imports the seven theorem mirrors.
"""
import pathlib, re, shutil

SRC = pathlib.Path("ElboimSly/Frozen")
DST = pathlib.Path("ElboimSlyChallenges/ElboimSly")
IMP = re.compile(r"^(public\s+)?import\s+(\S+)\s*$")
HEADER = ("/-\nCopyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.\n"
          "Released under Apache 2.0 license as described in the file LICENSE.\n"
          "Authors: Scott Armstrong, Ahmed Bou-Rabee\n-/\n")

for sub in ("Defs", "Theorems"):  # Theorems/ is no longer generated
    if (DST / sub).exists(): shutil.rmtree(DST / sub)
# declared name -> definition file, for theorem files that saw the definitions only through their proof
DEFNAME = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|structure|class|inductive|instance)\s+([^\s:({\[]+)", re.M)
defs_of = {}
for f in sorted((SRC / "Defs").glob("*.lean")):
    for n in DEFNAME.findall(f.read_text(encoding="utf8")): defs_of[n.split(".")[-1]] = f.stem
# theorem files that some definition file imports (`interchangePi` is defined from
# `existsUnique_trajectories`) are mirrored next to the definitions, with the body `sorry`
def_imported = set()
for f in (SRC / "Defs").glob("*.lean"):
    for l in f.read_text(encoding="utf8").split("\n"):
        m = IMP.match(l)
        if m and m.group(2).startswith("ElboimSly.Frozen.Theorems."):
            def_imported.add(m.group(2)[len("ElboimSly.Frozen.Theorems."):])
def mirror_def(rel, lines):
    out, skip = [], False
    for line in lines:
        m = IMP.match(line)
        if m and m.group(2).startswith("ElboimSly.Provider."):
            out.append("public import Mathlib"); continue
        if m and m.group(2).startswith("ElboimSly.Frozen."):
            line = f"{m.group(1) or ''}import ElboimSlyChallenges.ElboimSly.Defs." + m.group(2).split(".")[-1]
        if line.startswith("-- FROZEN_ANCHOR_PROOF_BEGIN"):
            out.append("  sorry"); skip = True; continue
        if line.startswith("-- FROZEN_ANCHOR_PROOF_END"): skip = False; continue
        if skip or line.startswith("-- FROZEN_ANCHOR_"): continue
        out.append(line)
    body = "\n".join(out)
    body = re.sub(r"\A/-.*?-/\n", HEADER, body, count=1, flags=re.S)
    dst = DST / "Defs" / rel.name; dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(body, encoding="utf8")


defs_done = 0
thm_bodies = []          # (name, challenge body, solution body, imports for challenge, imports for solution)
for src in sorted(SRC.rglob("*.lean")):
    rel = src.relative_to(SRC)
    text = src.read_text(encoding="utf8")
    lines = text.split("\n")
    imps = [m.group(2) for l in lines if (m := IMP.match(l))]
    if rel.parts[0] == "Theorems" and rel.stem in def_imported:
        mirror_def(rel, lines)   # stated beside the definitions only (comparator lists its library name)
        continue
    if rel.parts[0] == "Defs":
        mirror_def(rel, lines)
        defs_done += 1
        continue
    # a theorem file: keep everything after the module docstring, i.e. its `public section ... end`
    i = next(k for k, l in enumerate(lines) if l.startswith("/-!"))
    while not lines[i].rstrip().endswith("-/"): i += 1
    rest = lines[i + 1:]
    chal, sol, skip = [], [], False
    for l in rest:
        if l.startswith("-- FROZEN_ANCHOR_PROOF_BEGIN"):
            chal.append("  sorry"); skip = True; continue
        if l.startswith("-- FROZEN_ANCHOR_PROOF_END"): skip = False; continue
        if l.startswith("-- FROZEN_ANCHOR_"): continue
        if skip: sol.append(l); continue
        chal.append(l); sol.append(l)
    stmt = text.split("FROZEN_ANCHOR_PROOF_BEGIN")[0]
    deps = {d[len("ElboimSly.Frozen.Defs."):] for d in imps if d.startswith("ElboimSly.Frozen.Defs.")}
    for n, f in defs_of.items():
        if re.search(r"(?<![\w.])" + re.escape(n) + r"(?![\w'])", stmt): deps.add(f)
    provs = [d for d in imps if d.startswith("ElboimSly.Provider.")]
    # the challenge theorems live in `ElboimSly.Challenge`: unqualified names still resolve to the
    # `ElboimSly` definitions, and the library's own theorem names stay free
    def rens(ls):
        return [("namespace ElboimSly.Challenge" if l == "namespace ElboimSly" else
                 "end ElboimSly.Challenge" if l == "end ElboimSly" else l) for l in ls]
    chal, sol = rens(chal), rens(sol)
    thm_bodies.append((rel.stem, "\n".join(chal).strip(), "\n".join(sol).strip(), deps, provs))

doc_c = """
/-!
# Challenge: infinite cycles in the interchange process in five dimensions

The main results of D. Elboim and A. Sly, *Infinite cycles in the interchange process in five
dimensions* (arXiv:2211.17023v3), stated from Mathlib alone, in the namespace `ElboimSly.Challenge`:
Theorem 1 (`root_R2`), the bound `P(the cycle of 0 is finite) < 2/β` from its proof (`root_R1`), and
Theorem 3.2 with (H1)–(H5) (`ind_main`); and four theorems behind them: existence and uniqueness of
particle trajectories (`existsUnique_trajectories`), bijectivity of `π_s` (`interchangePi_bijective`),
the KMT coupling for Poisson increments (`poisson_kmt_coupling`), and the strong approximation that
replaces Theorem 7.5 of the paper (`x1theta_coupling`). They are the library's theorems of the same
names in the namespace `ElboimSly`. Existence and uniqueness of trajectories is stated in `Defs/`, as
`ElboimSly.existsUnique_trajectories` with the body `sorry`, because `interchangePi` is defined from
it; the comparator configuration lists it under that name.

Every definition the statements use is in its own file under `Defs/`; these import Mathlib and one
another only. Each theorem below has the body `sorry`. `Solution.lean` proves the same statements
from the library, and leanprover/comparator checks that the two agree, definitions included. The
statements and definitions are generated from those of the library by `scripts/build_challenge.py`.
-/
"""
doc_s = """
/-!
# Solution: infinite cycles in the interchange process in five dimensions

The seven statements of `Challenge.lean`, each proved by the corresponding theorem of the library
(`ElboimSly/Provider/`), under the same names. Generated by `scripts/build_challenge.py`.
-/
"""
all_deps = sorted({d for _, _, _, ds, _ in thm_bodies for d in ds})
chal = HEADER + "module\n\npublic import Mathlib\n" + "".join(
    f"public import ElboimSlyChallenges.ElboimSly.Defs.{d}\n" for d in all_deps) + doc_c
sol = HEADER + "module\n\npublic import Mathlib\n" + "".join(
    f"public import ElboimSly.Frozen.Defs.{d}\n" for d in all_deps) + "".join(
    f"public import {pv}\n" for _, _, _, _, ps in thm_bodies for pv in ps) + doc_s
for name, c, s, _, _ in thm_bodies:
    chal += f"\n/-! ## `{name}` -/\n\n{c}\n"
    sol += f"\n/-! ## `{name}` -/\n\n{s}\n"
(DST / "Challenge.lean").write_text(chal, encoding="utf8")
(DST / "Solution.lean").write_text(sol, encoding="utf8")
print(f"wrote {defs_done} definition mirrors, Challenge.lean and Solution.lean ({len(thm_bodies)} theorems)")
