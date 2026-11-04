#!/usr/bin/env python3
"""Generate the comparator challenge from the frozen files.

Usage, from the repository root: python3 -I scripts/build_challenge.py

Writes ElboimSlyChallenges/ElboimSly/Challenge.lean, a single file whose only import is Mathlib:
every frozen definition (and `existsUnique_trajectories`, from which `interchangePi` is defined),
in dependency order, with the same text as in the library, followed by the seven theorems in the
namespace `ElboimSly.Challenge`. Every proof is `sorry`. Solution.lean states the same theorems and
proves them from the library.
"""
import pathlib, re, shutil

SRC = pathlib.Path("ElboimSly/Frozen")
DST = pathlib.Path("ElboimSlyChallenges/ElboimSly")
IMP = re.compile(r"^(public\s+)?import\s+(\S+)\s*$")
HEADER = ("/-\nCopyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.\n"
          "Released under Apache 2.0 license as described in the file LICENSE.\n"
          "Authors: Scott Armstrong, Ahmed Bou-Rabee\n-/\n")

for sub in ("Defs", "Theorems"):  # no longer generated: the challenge is a single file
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
def def_block(lines, keep_proof=False):
    """The part of a frozen definition file after its module docstring, proofs replaced by `sorry`
    (kept, for the solution, when `keep_proof`)."""
    i = next(k for k, l in enumerate(lines) if l.startswith("/-!"))
    while not lines[i].rstrip().endswith("-/"): i += 1
    out, skip = [], False
    for line in lines[i + 1:]:
        if line.startswith("-- FROZEN_ANCHOR_PROOF_BEGIN"):
            if not keep_proof: out.append("  sorry")
            skip = not keep_proof; continue
        if line.startswith("-- FROZEN_ANCHOR_PROOF_END"): skip = False; continue
        if skip or line.startswith("-- FROZEN_ANCHOR_"): continue
        out.append(line)
    # `public section / opens / namespace ElboimSly / body / end ElboimSly / end` becomes
    # `section / opens / body / end` inside one `namespace ElboimSly.Challenge` (opens and variables
    # stay scoped)
    out = [l for l in "\n".join(out).strip().split("\n") if l.strip()]
    assert out[0] == "public section" and out[-1] == "end" and out[-2] == "end ElboimSly", out[:2] + out[-2:]
    assert out.count("namespace ElboimSly") == 1, out[:6]
    out = ["section"] + [l for l in out[1:-2] if l != "namespace ElboimSly"] + ["end"]
    return "\n".join(out)

def_blocks, sol_blocks, def_deps, def_provs = {}, {}, {}, set()
def mirror_def(rel, lines):
    def_blocks[rel.stem] = def_block(lines)
    sol_blocks[rel.stem] = def_block(lines, keep_proof=True)
    def_provs.update(m.group(2) for l in lines if (m := IMP.match(l)) and m.group(2).startswith("ElboimSly.Provider."))
    def_deps[rel.stem] = {m.group(2).split(".")[-1] for l in lines if (m := IMP.match(l))
                          and m.group(2).startswith(("ElboimSly.Frozen.Defs.", "ElboimSly.Frozen.Theorems."))}


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
dimensions* (arXiv:2211.17023v3), stated from Mathlib alone: Theorem 1 (`root_R2`), the bound
`P(the cycle of 0 is finite) < 2/β` from its proof (`root_R1`), and Theorem 3.2 with (H1)–(H5)
(`ind_main`); and four theorems behind them: existence and uniqueness of particle trajectories
(`existsUnique_trajectories`), bijectivity of `π_s` (`interchangePi_bijective`), the KMT coupling for
Poisson increments (`poisson_kmt_coupling`), and the strong approximation that replaces Theorem 7.5
of the paper (`x1theta_coupling`).

Every definition the statements use is given below, in the namespace `ElboimSly.Challenge`, with the
text of the library's definition of the same name in `ElboimSly`. `existsUnique_trajectories` is stated
among them because `interchangePi` is defined from it. Every proof is `sorry`. `Solution.lean` proves
the same statements from the library, and leanprover/comparator checks that the two agree,
definitions included. This file is generated from the library by `scripts/build_challenge.py`.
-/
"""
doc_s = """
/-!
# Solution: infinite cycles in the interchange process in five dimensions

The definitions of `Challenge.lean`, verbatim, and its seven statements, each proved by the library's
theorem of the same name in `ElboimSly` (`ElboimSly/Provider/`): every definition here unfolds to the
library's definition of the same name. Generated by `scripts/build_challenge.py`.
-/
"""
all_deps = sorted({d for _, _, _, ds, _ in thm_bodies for d in ds})
order, seen = [], set()
def visit(n):
    if n in seen: return
    seen.add(n)
    for m in sorted(def_deps[n]): visit(m)
    order.append(n)
for n in sorted(def_blocks): visit(n)
# The solution repeats the definitions verbatim, so that they elaborate exactly as in the challenge
# (same text, order and imports; Lean names the auxiliary proofs inside definitions per file), and
# proves every theorem by the library's theorem of the same name: the definitions of
# `ElboimSly.Challenge` unfold to those of the library.
DEFS_OPEN = "\n/-! ## Definitions -/\n\npublic section\n\nnamespace ElboimSly.Challenge\n"
DEFS_CLOSE = "\nend ElboimSly.Challenge\n\nend\n\n/-! ## Theorems -/\n"
chal = HEADER + "module\n\npublic import Mathlib\n" + doc_c + DEFS_OPEN
sol = HEADER + "module\n\npublic import Mathlib\n" + "".join(
    f"public import {pv}\n" for pv in sorted({pv for _, _, _, _, ps in thm_bodies for pv in ps} | def_provs)) + doc_s + DEFS_OPEN
for n in order:
    chal += f"\n{def_blocks[n]}\n"
    sol += f"\n{sol_blocks[n]}\n"
chal += DEFS_CLOSE
sol += DEFS_CLOSE
for name, c, s, _, _ in thm_bodies:
    chal += f"\n{c}\n"
    sol += f"\n{s}\n"
(DST / "Challenge.lean").write_text(chal, encoding="utf8")
(DST / "Solution.lean").write_text(sol, encoding="utf8")
print(f"wrote Challenge.lean ({len(order)} definition blocks, {len(thm_bodies)} theorems, "
      f"{chal.count(chr(10))} lines, {len(chal.encode())} bytes) and Solution.lean")
