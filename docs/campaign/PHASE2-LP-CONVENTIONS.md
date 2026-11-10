# Phase 2: Lattice-Probability (LP) conventions

Digest for workers adding a module to LP, from a read-only survey of LP (branch `lean-v4.35`, HEAD 3912597) and of
`/home/nitro/subdiffusive-process` (branch `main`, HEAD c14a982). Where a file disagrees with this digest, the file wins.

## 1. Repository and pins
- LP: `/home/nitro/lean/Lattice-Probability-v435` (sandbox), branch `lean-v4.35`, clean. Toolchain `leanprover/lean4:v4.35.0-rc2`.
- Mathlib pin `065356127b`, same in LP and HB. HB pins LP at `3912597a70`: a new LP commit reaches HB only by a manifest bump.

## 2. Layout
- Subject directories under `LatticeProb/`: Walk, Graph, Network, Sandpile, Prob, Gauss, Lattice, Order, Analysis, Topology,
  Support, External, Meta, Combinatorics, Data, Euclidean, LinearAlgebra, Bonanno (509 files, adapted from leobon12).
- Lakefile: `LatticeProb` (not default; v4.32 modules); `LatticeProbV435` (default; root `LatticeProb/V435.lean`, 5 lines, no
  imports; globs LQG, MatedCRT, Bonanno); `LatticeProbAudit` (comparator surface, not default). `LQG/` and `MatedCRT/` are empty.
- Root index `LatticeProb.lean` (817 imports) includes v4.35 ports (`Prob.Birkhoff`), not `Bonanno/`; HB imports `Bonanno.*` directly.

## 3. Adding a module (CONTRIBUTING.md)
1. Place by subject, namespace `LatticeProb.<Subject>`, so short lemma names do not collide.
2. Header `/- ... -/` says what is proved and how; each outward-facing def or theorem has a `/-- ... -/` docstring with the
   result in words and formulas; a principal result opens with a bold lead.
3. Index: import in `LatticeProb.lean`; a principal theorem also goes into README "What is proved > Contents" and
   `LatticeProb/Meta/AxiomsAudit.lean` (590 `#print axioms` lines).
4. A cited result not proved here is a `Prop` in `External/` with its source in the docstring, taken as a hypothesis.
5. Adapted code: header naming source repository, commit and file; README credit; `NOTICE` if the license requires.
6. Metadata in `formalization.yaml` (`sources`, `automation.models`, `status.scope`). Never rename or restate a declaration a downstream repository uses.

## 4. Gates LP expects
- `lake exe cache get` (first time), `lake build`, `lake build LatticeProbAudit`. Never `lake clean`; `touch` does nothing.
- `python3 tools/check_warnings.py`; `lake build LatticeProb.Meta.AxiomsAudit` then `python3 tools/check_axioms.py`.
- `bash LatticeProbAudit/check_standalone.sh <Pair>/Challenge.lean` (and `--vocabulary`); `python3 tools/check_names.py PROMPTFILE`.
- `python3 tools/check_public_hygiene.py` (no local paths); CI on request: `python3 tools/verify.py --preflight-only`.

## 5. What an LP module must not contain
- `sorry`, `admit`, `axiom`, or a declaration not reducing to `propext`, `Classical.choice`, `Quot.sound`.
- HB- or IDLA-specific objects (`HarmonicBalls.*`, IDLA names, paper-specific definitions): general statements only.
- Local paths; fleet, worker, ticket or status vocabulary in names or docstrings; literature inputs as bare axioms.
- Raised `maxHeartbeats`; files over 1500 lines; adapted code without a source header.

## 6. Elaboration policy (CONTRIBUTING.md; not enforced by a tool)
- Named monotonicity lemmas and `calc`, not `nlinarith`; `rpow`/`exp` facts hoisted into private lemmas.
- No import narrowing or file split for speed without `lake env lean --profile` before and after.

## 7. Subdiffusive-process README style (item C)
- Sections: H1 title; "A Lean 4 formalization of" + paper citation (blockquote); content and status paragraphs; Main results
  (table: Paper | Lean declaration | Content); Verification; Size; Building; Repository layout; How this was built; Authors and citation; License.
- AI disclosure, whole paragraph: "The development used AI-assisted proof writing under human direction. [`formalization.yaml`]
  records the available automation and review information; verification of this release candidate is pending."
- Leaves out: model names, cost, agent or harness names, prompts, worker or ticket vocabulary, CI internals, logs.
  The local copy is Lean v4.26.0 (its README says so); five `*-release-*` copies not read.

## 8. Open questions (operator)
1. New v4.35 modules: subject directories under `LatticeProb/` (as `Prob.Birkhoff`), or the `LatticeProbV435` globs?
2. Which LP working branch do Haiku workers use? Only `lean-v4.35` and `main` exist locally.
3. Add Harmonic-Balls-LQG to `status.scope` and `claude-haiku-5-5` to `automation.models` (both absent)?

Stale LP text, not fixed: README "Building" says `lean4:v4.32.0` (`lean-toolchain`: v4.35.0-rc2); README "Repository layout"
omits Bonanno, Combinatorics, Data, Euclidean, LinearAlgebra, LQG, MatedCRT, and the root index omits Bonanno.
