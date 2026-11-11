# Section 6 export checks: Lemma 6.5 and Lemma 6.12

TASK: z4-section6-annulus-export-check (worker z4, 2026-11-07). Lean file: `archive/HarmonicBalls/Audit/Section6AnnulusChecks.lean`.
Scope: the proved exports of Lemma 6.5 (`AnnulusIterationStmt`) and Lemma 6.12 (`ShellDecompositionStmt`) at their
exact frozen types; their dependencies by constant closure; Leonardo Bonanno's attribution. Lean only: no new
mathematics, no numbered closure, no edit to frozen, proposed or source files.

## Result

Both exports compile at their frozen types, and their printed axioms are standard.

| Result | Frozen statement (`Draft/Section6.lean`) | Provider, exact type | Literature dependence (constant closure) |
|---|---|---|---|
| Lemma 6.5, `lemma:annulus-iterate` | `HarmonicBalls.AnnulusIterationStmt` :289 | `HarmonicBalls.Section6.annulusIterationStmt_proved` (`Proofs/Sec6/AnnulusLawTransfer.lean:207`) | Bonanno's `LQGMetric.LM.lmLem3_1a`, reached through `annulus_iteration_range_of_distribution` (`Proofs/Sec6/AnnulusIteration.lean:66`, applied at :81). 10 LatticeProb modules, 55 HarmonicBalls constants |
| Lemma 6.12, `lemma:shell-decomposition` | `HarmonicBalls.ShellDecompositionStmt` :442 | `HarmonicBalls.shellDecompositionStmt_proved` (`Proofs/Sec6/ShellDecomposition.lean:164`) | None. No LatticeProb module and no `HarmonicBalls.Proposed` declaration; 46 HarmonicBalls constants |

Guards in the audit file (an error fails `lc` or `lb`):
- Each export's type is the bare frozen constant, so it carries no premise.
- The printed axioms of both exports, and of the consuming assembly, are within `propext`, `Classical.choice`, `Quot.sound`.
- The assembly `HarmonicBalls.Section6.section6_of_greenPotential_and_literature`
  (`Proofs/Sec6/Section6LiteratureAssembly.lean:23`) has no binder mentioning either frozen statement. Its binders are
  the staged inputs `hholder`, `hDG`, `hAff`, `hCC`, `hW`, `hE`, `hN`. It uses the Lemma 6.5 export at line 59 and the
  Lemma 6.12 export at line 66.
- No `HarmonicBalls.Proposed` declaration is reached from either export. A positive control confirms that the
  detector does reach the staged Proposed premises of the assembly, so the negative result is not vacuous.
- The Lemma 6.5 closure reaches `LQGMetric.LM.lmLem3_1a`. The Lemma 6.12 closure does not.

## Bonanno attribution

- Leonardo Bonanno's formalization supplies the Lemma 6.5 input: `LQGMetric.LM.lmLem3_1a`
  (module `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, line 104). Its Prop is `LMLem3_1a`
  (`LatticeProb/Bonanno/LQGMetric/Blueprint/LMResults.lean:113`). His file headers identify `LM` as Gwynne–Miller,
  *Local metrics of the Gaussian free field*, arXiv:1905.00379, Lemma 3.1 (`lem-annulus-iterate`). That is the reference
  cited as `gwynne2020local` in the paper and as GM20b in `docs/campaign/GRAPH.md:1858`.
- The bridge from his whole-plane field setting to the frozen pairing-valued GFF is in
  `Proofs/Sec6/AnnulusLawTransfer.lean` (module docstring, credited to him). It imports the Bonanno modules
  `LQGMetric.Field.GFFLaw`, `.CircleAvgRate` and `.ExistGFF`. The constant closure also reaches
  `LQGMetric.Statement.{Field,GFF}`.
- Credits in the repository (`grep "Leonardo Bonanno"`): `AnnulusLawTransfer.lean` (2), `AnnulusIteration.lean` (1), and
  each direct consumer of `annulusIterationStmt_proved`: `ThickAnnulusIteration`, `GeometricAnnulusIteration`,
  `ScaledGoodAnnulusIteration`, `Section6FromVolumeGrowth`, `Section6LiteratureAssembly`, `Section6VolumeGrowthAssembly`,
  `Section6FineSupportAssembly` (1 each). The new audit file credits him (2). `ShellDecomposition.lean` carries no credit,
  which is correct: it uses no Bonanno module.
- Naming hazard, not used here: Bonanno's docstrings also cite "GM Lemma 2.6" for the same `N = 0` hypotheses
  (`LMResults.lean:14, 22, 102`). That is a different label from the Lemma 6.5 citation, and this audit does not
  identify the source of "GM".

## Compiled implication versus source admission

- **Compiled implication (checked by Lean).** `lmLem3_1a` implies `annulus_iteration_range_of_distribution`, which with
  the bridge implies `annulusIterationStmt_proved : AnnulusIterationStmt.{u}`. The axiom guard runs over the full
  constant closure, including Mathlib, and finds no `sorry`. This is a relation between Lean declarations only.
  Bonanno's library is an external dependency (`.lake/packages/lattice-probability`). Its formal statements were not
  checked against the source text here.
- **Source admission (paper text, unchanged).** The corrected paper states Lemma 6.5 as a citation,
  `\begin{lemma}[\cite{gwynne2020local}]` (corrected tex lines 1266–1277), with no proof. The sentence before it reads
  "See~\cite[Lemma 3.1]{gwynne2020local} for a slightly more general statement" (tex:1263). The next proof in that
  region (tex:1282) is of `lemma:good-annuli`, not of Lemma 6.5. So the source admits Lemma 6.5 as a cited result.
  The compiled implication does not change that status. `GRAPH.md` (Lemma 6.5 entry, lines 480–490) says "Proof: none
  (cited)", and `INVENTORY.tsv` row 31 says "cited".
- **Lemma 6.12 has no source admission.** The corrected paper states it at tex lines 1640–1678 with no citation and
  proves it at tex lines 1679–1710.

## The replaced Gwynne–Miller input

- Lean: not a premise. The export types and the assembly binders carry no such hypothesis (guards above). No
  `HarmonicBalls.Proposed` declaration is in either closure. `docs/campaign/FROZEN.md:54` records "proved via Bonanno
  lmLem3_1a (operator approved E35)". `INPUT-REQUESTS.md` and `STATUS.md` contain no GM20b entry (grep).
- Remaining presentations. None is a Lean premise, and none was edited here:
  1. `HarmonicBalls/Draft/Section6.lean:84–85` (frozen): "Lemma 6.5 ... is cited from GM20b ..., its statement here is the
     input to be admitted". Also `:288`: "This is a literature input." Both describe the frozen statement as an
     admitted input, next to a compiled proof. The frozen file cannot be edited by this worker; the wording is an
     operator decision.
  2. `HarmonicBalls/Steps/Sec6/Prevalence.lean:19` (docstring): "Lemma 6.5 (GM20b Lemma 3.1) for annuli centred at z".
     The `GoodAnnuliSubRangeStep` Prop (lines 38–46) quantifies over `Ω`, `P`, `hC`, `hcirc`, `μ₀` and has no
     annulus-iteration premise.
  3. `docs/campaign/GRAPH.md:446` ("Lit: none directly (GM20b through Lemma 6.5)") and `:485` ("Lit: GM20b ... Lemma 3.1"),
     which predate E35. Not owned by this worker.

## Open items for the operator (no change made)

- Status wording differs. The E35 entry in `ESCALATIONS.md` (from line 182) says "Do not mark the numbered result
  closed yet", because the lean-statement-audit anchor and provider metadata are not yet recorded. The operator's entry there records approval of closure at this
  declaration and proof (08:20 UTC). `inbox.md:116–118` says "CLOSED". This audit does not close Lemma 6.5 or 6.12 and
  changes no status file.
- Written argument. No failing implication was found. The Lean chain compiles, and the source status of Lemma 6.5 is
  "cited", not "proved".

## Checks run

- `lc archive/HarmonicBalls/Audit/Section6AnnulusChecks.lean`: CHECK OK (final run; log `logs/lc/003946-1683614.log`).
- `lb HarmonicBalls.Audit.Section6AnnulusChecks`: BUILD OK (log `logs/lb/004002-1684446.log`).
- Printed axioms, from the lc log: `annulusIterationStmt_proved`, `shellDecompositionStmt_proved` and
  `section6_of_greenPotential_and_literature` each depend on `[propext, Classical.choice, Quot.sound]`.
- Forbidden-token scan (whole words `sorry admit axiom native_decide maxHeartbeats opaque unsafe implemented_by extern
  set_option`) over the audit file: 0 hits.
- Guard message, from the lc log: Lemma 6.5 closure has 55 HarmonicBalls constants and reaches the LatticeProb modules
  `Bonanno.LQGMetric.Field.GFFInvariance`, `.Statement.Field`, `.Statement.GFF`, `.Field.GFFLaw`, `.Blueprint.M2Defs`,
  `.Field.CircleAvgRate`, `Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction`, `.Field.ExistGFF`,
  `.Papers.LM.L3_4M6`, `.Blueprint.LMResults`. Lemma 6.12 closure has 46 HarmonicBalls constants and no LatticeProb module.
  The traversal does not enter Mathlib or Lean-core constants; the axiom check covers them.

## Not done

- No source check of Bonanno's formal statements against the paper, and no statement audit of `Draft/Section6`. The frozen
  statements are used as given.
- The bibliographic record in `GRAPH.md:1858` was not checked against a bibliography file, since the repository has none.
- No numbered closure is claimed by this audit or by the commit.
