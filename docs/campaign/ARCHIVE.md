# Archive ledger

Files moved out of the default build or out of the paper tree with `git mv`. No file has been deleted. Each entry gives the old path, the new path and the commit that made the move. Paths are relative to the repository root.

## Commit 2ec20eeb: paper build products and unreferenced figures

Moved to `archive/` (37 files, each a rename at 100% similarity; `git show -M --name-status 2ec20eeb`).

| old path | new path |
|---|---|
| paper/Figures/harnack-proof-outline.tikz.aux | archive/paper/Figures/harnack-proof-outline.tikz.aux |
| paper/Figures/harnack-type-connected-crossing-oldd.pdf | archive/paper/Figures/harnack-type-connected-crossing-oldd.pdf |
| paper/Figures/texput.log | archive/paper/Figures/texput.log |
| paper/Figures/both-balls-trun/0.5.png | archive/paper/Figures/unused/both-balls-trun/0.5.png |
| paper/Figures/both-balls-trun/0.5_.png | archive/paper/Figures/unused/both-balls-trun/0.5_.png |
| paper/Figures/both-balls-trun/1.0.png | archive/paper/Figures/unused/both-balls-trun/1.0.png |
| paper/Figures/both-balls-trun/1.0_.png | archive/paper/Figures/unused/both-balls-trun/1.0_.png |
| paper/Figures/both-balls-trun/1.5.png | archive/paper/Figures/unused/both-balls-trun/1.5.png |
| paper/Figures/both-balls-trun/1.5_.png | archive/paper/Figures/unused/both-balls-trun/1.5_.png |
| paper/Figures/both-balls-trun/1.8.png | archive/paper/Figures/unused/both-balls-trun/1.8.png |
| paper/Figures/both-balls-trun/1.8_.png | archive/paper/Figures/unused/both-balls-trun/1.8_.png |
| paper/Figures/both-balls-trun/2.0.png | archive/paper/Figures/unused/both-balls-trun/2.0.png |
| paper/Figures/both-balls-trun/2.0_.png | archive/paper/Figures/unused/both-balls-trun/2.0_.png |
| paper/Figures/both-balls/0.5.png | archive/paper/Figures/unused/both-balls/0.5.png |
| paper/Figures/both-balls/0.5_.png | archive/paper/Figures/unused/both-balls/0.5_.png |
| paper/Figures/both-balls/1.0.png | archive/paper/Figures/unused/both-balls/1.0.png |
| paper/Figures/both-balls/1.0_.png | archive/paper/Figures/unused/both-balls/1.0_.png |
| paper/Figures/both-balls/1.5.png | archive/paper/Figures/unused/both-balls/1.5.png |
| paper/Figures/both-balls/1.5_.png | archive/paper/Figures/unused/both-balls/1.5_.png |
| paper/Figures/both-balls/1.8.png | archive/paper/Figures/unused/both-balls/1.8.png |
| paper/Figures/both-balls/1.8_.png | archive/paper/Figures/unused/both-balls/1.8_.png |
| paper/Figures/both-balls/2.0.png | archive/paper/Figures/unused/both-balls/2.0.png |
| paper/Figures/both-balls/2.0_.png | archive/paper/Figures/unused/both-balls/2.0_.png |
| paper/Figures/comp/lfpp_15.png | archive/paper/Figures/unused/comp/lfpp_15.png |
| paper/Figures/comp/lfpp_20.png | archive/paper/Figures/unused/comp/lfpp_20.png |
| paper/Figures/comp/sandpile_15_.png | archive/paper/Figures/unused/comp/sandpile_15_.png |
| paper/Figures/comp/sandpile_20_.png | archive/paper/Figures/unused/comp/sandpile_20_.png |
| paper/Figures/constant-dependence.pdf | archive/paper/Figures/unused/constant-dependence.pdf |
| paper/Figures/fig-keylock.pdf | archive/paper/Figures/unused/fig-keylock.pdf |
| paper/Figures/fig-pinch-point.pdf | archive/paper/Figures/unused/fig-pinch-point.pdf |
| paper/Figures/harmonic-balls-no-trunc/1_1.png | archive/paper/Figures/unused/harmonic-balls-no-trunc/1_1.png |
| paper/Figures/harmonic-balls-no-trunc/1_2.png | archive/paper/Figures/unused/harmonic-balls-no-trunc/1_2.png |
| paper/Figures/harmonic-balls-no-trunc/9_5.png | archive/paper/Figures/unused/harmonic-balls-no-trunc/9_5.png |
| paper/Figures/harmonic-balls/1_1.png | archive/paper/Figures/unused/harmonic-balls/1_1.png |
| paper/Figures/harmonic-balls/1_2.png | archive/paper/Figures/unused/harmonic-balls/1_2.png |
| paper/Figures/harmonic-balls/3_2.png | archive/paper/Figures/unused/harmonic-balls/3_2.png |
| paper/Figures/harmonic-balls/9_5.png | archive/paper/Figures/unused/harmonic-balls/9_5.png |

## Development audit modules

Moved to `archive/HarmonicBalls/Audit/` (27 files, each a rename at 100% similarity; `git show -M --name-status` on the commit titled "Archive development audit modules"). Reason: development audit checks, superseded by `checks/AxiomGate.lean`. No file was deleted.

Kept in `HarmonicBalls/Audit/`, because five modules outside it import them: `GreenSubharmonicTestClass.lean` (imported by `HarmonicBalls/Proofs/Potential/BoundedJensenPotentialIntegrability.lean`, `BoundedJensenSmoothTests.lean` and `BoundedSubharmonicRepresentatives.lean`), `Section5InfimumSemantics.lean` (imported by `HarmonicBalls/Proofs/Sec5/PoleInfimumCharacterization.lean`) and `Section5ExhaustionCompatibility.lean` (imported by `HarmonicBalls/Proofs/Sec5/StrongCompatibilityAssembly.lean`). None of the three imports a moved module.

| old path | new path |
|---|---|
| HarmonicBalls/Audit/AppendixInputChecks.lean | archive/HarmonicBalls/Audit/AppendixInputChecks.lean |
| HarmonicBalls/Audit/ConeProbabilityLiterature.lean | archive/HarmonicBalls/Audit/ConeProbabilityLiterature.lean |
| HarmonicBalls/Audit/FirstPass11.lean | archive/HarmonicBalls/Audit/FirstPass11.lean |
| HarmonicBalls/Audit/GFFSamplewiseRepresentation.lean | archive/HarmonicBalls/Audit/GFFSamplewiseRepresentation.lean |
| HarmonicBalls/Audit/Sec11CirclePalmImportChecks.lean | archive/HarmonicBalls/Audit/Sec11CirclePalmImportChecks.lean |
| HarmonicBalls/Audit/Section10CrossingExports.lean | archive/HarmonicBalls/Audit/Section10CrossingExports.lean |
| HarmonicBalls/Audit/Section10JordanExport.lean | archive/HarmonicBalls/Audit/Section10JordanExport.lean |
| HarmonicBalls/Audit/Section11PinchMetricFieldConsumer.lean | archive/HarmonicBalls/Audit/Section11PinchMetricFieldConsumer.lean |
| HarmonicBalls/Audit/Section11PinchPositivity.lean | archive/HarmonicBalls/Audit/Section11PinchPositivity.lean |
| HarmonicBalls/Audit/Section11ProperGeodesics.lean | archive/HarmonicBalls/Audit/Section11ProperGeodesics.lean |
| HarmonicBalls/Audit/Section1ConditionalExports.lean | archive/HarmonicBalls/Audit/Section1ConditionalExports.lean |
| HarmonicBalls/Audit/Section2FourInputChecks.lean | archive/HarmonicBalls/Audit/Section2FourInputChecks.lean |
| HarmonicBalls/Audit/Section2VolumeGrowthInputs.lean | archive/HarmonicBalls/Audit/Section2VolumeGrowthInputs.lean |
| HarmonicBalls/Audit/Section3InputChecks.lean | archive/HarmonicBalls/Audit/Section3InputChecks.lean |
| HarmonicBalls/Audit/Section4InputChecks.lean | archive/HarmonicBalls/Audit/Section4InputChecks.lean |
| HarmonicBalls/Audit/Section5ConditionalExports.lean | archive/HarmonicBalls/Audit/Section5ConditionalExports.lean |
| HarmonicBalls/Audit/Section5ContinuityCompatibility.lean | archive/HarmonicBalls/Audit/Section5ContinuityCompatibility.lean |
| HarmonicBalls/Audit/Section5ExistenceUniqueness.lean | archive/HarmonicBalls/Audit/Section5ExistenceUniqueness.lean |
| HarmonicBalls/Audit/Section5InputChecks.lean | archive/HarmonicBalls/Audit/Section5InputChecks.lean |
| HarmonicBalls/Audit/Section5StagedChecks.lean | archive/HarmonicBalls/Audit/Section5StagedChecks.lean |
| HarmonicBalls/Audit/Section6AnnulusChecks.lean | archive/HarmonicBalls/Audit/Section6AnnulusChecks.lean |
| HarmonicBalls/Audit/Section6ConditionalExports.lean | archive/HarmonicBalls/Audit/Section6ConditionalExports.lean |
| HarmonicBalls/Audit/Section6FullInputChecks.lean | archive/HarmonicBalls/Audit/Section6FullInputChecks.lean |
| HarmonicBalls/Audit/Section8ConditionalExports.lean | archive/HarmonicBalls/Audit/Section8ConditionalExports.lean |
| HarmonicBalls/Audit/Section9ComparisonExports.lean | archive/HarmonicBalls/Audit/Section9ComparisonExports.lean |
| HarmonicBalls/Audit/Section9ThreeInputChecks.lean | archive/HarmonicBalls/Audit/Section9ThreeInputChecks.lean |
| HarmonicBalls/Audit/Section9UniquenessChecks.lean | archive/HarmonicBalls/Audit/Section9UniquenessChecks.lean |
