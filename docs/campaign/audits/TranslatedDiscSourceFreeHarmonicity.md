# Source-free potentials on translated discs

`HarmonicBalls.Proofs.Potential.TranslatedDiscSourceFreeHarmonicity` proves
harmonicity and continuity for a finite measure concentrated on a compact set
inside an arbitrary disc, both off that set and on any open subset of the disc
having zero source mass. The source-free continuity declaration uses `on` in
its name because `DiscChangedSourceObstruction` already has a declaration
with the corresponding `of` name.

The compact-source proof translates the measure and its concentration set to
a disc centred at zero, applies the existing centred-disc harmonicity theorem,
and transports harmonicity back. The open-set theorem removes the source-free
open set from the compact concentration set. The potential is the original
Bochner integral, with its existing totalized and diagonal semantics; no growth,
Hölder, or reciprocity hypothesis is added. The potential-theoretic
infrastructure uses work of Leonardo Bonanno.

This is a disc-only analytic leaf, not a numbered-result closure; general-domain
harmonicity is not established here. Lock-free compilation and the shared module
build pass. Each of the four declarations depends only on `propext`,
`Classical.choice`, and `Quot.sound`. The Lean file has no forbidden proof
tokens or heartbeat override.
