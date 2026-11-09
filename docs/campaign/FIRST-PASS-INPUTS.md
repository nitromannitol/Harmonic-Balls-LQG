# FIRST PASS: inputs of the main theorems (HB)

Owner: worker n2, task `fp-HB-main-composition`. Source of truth: `HarmonicBalls/FirstPass/Main.lean`
(commit 1437843; strict `lc` OK, `lb HarmonicBalls.FirstPass.Main` OK; `#print axioms` of each
`firstPassMain_*` = `propext, Classical.choice, Quot.sound`).

## Classes

- **EXTERNAL**: a Prop used as an explicit hypothesis. Either a staged literature Prop (`Proposed/LQG.lean`, pending
  operator source-check), a cited input (Draft statement, not proved in the first pass), or a FIRST-PASS FROZEN Prop.
- **OPEN**: the Draft statement of a numbered result that is not yet PROVED-FP; left as a named hypothesis.
- Specialisations (`α₀ = 0` instances of `hCC`, `hE`, built inside the proofs) are not inputs; they are derived from
  the `∀ α₀` / `∀ α` forms that the hypotheses already carry.

## EXTERNAL hypotheses

| name | Prop | defined at | source locator (from docstring) |
|---|---|---|---|
| hDG | `WholePlaneLQGBallMassBounds` | `HarmonicBalls/Proposed/LQG.lean:152` | Ding-Gwynne, arXiv:1807.01072, Lemma 3.8 (p. 25), whole-plane case |
| hCC | `LQGMeasureCoordChange` (∀ α₀) | `Proposed/LQG.lean:114` | paper eq:measure-coord, line 412 (Fact 2.1 IV); Duplantier-Sheffield 2011 Prop 2.1 (p. 13); Sheffield-Wang 2016 |
| hE | `LQGMeasureExistence` (∀ α) | `Proposed/LQG.lean:66` | paper eq:measure-lim, line 396; Bou-Rabee-Gwynne arXiv:2208.11795v3 §2.2 p. 9; Duplantier-Sheffield arXiv:0808.1560v2 Prop 1.1; Berestycki-Powell arXiv:2404.16642v2 Thm 2.1 |
| hAff | `WholePlaneGFFAffineInvariance` | `Proposed/LQG.lean:51` | Gwynne-Holden-Sun arXiv:1910.04713v2 §3.2.2; paper line 367 |
| hW | `LQGMeasureWeylScaling` (α₀ = 0) | `Proposed/LQG.lean:93` | paper Fact 2.1 III, lines 406, 418 |
| hN | `LQGMeasureNonatomic` (∀ α₀) | `Proposed/LQG.lean:75` | paper Fact 2.1 I, lines 404, 418 (p. 9) |
| hmeasure | `LQGMeasureLocality` (∀ γ α₀) | `Proposed/LQG.lean:83` | paper Fact 2.1 II, lines 405, 418 |
| hmetricAxioms | `LQGMetricFieldAxioms` (∀ γ α₀ ξ) | `Proposed/LQG.lean:199` | paper Fact 2.2, lines 432-453; Ding-Dubedat-Dunlap-Falconet 2020, Dubedat-Falconet-Gwynne-Pfeffer-Sun 2020, Gwynne-Miller 2021 (as cited in INVENTORY 2.2) |
| hI2 | `LQGVolumeGrowthAllScalesStmt` | `HarmonicBalls/Draft/Section2.lean:122` | Input I2 (`docs/campaign/GRAPH.md:87`), paper eq:volume-growth (App A, line 3527) |
| hTor | `TorhorstSimpleLoopFrozen` (FIRST-PASS FROZEN) | `HarmonicBalls/FirstPass/Frozen/S1S10.lean:19` | Torhorst 1931; Jolivet-Loridant-Luo arXiv:1411.6776v1 Thm 3.1, p. 6; standard, locator pending |

## OPEN hypotheses (Draft statements not yet PROVED-FP)

| name | Draft Stmt | defined at | paper result |
|---|---|---|---|
| hTyp | `TypicalPointManyGoodScalesStmt` | `HarmonicBalls/Draft/Section8.lean:74` | Lemma 8.2, `lemma:mu_h-doubling-and-harnack` (paper line 2151) |
| h7 | `ManyConeBadScalesStmt` | `HarmonicBalls/Draft/Section11.lean:173` | Lemma 11.7, `lemma:mu_h-bad-and-harnack` (paper line 2802) |
| h13 | `ManyPinchScalesStmt` | `HarmonicBalls/Draft/Section11.lean:259` | Lemma 11.13, `lemma:mu_h-pinch-bad` (paper line 3144) |

## Per main theorem (Lean name: `HarmonicBalls/FirstPass/Main.lean`)

- **`firstPassMain_1_1`** (Theorem 1.1, `theorem:harmonic-balls`) → `ExistenceUniquenessHarmonicBallsStmt`.
  Hypotheses: hDG, hCC, hE (EXTERNAL); hTyp (OPEN, 8.2).
  Uses: `firstPass_1_1` ← `firstPass_5_5` (`FirstPass/S5S7S8.lean:161`), `firstPass_5_6` (`S5S7S8.lean:173`).

- **`firstPassMain_1_2`** (Theorem 1.2, `theorem:harmonic-balls-properties`) → `HarmonicBallNoveltyStmt`.
  Hypotheses: hDG, hAff, hCC, hW, hE, hN, hI2, hTor, hmetricAxioms (EXTERNAL); hTyp (OPEN, 8.2), h7 (OPEN, 11.7),
  h13 (OPEN, 11.13).
  Uses: `firstPass_1_2` ← 5.5, 5.6 (above); Jordan clause `firstPass_10_7` (`FirstPass/S1S10.lean:75`) ←
  `firstPass_10_6` (`S1S10.lean:92`) ← `firstPass_10_1` (`S1S10.lean:64`), `firstPass_3_2`
  (`FirstPass/S2S3S4S9SA.lean:66`); non-Lipschitz `firstPass_11_2` (`FirstPass/S11.lean:59`) ← `firstPass_11_5`
  (`S11.lean:67`) ← `firstPass_11_6` (`S11.lean:79`) ← `firstPass_6_8` (`FirstPass/S6.lean:61`), `firstPass_6_10`
  (`S6.lean:70`), `firstPass_8_1` (`FirstPass/S5S7S8.lean:72`), `firstPass_5_5`; non-metric-ball
  `firstPass_11_11` (`FirstPass/S11.lean:111`) ← `firstPass_11_6`.

- **`firstPassMain_1_3`** (Proposition 1.3, `prop:locally-determined`) → `HarmonicBallLocalSetStmt`.
  Hypotheses: hI2, hDG, hCC, hE, hmeasure (EXTERNAL); hTyp (OPEN, 8.2).
  Uses: `firstPass_1_3` (`FirstPass/S1S10.lean:53`) ← `firstPass_5_5`, `firstPass_5_6`.

## Flags for the operator

1. **hI2 classification.** `LQGVolumeGrowthAllScalesStmt` is treated as EXTERNAL (Input I2). Its Draft docstring
   (`Draft/Section2.lean:116-122`) says "the paper derives it from Lemma 2.4 and the scaling properties" and "It is
   a consequence, not a literature input". Lemma 2.4 is cited (INVENTORY 2.4). If I2 is NEW, it needs a
   `firstPass_2_x` theorem (Borel-Cantelli over dyadic scales from Lemma 2.4 and paper lines 3529-3530); none exists.
2. **Proposed docstrings.** `LQGMeasureWeylScaling` (`Proposed/LQG.lean:93`) says it is "expected to be proved rather
   than admitted". `LQGMeasureExistence` (`:66`) says the cited references treat bounded-domain fields and that the
   whole-plane transfer needs more. Both are staged literature inputs pending source-check.
3. **Specialisations.** Main hypotheses use the `∀ α₀` / `∀ α` forms (`hCC`, `hE`, `hN`, `hmeasure`) and derive the
   `α₀ = 0` instances inside the proof. No hypothesis is weakened.
