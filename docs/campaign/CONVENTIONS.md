# Conventions (lead-owned; all workers follow)

- Ambient plane `ℂ`, Lebesgue measure `volume`, balls `Metric.ball z r` / `Metric.closedBall z r`; shared notation in
  `HarmonicBalls/Defs/Notation.lean` (`annulus`, `lqgQ`, `PolyHighProb`). Namespace `HarmonicBalls`.
- Paper line numbers refer to paper/lqg_harmonic_ball-corrected.tex. Cite them in every docstring (`(eq:..., line N)`).
- Numbering: one shared counter per section for theorem/prop/fact/cor/lemma/definition (paper/defs.tex:50-55);
  `problem` has its own counter and is not a result. Appendix results are A.1..A.6. Table: docs/campaign/INVENTORY.tsv.
- Draft statements: `def <Name>Stmt : Prop` in `HarmonicBalls/Draft/Section<k>.lean` (appendix: `SectionA.lean`),
  docstring `Lemma 3.2 (lemma:non-coincidence-open-harmonic, line 627)`. Names: column draft_name of INVENTORY.tsv.
- Randomness: a statement about the field quantifies over a probability space `(Ω, P)` and a field satisfying the
  defining Prop of `HarmonicBalls/Defs/GFF.lean`, and a random measure satisfying the defining Prop of
  `Defs/LQG.lean`; "on an event of probability one" is `∀ᵐ ω ∂P`; "for each fixed t, a.s." keeps the order of the paper's
  quantifiers exactly (∀ t, ∀ᵐ ω  versus  ∀ᵐ ω, ∀ t).
- Green function: `greenFunction O x y : ℝ` with ΔG_O(x,·) = -δ_x (Prop 2.3, line 480). The paper's value +∞ on the
  diagonal is replaced by a junk value; every definition and statement evaluating G at `x = y` excludes the diagonal
  explicitly. Distributional (in)equalities: `Defs/Laplacian.lean`.
- Literature inputs: never an axiom. A cited fact is a `def <Name> : Prop` with docstring (source, theorem number, page),
  staged in `HarmonicBalls/Proposed/*.lean`; the operator admits it into `HarmonicBalls/External`. Proofs take it as an
  explicit hypothesis.
- Every Defs file ends with small sanity lemmas showing the definitions are not vacuous where cheap (e.g. `0` is a
  supersolution), and has no sorry/axiom.
- Test functions are `ContDiff ℝ ∞` (NOT `⊤`: in this Mathlib `⊤ : WithTop ℕ∞` is ω, analytic; compactly supported
  analytic functions vanish). `open scoped ContDiff` makes `ω` a token: do not name sample points `ω` in such files.
- Corrections in force for drafts: ~/paper-fleets/hb/CORRECTIONS-PROPOSED.md ([C1]-[C6]; C1, C5 provisional).
- Field interface: `IsWholePlaneGFF P hC hcirc`, field h = h^ℂ - α₀ log|·| (`fieldPairing`, `fieldCircleAverage`), `σ(h|_U)` =
  `fieldSigmaAlgebra`; μ_h: `IsLQGMeasureOfField P γ α₀ hcirc μ` (assume 0 < γ < 2, α₀ < lqgQ γ). Locality ("measurable w.r.t.
  σ(h|_U)") = a.s. equal to a fieldSigmaAlgebra-measurable variable.
