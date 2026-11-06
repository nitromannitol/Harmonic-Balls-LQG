# Deterministic affine identities for the cone event

Task `cone-event-affine-identities-source-proof`, 2026-11-06. This is a
mathematical proof and implementation specification, not a compiled Lean
declaration, a new input, or a probability or frequency claim. Definitions are
the frozen `Defs/Geometry.lean:139–154`, `Defs/Notation.lean:15`,
`Defs/Annuli.lean:65`, and `Draft/Section11.lean:72`. In particular an annulus
is an open ball minus a **closed** ball, and the Green integrand is `∞` on
the diagonal. No real-valued potential is substituted for it.

## Geometry and Borelness

For any `Q : Set ℂ`, `IsCone Q` gives either `IsOpen Q` or `IsOpen Qᶜ`;
the latter gives `IsClosed Q`. Thus `MeasurableSet Q`. Since translation is a
homeomorphism with inverse subtraction, `coneAt Q z` is Borel. Hence
`annulus z a b ∩ coneAt Q z` is Borel for every real `a,b` and every `z`.
The cone need not itself be open: complements are included in `IsCone`.

Let `k > 0`. For `openSector v w`, membership is represented by strictly
positive real coefficients. Multiplication by `k` multiplies both coefficients
by `k`; the inverse transformation multiplies them by `k⁻¹`. Thus
`(fun x : ℂ => k • x) '' openSector v w = openSector v w`. A bijection maps
complements to complements, so the same equality holds for every `IsCone Q`.
This uses no linear independence of `v,w`. Translation and dilation give
the following set equalities for *all* real `a,b`, including empty annuli:

```lean
(fun x : ℂ => x + t) '' annulus z a b = annulus (z + t) a b
(fun x : ℂ => k • x) '' annulus z a b = annulus (k • z) (k*a) (k*b)
(fun x : ℂ => x + t) '' coneAt Q z = coneAt Q (z+t)
(fun x : ℂ => k • x) '' coneAt Q z = coneAt Q (k • z)
```

The last equality requires `IsCone Q` and `0 < k`; the third requires
neither. They follow by writing each point of `coneAt Q z` as `q+z`, using
injectivity for intersections, and using the cone equality. The annulus
equalities follow from invariance of distance under translation and
`dist (k • x) (k • z) = k * dist x z`; strict outer and strict inner
inequalities are both preserved. Existing dilation membership and preimage
lemmas are `Steps/Sec11/AnnulusDilation.lean:16,25`. No assumption `r > 0`
is needed for the covariance statements below.

## Exact transport statements

For implementation, use `open MeasureTheory Metric Set` and abbreviate
`S μ z a b := annulusGreenPotentialSup μ z a b`. All declarations in the
following block are proposed Lean types, not already checked theorems.

```lean
-- For all measures, with no cone hypothesis:
theorem greenSup_translate (μ : Measure ℂ) (t z : ℂ) (a b : ℝ) :
  S (μ.map (fun y : ℂ => y - t)) z a b = S μ (z+t) a b

-- For arbitrary Q, the hypothesis needed here is exactly Borelness
-- of the set whose mass is read by Measure.map_apply.
theorem coneMass_translate (μ : Measure ℂ) (Q : Set ℂ) (M r : ℝ)
    (z t : ℂ)
    (hB : MeasurableSet (annulus z r (2*r) ∩ coneAt Q z)) :
  coneMassEvent (μ.map (fun y : ℂ => y-t)) Q M r z ↔
    coneMassEvent μ Q M r (z+t)

theorem coneMass_dilate (μ : Measure ℂ) (Q : Set ℂ) (M r : ℝ)
    (z : ℂ) {k : ℝ} (hk : 0 < k) (hQ : IsCone Q) :
  coneMassEvent (μ.map (fun y : ℂ => k⁻¹ • y)) Q M r z ↔
    coneMassEvent μ Q M (k*r) (k • z)

theorem coneMass_affine (μ : Measure ℂ) (Q : Set ℂ) (M r : ℝ)
    (z t : ℂ) {k : ℝ} (hk : 0 < k) (hQ : IsCone Q) :
  coneMassEvent (μ.map (fun y : ℂ => k⁻¹ • (y-t))) Q M r z ↔
    coneMassEvent μ Q M (k*r) (k • z+t)
```

For `coneMass_translate`, `hB` is supplied by `IsCone Q`; it is weaker than
assuming a cone. For `coneMass_dilate` an even weaker sufficient condition is
Borelness of the target set together with `(fun x : ℂ => k • x) '' Q = Q`.
The affine formula's order is deliberate: its map is the inverse of
`x ↦ k • x + t`. Obtain it from translation applied at `k • z`, followed by
dilation of the translated-back measure, using `Measure.map_map` for the two
continuous maps. Reassociate `k*(2*r) = 2*(k*r)` and similarly for 3 and 6.
At `z=0`, `t=z₀` this is exactly recentering without rotating Q; taking
`t=0` gives the dyadic identity.

Proof of the first identity: set `A = annulus z a b` and use the Borel,
continuous inverse translation and `setLIntegral_map`. Its preimage of A is
`annulus (z+t) a b`. Translating `ball z b` yields `ball (z+t) b`;
`Section6.greenFunction_translate` (`Proofs/Sec6/GreenTranslation.lean:67`)
identifies the off-diagonal kernels, while injectivity identifies the two
diagonal tests and preserves their value `∞`. The extended kernel is Borel:
use the same `Measurable.ite`, singleton measurability and
`measurable_greenFunction` argument as in
`Steps/Sec11/AnnulusGreenDilation.lean:42–46`. Change the outer supremum index
bijectively by `x ↦ x+t`; both membership predicates correspond. This proves
the equality of extended nonnegative integrals and their suprema for arbitrary
`μ`, including zero, infinite and atomic measures. The dilation analogue is
already proved as `annulusGreenPotentialSup_comp_real_smul` at
`Steps/Sec11/AnnulusGreenDilation.lean:64` under exactly `0 < k`.

For the mass, the preimage of the Borel cone-annulus under the inverse map
is its affine image. `Measure.map_apply` therefore gives the mass equality.
Combine it with the Green-supremum equality and unfold `coneMassEvent`.
Nothing is canceled and no `toReal` or Bochner integral is involved.

## Mass normalization and consumer premises

For `c : ℝ≥0∞`, the *equalities* for both event operands under `c • μ`
hold for every c, including `0` and `∞`; see
`annulusGreenPotentialSup_smul` (`Proofs/Sec8/VeryGoodMeasureScaling.lean:31`)
and `Measure.smul_apply`. The equivalence of inequalities after cancellation
is ensured by `c ≠ 0` and `c ≠ ∞` (already proved as
`coneMassEvent_smul_iff`, `Proofs/GFF/FixedShiftCircleLQGRepresentation.lean:443`).
These are uniform sufficient conditions, necessary for a theorem over all
measures and events, though special events can have weaker conditions.

For a measurable `U` containing both event annuli, the exact available
`coneMassEvent_normalizedRestriction_iff`
(`Proofs/GFF/ConeMassLocalRepresentation.lean:48`) requires
`μ U ≠ 0` and `μ U ≠ ∞`; it then combines locality of the restrictions and
cancellation of `(μ U)⁻¹`. For unit scale `U = ball 0 7` contains both
annuli, since their outer radii are 2 and 6. A locally finite measure is
finite on this bounded ball via containment in compact `closedBall 0 7`.
For actual LQG measures, local finiteness is the a.e. field
`IsLQGLimit.isLocallyFiniteMeasure` from `IsLQGMeasureOfField`
(`Defs/LQG.lean:53–75`). Positivity on this nonempty open ball is supplied
by `LQGMeasureFullSupportStmt` (`Draft/Section2.lean:109`) under its stated
GFF, parameter and LQG hypotheses; that statement is a separate consequence,
not a field of `IsLQGLimit`. It is derivable from
`LQGVolumeGrowthAllScalesStmt` via
`lqgMeasureFullSupportStmt_of_volumeGrowth`; the latter in turn has the
source dependencies described in `Draft/Section2.lean:102–108`. Invoke the
actual available producer or carry this statement explicitly. For a
countable dyadic path intersect the a.e. assertions over the countable
indices; do not promote an a.e. equality to a pointwise one.

Likewise, converting a mass to `ENNReal.toReal` and back requires that mass
be finite (`ENNReal.ofReal_toReal` with `≠ ∞`). The finite-measure subtype
in `exists_coneMassEvent_countable_encoding`
(`ConeMassLocalRepresentation.lean:155–185`) supplies precisely this for
its normalized restriction; it is not a general property of `μ`. To identify
the extended integral with a Bochner Green integral at a point x, sufficient
conditions include `μ {x} = 0` and integrability of the real Green kernel on
the restricted annulus; nonnegativity and measurability then give the
nonnegative-integral identity. To convert an entire supremum to a real
quantity, one additionally needs finiteness of that supremum and appropriate
boundedness of the real family. Local finiteness alone does not provide these
conditions: an atom inside the Green annulus forces the extended supremum to
`∞`. The affine proof needs none of this; `greenPotential_translate` at
`Proofs/Sec6/GreenTranslation.lean:86` concerns a different, Bochner-defined
potential and alone does not establish the extended-kernel identity.

## Counterexamples to over-broad forms

Take `r=M=1`, `z=0`, and an open cone containing the positive real axis;
let `μ = dirac (3/2) + dirac 4` (complex points). The cone-annulus mass is
1. Because `4 ∈ annulus 0 3 6`, the diagonal term gives Green supremum
`∞`. Thus the event is false, while it is true for `0 • μ`, and also true
for `∞ • μ` (both sides then equal `∞` for the latter). Consequently neither
zero nor infinite mass scaling preserves the event in general. The same
example refutes replacing both event operands by their `toReal`: the false
extended inequality `∞ ≤ 1` becomes the true real inequality `0 ≤ 1`.
Even finite total mass does not make the Green supremum finite. A real
Bochner kernel with a junk diagonal cannot recover the extended atom term.

The geometric covariance also fails for an arbitrary Borel Q: let Q be the
open ball of radius `1/10` around `3/2`, `k=2`, `z=0`, `r=M=1`, and
`μ = ∞ • dirac 3 + dirac 8`. The inverse-dilated measure has infinite mass
at `3/2` in the cone-annulus and an atom at 4 in the Green annulus, so the
event is true. At scale 2 for μ, the Green supremum is `∞` but the cone
annulus has zero mass, so the event is false. Thus `k • Q = Q` is essential
to keeping the *same* Q. For `k=0` the map is not invertible, so neither
the set nor measure transport applies.

## Origin annulus distance

For `r>0`, let `A = annulus (0 : ℂ) r (6*r)`. It is nonempty: the real
point `2*r` has norm `2*r`, strictly between `r` and `6*r`. Every `y ∈ A`
has `r < ‖y‖ = dist 0 y`; by `Metric.le_infDist` and nonemptiness,
`r ≤ infDist 0 A`. Conversely, for every `ε>0`, take
`δ = min (ε/2) r` and the real point `y = r+δ`. Then `0<δ≤r`, hence
`r < ‖y‖ ≤ 2*r < 6*r`, so `y ∈ A` and
`infDist 0 A ≤ dist 0 y = r+δ < r+ε` by
`Metric.infDist_le_dist_of_mem`. Letting ε decrease to zero gives the
opposite inequality. Lean-ready target:

```lean
theorem infDist_origin_annulus (r : ℝ) (hr : 0 < r) :
  Metric.infDist (0 : ℂ) (annulus 0 r (6*r)) = r
```

Use `le_of_forall_pos_le_add` or an equivalent ε argument for the upper
bound; `Metric.le_infDist` explicitly requires nonemptiness. The infimum is
not attained at radius r, because the closed inner ball was removed.
Therefore `r/100 < infDist 0 A` follows from `hr` and arithmetic. No such
identity with the right side r holds for negative r (the distance is
nonnegative).

## Reuse and status

Existing spatial Green dilation and measure scaling are identified above;
translation of the extended annular integral, the cone geometry, and event
packaging remain implementation obligations. The Mathlib, MarkovProcess,
elliptic regularity and `/home/nitro/subdiffusive-process` searches did not
identify an existing cone-event transport declaration. No Lean file, frozen
statement, or literature input is changed by this audit.
