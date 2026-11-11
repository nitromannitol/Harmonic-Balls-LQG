import HarmonicBalls.Defs.Green

/-! # Harmonic balls (quadrature domains) for a measure on the plane

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Section 1.1
(lines 76-81 and 136-161). A *harmonic ball* for a measure `μ` centered at `z` (a *quadrature domain* for harmonic
functions in the terminology of Sakai and of Shahgholian–Sjödin) is an open set `Λ ∋ z` on which harmonic functions
satisfy the mean value property `f(z) = μ(Λ)⁻¹ ∫_Λ f dμ` (eq:harmonic-ball, line 78).

* `IsRegularOpen s`: `s` equals the interior of its closure (Theorem 1.1(a), line 154);
* `HausdorffContinuousOn Λ T`: `t ↦ Λ t` is continuous on `T` for the Hausdorff distance
  (Theorem 1.1(b), line 157); `hausdorffContinuousOn_iff_continuousOn_closure` identifies it with continuity of
  `t ↦ closure (Λ t)` in the space `Closeds ℂ` of closed sets with the Hausdorff edistance;
* `HasMeanValueProperty μ Λ z f`: `f` is `μ`-integrable on `Λ` and `f(z) μ(Λ) = ∫_Λ f dμ`;
* `IsHarmonicBall μ Λ z`: the harmonic ball of eq:harmonic-ball (line 78);
* `greenPotentialClass O D`: the class `H̃_O(D)` of Green potentials (eq:harmonic-fns, line 140);
* `harmonicBallTestClass Λ` and `IsHarmonicBallGen μ Λ z`: the enlarged class of test functions `f₁ + f₂` of
  lines 143-146 and the corresponding notion of harmonic ball, the one of Theorem 1.1 (line 150).

## Modelling choices

* *Integrability.* The paper's mean value property (eq:harmonic-ball) presupposes that `∫_Λ f dμ` exists; here it is
  the explicit conjunct `IntegrableOn f Λ μ` of `HasMeanValueProperty` (the Bochner integral of a non-integrable
  function is the junk value `0`). We also require `0 < μ(Λ) < ∞`, implicit in the division by `μ(Λ)`.
* *Harmonic near `closure Λ`.* "Harmonic in a neighborhood of the closure of `Λ`" is
  `InnerProductSpace.HarmonicOnNhd f (closure Λ)`: `f` is harmonic at every point of `closure Λ`, i.e. on an open
  neighbourhood of `closure Λ` (the union of the neighbourhoods given by `HarmonicAt`).
* *Signed Radon measures in `H̃_O(D)`.* A signed Radon measure on `ℂ` whose (closed) support lies in the bounded set
  `O \ D` has compact support `K ⊆ O \ D` and finite total variation; its Jordan decomposition is a pair of finite
  measures `ν₁, ν₂` concentrated on `K`, and conversely `ν₁ - ν₂` is such a signed measure. Its Green potential is
  `greenPotential O ν₁ - greenPotential O ν₂`. This matches the subharmonic-ball class of eq:sub-harmonic-potential
  (lines 746-751, "`ν` ... with compact support in `O`").
* *The condition on `O`, line 146 (suspected misprint).* The paper requires `f₂ ∈ H̃_O(Λ)` "for some `O` with
  `Λ ⊂ Ō`". Read literally this makes Theorem 1.1 false: if `S ⊆ Λ` is a segment through `z` and `O = B_R \ S`
  with `closure Λ ⊂ B_R`, then `Λ ⊂ Ō` and `f₂ = G_O(·, y) ∈ H̃_O(Λ)` for `y ∈ B_R \ closure Λ`, but `f₂(z) = 0`
  (`z ∈ ∂O`, a regular boundary point) while `∫_Λ f₂ dμ > 0` whenever `μ` charges open sets; so no `Λ` would be a
  harmonic ball (already for Lebesgue measure and `Λ = B_1(0)`). The remark of lines 753-754 identifies the enlarged
  class with the functions of eq:sub-harmonic-potential with `ν|_Λ = 0`, where `O` contains a neighbourhood of
  `closure Λ` (line 749), and the uniqueness proof (Lemma 9.1, lines 2285-2317) only uses `O = B_R ⊇ closure A`.
  We therefore require `closure Λ ⊆ O`, with `O` bounded and open (line 141).
* *Enlargement.* Line 137 says the class of harmonic functions is *enlarged*. For unbounded `Λ` there is no bounded
  `O ⊇ closure Λ`, so the literal class `{f₁ + f₂}` would be empty; `IsHarmonicBallGen` is therefore defined as
  `IsHarmonicBall` together with the mean value property on `harmonicBallTestClass Λ`. For bounded `Λ` (the case of
  Theorem 1.1(b)) both readings agree: `isHarmonicBallGen_iff_of_isBounded`.
* *Green function junk values.* `greenFunction O x y = 0` on the diagonal and off `O × O` (`Defs/Green.lean`). On
  `Λ ⊆ O` the potential `greenPotential O ν x` only evaluates `G_O(x, ·)` on `K ⊆ O \ Λ`, so `x ∉ K` and no diagonal
  value enters the mean value property.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology InnerProductSpace TopologicalSpace

/-! ## Regular open sets and Hausdorff continuity of families of sets -/

/-- A set is *regular open* if it is equal to the interior of its closure (Theorem 1.1(a), line 154: "`Λ_t(z)` is
equal to the interior of its closure"). Mathlib (v4.35.0-rc2) has no such predicate. -/
def IsRegularOpen {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  interior (closure s) = s

/-- A family of sets `t ↦ Λ t` is *continuous in the Hausdorff topology* on `T` (Theorem 1.1(b), line 157:
"increase continuously in `t` (in the Hausdorff topology)"): for every `t ∈ T` and `ε > 0`, the Hausdorff
edistance `d_H(Λ s, Λ t)` is `< ε` for `s ∈ T` near `t`. The Hausdorff edistance does not see the difference between
a set and its closure, see `hausdorffContinuousOn_iff_continuousOn_closure`. -/
def HausdorffContinuousOn (Λ : ℝ → Set ℂ) (T : Set ℝ) : Prop :=
  ∀ t ∈ T, ∀ ε > 0, ∀ᶠ s in 𝓝[T] t, hausdorffEDist (Λ s) (Λ t) < ε

/-! ## Harmonic balls -/

/-- The *mean value property* of `f` on `Λ` at `z` for `μ` (eq:harmonic-ball, line 78):
`f` is `μ`-integrable on `Λ` and `f(z) μ(Λ) = ∫_Λ f dμ`. For `0 < μ(Λ) < ∞` this is
`f(z) = ⨍_Λ f dμ` (`hasMeanValueProperty_iff_eq_setAverage`). -/
def HasMeanValueProperty (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) (f : ℂ → ℝ) : Prop :=
  IntegrableOn f Λ μ ∧ f z * μ.real Λ = ∫ x in Λ, f x ∂μ

/-- `Λ` is a *harmonic ball for `μ` centered at `z`* (eq:harmonic-ball, line 78): `Λ` is an open set containing
`z`, with `0 < μ(Λ) < ∞`, such that every function `f` harmonic in a neighbourhood of the closure of `Λ` satisfies the
mean value property `f(z) = μ(Λ)⁻¹ ∫_Λ f dμ` (with `f` integrable on `Λ`). -/
def IsHarmonicBall (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) : Prop :=
  IsOpen Λ ∧ z ∈ Λ ∧ 0 < μ Λ ∧ μ Λ < ⊤ ∧
    ∀ f : ℂ → ℝ, HarmonicOnNhd f (closure Λ) → HasMeanValueProperty μ Λ z f

/-- The class `H̃_O(D)` of Green potentials (eq:harmonic-fns, line 140): the functions
`x ↦ ∫_O G_O(x,y) ν(dy)` with `ν` a signed Radon measure with support in `O \ D`, written via its Jordan
decomposition `ν = ν₁ - ν₂`, with `ν₁, ν₂` finite measures concentrated on a compact set `K ⊆ O \ D`
(see the module docstring). In the paper `O, D` are bounded open sets (line 141).
Reading: the class is restricted to `ν = ν₁ - ν₂` with finite measures `ν₁, ν₂`
concentrated on one compact `K ⊆ O \ D`. The printed text (eq:harmonic-fns, line 140) speaks of a signed Radon measure
with support in `O \ D`. This reading weakens existence and strengthens uniqueness relative
to the printed class. -/
def greenPotentialClass (O D : Set ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (K : Set ℂ) (ν₁ ν₂ : Measure ℂ), IsCompact K ∧ K ⊆ O \ D ∧ IsFiniteMeasure ν₁ ∧ IsFiniteMeasure ν₂ ∧
    ν₁ Kᶜ = 0 ∧ ν₂ Kᶜ = 0 ∧ f = greenPotential O ν₁ - greenPotential O ν₂}

/-- The enlarged class of test functions of lines 143-146: `f = f₁ + f₂` with `f₁` harmonic in a neighbourhood of
`closure Λ` and `f₂ ∈ H̃_O(Λ)` for some bounded open `O` with `closure Λ ⊆ O`. The paper prints `Λ ⊂ Ō` (line 146);
`closure Λ ⊆ O` is the condition of lines 749 and 753-754 (see the module docstring: the printed condition makes
Theorem 1.1 false). -/
def harmonicBallTestClass (Λ : Set ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (f₁ f₂ : ℂ → ℝ) (O : Set ℂ), HarmonicOnNhd f₁ (closure Λ) ∧ IsOpen O ∧ Bornology.IsBounded O ∧
    closure Λ ⊆ O ∧ f₂ ∈ greenPotentialClass O Λ ∧ f = f₁ + f₂}

/-- `Λ` is a *harmonic ball for `μ` centered at `z` with respect to the enlarged class of test functions*
(lines 136-146), the notion of Theorem 1.1 (theorem:harmonic-balls, line 150): `Λ` is a harmonic ball
(eq:harmonic-ball) and every `f ∈ harmonicBallTestClass Λ` has the mean value property on `Λ` at `z`. For bounded
`Λ` the first conjunct is implied by the second (`isHarmonicBallGen_iff_of_isBounded`). -/
def IsHarmonicBallGen (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) : Prop :=
  IsHarmonicBall μ Λ z ∧ ∀ f ∈ harmonicBallTestClass Λ, HasMeanValueProperty μ Λ z f

/-! ## Sanity lemmas -/

theorem IsRegularOpen.isOpen {X : Type*} [TopologicalSpace X] {s : Set X} (h : IsRegularOpen s) : IsOpen s :=
  h ▸ isOpen_interior

/-- Open Euclidean balls are regular open. -/
theorem isRegularOpen_ball (z : ℂ) {r : ℝ} (hr : 0 < r) : IsRegularOpen (ball z r) := by
  unfold IsRegularOpen
  rw [closure_ball z hr.ne', interior_closedBall z hr.ne']

/-- `HausdorffContinuousOn` is continuity of `t ↦ closure (Λ t)` into `Closeds ℂ` with the Hausdorff edistance. -/
theorem hausdorffContinuousOn_iff_continuousOn_closure {Λ : ℝ → Set ℂ} {T : Set ℝ} :
    HausdorffContinuousOn Λ T ↔ ContinuousOn (fun t => Closeds.closure (Λ t)) T := by
  rw [EMetric.continuousOn_iff']
  have h : ∀ s : Set ℂ, ((Closeds.closure s : Closeds ℂ) : Set ℂ) = closure s := fun _ => rfl
  simp only [Closeds.edist_eq, h, hausdorffEDist_closure]
  rfl

theorem hausdorffContinuousOn_const (A : Set ℂ) (T : Set ℝ) : HausdorffContinuousOn (fun _ => A) T :=
  fun _ _ ε hε => Eventually.of_forall fun _ => by simpa [hausdorffEDist_self] using hε

theorem hasMeanValueProperty_iff_eq_setAverage {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {f : ℂ → ℝ}
    (hpos : μ Λ ≠ 0) (hfin : μ Λ ≠ ⊤) :
    HasMeanValueProperty μ Λ z f ↔ IntegrableOn f Λ μ ∧ f z = ⨍ x in Λ, f x ∂μ := by
  have h : μ.real Λ ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩
  unfold HasMeanValueProperty
  rw [setAverage_eq, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ h, mul_comm]

theorem zero_mem_greenPotentialClass (O D : Set ℂ) : (0 : ℂ → ℝ) ∈ greenPotentialClass O D :=
  ⟨∅, 0, 0, isCompact_empty, Set.empty_subset _, inferInstance, inferInstance, rfl, rfl, (sub_self _).symm⟩

/-- The Green function with pole `y ∈ O \ D` belongs to `H̃_O(D)` (take `ν = δ_y`). These are the test functions
`g(w) = G_{B_R}(w, x)`, `x ∈ B_R \ A`, of the uniqueness argument (Lemma 9.1, lines 2285-2317). -/
theorem greenFunction_mem_greenPotentialClass {O D : Set ℂ} {y : ℂ} (hy : y ∈ O \ D) :
    (fun x => greenFunction O x y) ∈ greenPotentialClass O D := by
  refine ⟨{y}, Measure.dirac y, 0, isCompact_singleton, Set.singleton_subset_iff.2 hy, inferInstance,
    inferInstance, by simp, rfl, ?_⟩
  funext x
  simp [greenPotential, integral_dirac]

theorem IsHarmonicBallGen.isHarmonicBall {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} (h : IsHarmonicBallGen μ Λ z) :
    IsHarmonicBall μ Λ z :=
  h.1

/-- For bounded `Λ`, every function harmonic near `closure Λ` lies in the enlarged test class (`f₂ = 0`). -/
theorem harmonicOnNhd_mem_harmonicBallTestClass {Λ : Set ℂ} (hΛ : Bornology.IsBounded Λ) {f : ℂ → ℝ}
    (hf : HarmonicOnNhd f (closure Λ)) : f ∈ harmonicBallTestClass Λ := by
  obtain ⟨r, hr⟩ := hΛ.subset_ball 0
  refine ⟨f, 0, ball 0 (r + 1), hf, isOpen_ball, isBounded_ball, ?_, zero_mem_greenPotentialClass _ _,
    (add_zero f).symm⟩
  exact (closure_minimal (hr.trans ball_subset_closedBall) isClosed_closedBall).trans
    (closedBall_subset_ball (lt_add_one r))

/-- For bounded `Λ`, `IsHarmonicBallGen` is the literal definition of lines 143-146: the mean value property for
all `f₁ + f₂` of the enlarged class. -/
theorem isHarmonicBallGen_iff_of_isBounded {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} (hΛ : Bornology.IsBounded Λ) :
    IsHarmonicBallGen μ Λ z ↔ IsOpen Λ ∧ z ∈ Λ ∧ 0 < μ Λ ∧ μ Λ < ⊤ ∧
      ∀ f ∈ harmonicBallTestClass Λ, HasMeanValueProperty μ Λ z f := by
  constructor
  · rintro ⟨⟨hO, hz, hpos, hfin, -⟩, h⟩
    exact ⟨hO, hz, hpos, hfin, h⟩
  · rintro ⟨hO, hz, hpos, hfin, h⟩
    exact ⟨⟨hO, hz, hpos, hfin, fun f hf => h f (harmonicOnNhd_mem_harmonicBallTestClass hΛ hf)⟩, h⟩

/-- The mean value property used in the uniqueness argument (Lemma 9.1(2), line 2308): if `Λ` is a harmonic ball
in the sense of Theorem 1.1 with `closure Λ ⊆ B_R(0)` and `x ∈ B_R(0) \ Λ` (possibly `x ∈ ∂Λ`), then
`∫_Λ G_{B_R}(w, x) μ(dw) = μ(Λ) G_{B_R}(z, x)`. -/
theorem IsHarmonicBallGen.hasMeanValueProperty_greenFunction {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : IsHarmonicBallGen μ Λ z) {R : ℝ} (hΛ : closure Λ ⊆ ball 0 R) {x : ℂ} (hx : x ∈ ball 0 R \ Λ) :
    HasMeanValueProperty μ Λ z (fun w => greenFunction (ball 0 R) w x) :=
  h.2 _ ⟨0, _, ball 0 R, harmonicOnNhd_const 0, isOpen_ball, isBounded_ball, hΛ,
    greenFunction_mem_greenPotentialClass hx, (zero_add _).symm⟩

end HarmonicBalls
