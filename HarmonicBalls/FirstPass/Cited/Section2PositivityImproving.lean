import Mathlib.MeasureTheory.Function.L2Space

/-!
# Proposition 2.6: irreducibility and positivity improving semigroups (cited)

The strict positivity in Proposition 2.6 (prop:lbm-continuity, paper/lqg_harmonic_ball-corrected.tex:560-:562) is
not part of Kigami 2019, Theorem 13.1 as printed. The route to it goes through the theorem that an irreducible
positivity preserving self-adjoint semigroup is positivity improving. This module states that literature input at
the level of semigroups on `L²(X, m)` of a finite measure, as the Prop `klvwPositivityImprovingCited`.

[KLVW] = M. Keller, D. Lenz, H. Vogt and R. Wojciechowski, *Note on basic features of large time behaviour of heat
kernels*, J. reine angew. Math. 708 (2015) (arXiv:1101.0373), Appendix A.

## The cited statement as printed

Definition A.1 of [KLVW]: "Let L be a selfadjoint operator in L²(X, m) and assume that −L generates a positivity
preserving semigroup (e^{−tL})_{t>0}. Then L is called irreducible if any closed subspace of L²(X, m) which is
• invariant under multiplication by bounded measurable functions and • invariant under the semigroup, agrees with
{0} or L²(X, m)."

Theorem A.2 of [KLVW]: "Let L be a selfadjoint operator in L²(X, m) which is bounded below. Assume that the semigroup
(e^{−tL})_{t>0} is positivity preserving. Then the following assertions are equivalent: (i) e^{−tL} is positivity
improving for one (all) t > 0. (ii) (L + α)^{−1} is positivity improving for one (all) α > −E₀(L). (iii) L is
irreducible."

Section 2 of [KLVW]: "A function f on X is called positive if ⟨f, f⟩ > 0 and f(x) ≥ 0 for m-almost every x ∈ X. A
function f on X is called strictly positive if f(x) > 0 for m-almost every x ∈ X. The semigroup (e^{−tL})_{t>0} is
called positivity preserving if e^{−tL} maps non-negative functions to non-negative functions for each t > 0; it is
called positivity improving if e^{−tL} f is strictly positive for any positive f and all t > 0." There `X` carries a
σ-finite measure `m`.

## Reading of the cited statement

* **Operators and semigroups.** A self-adjoint `L` bounded below gives the semigroup `T_t = e^{−tL}` of bounded
  self-adjoint operators, strongly continuous, with `‖T_t‖ ≤ e^{−E₀ t}`; conversely a strongly continuous semigroup
  of bounded self-adjoint contractions on a Hilbert space is `e^{−tL}` for a unique self-adjoint `L ≥ 0` (its
  generator). The statement is therefore made for strongly continuous semigroups `T : ℝ≥0 → (L² →L[ℝ] L²)` with
  `T 0 = 1`, `T (s + t) = T s ∘ T t`, `T t` self-adjoint and `‖T t f‖ ≤ ‖f‖`, positivity preserving and sub-Markov
  (`IsSymmetricMarkovSemigroup`). The sub-Markov condition (`0 ≤ f ≤ 1` implies `T t f ≤ 1`) and the finiteness of
  `m` are extra hypotheses; they only restrict the class of semigroups. The scalars are real: `L²(X, m)` is the real
  space `Lp ℝ 2 m`, and a positivity preserving operator on the complex space is the complexification of its
  restriction to real functions.
* **Irreducibility** (`IsIrreducibleSemigroup`) is Definition A.1, with "invariant under multiplication by bounded
  measurable functions" read as: for `f ∈ U` and a measurable `g` with `|g| ≤ C`, the class of `g f` lies in `U`.
* **Positive, strictly positive, positivity improving** are the definitions of Section 2 quoted above
  (`IsPositivityImprovingAt`).
* **Conclusions.** Only the equivalence of (i) and (iii) is stated, with (i) in both forms "for one t > 0" and
  "for all t > 0". The resolvent statement (ii) is not used and is not stated.

The invariant sets of a semigroup (`IsInvariantSet`) are recorded as vocabulary: for a measurable `E`, the closed
subspace `{f : f = 0 almost everywhere off E}` is invariant under multiplication by bounded measurable functions,
and it is invariant under the semigroup exactly when `T t (1_E f) = 1_E T t f` for all `t` and `f`.
-/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X]

/-- `IsSymmetricMarkovSemigroup m T`: `T` is a strongly continuous semigroup of self-adjoint contractions of the real
space `L²(X, m)`, positivity preserving and sub-Markov: `T 0 = 1`, `T (s + t) = T s ∘ T t`, `t ↦ T t f` continuous,
`⟪T t f, g⟫ = ⟪f, T t g⟫`, `‖T t f‖ ≤ ‖f‖`, `f ≥ 0` a.e. implies `T t f ≥ 0` a.e., and `f ≤ 1` a.e. implies
`T t f ≤ 1` a.e. for `0 ≤ f`. -/
structure IsSymmetricMarkovSemigroup (m : Measure X) (T : ℝ≥0 → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) :
    Prop where
  /-- `T 0` is the identity. -/
  map_zero : T 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 m)
  /-- The semigroup law. -/
  map_add : ∀ s t, T (s + t) = (T s).comp (T t)
  /-- Strong continuity. -/
  continuous : ∀ f, Continuous fun t => T t f
  /-- Each `T t` is symmetric. -/
  symm : ∀ t f g, ⟪T t f, g⟫_ℝ = ⟪f, T t g⟫_ℝ
  /-- Each `T t` is a contraction. -/
  norm_le : ∀ t f, ‖T t f‖ ≤ ‖f‖
  /-- Positivity preserving. -/
  nonneg : ∀ t (f : Lp ℝ 2 m), 0 ≤ᵐ[m] (f : X → ℝ) → 0 ≤ᵐ[m] (T t f : X → ℝ)
  /-- Sub-Markov. -/
  le_one : ∀ t (f : Lp ℝ 2 m), (∀ᵐ x ∂m, 0 ≤ (f : X → ℝ) x ∧ (f : X → ℝ) x ≤ 1) →
    ∀ᵐ x ∂m, (T t f : X → ℝ) x ≤ 1

/-- A measurable set `E` is *invariant* for `T` when `T t (1_E f) = 1_E T t f` for all `t` and `f`. -/
def IsInvariantSet (m : Measure X) (T : ℝ≥0 → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (E : Set X) : Prop :=
  MeasurableSet E ∧ ∀ t (f h : Lp ℝ 2 m), (h : X → ℝ) =ᵐ[m] E.indicator (f : X → ℝ) →
    (T t h : X → ℝ) =ᵐ[m] E.indicator (T t f : X → ℝ)

/-- **Irreducibility** ([KLVW], Definition A.1): every closed subspace of `L²(X, m)` invariant under
multiplication by bounded measurable functions and under the semigroup is `{0}` or `L²(X, m)`. -/
def IsIrreducibleSemigroup (m : Measure X) (T : ℝ≥0 → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) : Prop :=
  ∀ U : Submodule ℝ (Lp ℝ 2 m), IsClosed (U : Set (Lp ℝ 2 m)) →
    (∀ f ∈ U, ∀ (g : X → ℝ) (C : ℝ), Measurable g → (∀ x, |g x| ≤ C) →
      ∀ h : Lp ℝ 2 m, (h : X → ℝ) =ᵐ[m] (fun x => g x * (f : X → ℝ) x) → h ∈ U) →
    (∀ t, ∀ f ∈ U, T t f ∈ U) → U = ⊥ ∨ U = ⊤

/-- **Positivity improving at time `t`** ([KLVW], Section 2): `T t f` is strictly positive (`> 0` almost
everywhere) for every positive `f` (`f ≥ 0` almost everywhere and `⟪f, f⟫ > 0`). -/
def IsPositivityImprovingAt (m : Measure X) (T : ℝ≥0 → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (t : ℝ≥0) :
    Prop :=
  ∀ f : Lp ℝ 2 m, 0 ≤ᵐ[m] (f : X → ℝ) → 0 < ⟪f, f⟫_ℝ → ∀ᵐ x ∂m, 0 < (T t f : X → ℝ) x

/-- **The irreducibility criterion for positivity improving semigroups** ([KLVW], Theorem A.2, (i) ⟺ (iii)),
cited, for strongly continuous semigroups of self-adjoint sub-Markov contractions on `L²(X, m)` of a finite
measure: the semigroup is irreducible if and only if it is positivity improving for all `t > 0`, if and only if it
is positivity improving for one `t > 0`. PENDING TRUTH CHECK. See the module docstring for the reading. -/
def klvwPositivityImprovingCited : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (m : Measure X) [IsFiniteMeasure m]
    (T : ℝ≥0 → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m), IsSymmetricMarkovSemigroup m T →
    (IsIrreducibleSemigroup m T ↔ ∀ t : ℝ≥0, 0 < t → IsPositivityImprovingAt m T t) ∧
    (IsIrreducibleSemigroup m T ↔ ∃ t : ℝ≥0, 0 < t ∧ IsPositivityImprovingAt m T t)

end HarmonicBalls
