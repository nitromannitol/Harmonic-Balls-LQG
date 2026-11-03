import HarmonicBalls.Defs.Notation

/-! # The distributional Laplacian on the plane

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Section 1.6:
"Differential inequalities/equalities are interpreted in the distributional sense" (line 326). This file fixes
that meaning for the statements of the paper:

* `IsTestFunction U φ`: `φ : ℂ → ℝ` is smooth (`C^∞`) with compact support contained in `U`;
* `LaplacianLE w μ U`: `Δw ≤ μ` in `U`, e.g. the supersolution condition `Δw ≤ μ_h in B_r`
  (eq:super-solutions, line 584);
* `LaplacianGE w μ U`: `Δw ≥ μ` in `U`;
* `HasLaplacian w μpos μneg U`: `Δw = μpos - μneg` in `U`, e.g. `Δv = μ_h|_Λ + ν|_{∂Λ}` and
  `Δu = -t δ_z + μ_h|_Λ + ν|_{∂Λ}` of Lemma 3.2 (lemma:non-coincidence-open-harmonic, line 627), or
  `Δ q_{B_R} = -μ` (line 3540).

The Laplacian of a test function is Mathlib's `Laplacian.laplacian` (notation `Δ`, `open Laplacian`), the trace of
the second derivative; on `ℂ ≃ ℝ²` it is `∂²/∂x² + ∂²/∂y²`
(`InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane`).
A measure is a (positive) `MeasureTheory.Measure ℂ`; signed right-hand sides are written as a difference `μpos - μneg`.

## Integrability conventions

The pairing `⟨w, Δφ⟩ = ∫ w Δφ` is against Lebesgue measure, and `w` is required to be locally integrable on `U`.
The pairing `⟨μ, φ⟩ = ∫ φ dμ` is a Bochner integral; to keep the definitions exact for every measure (not only for
Radon measures, where test functions are automatically integrable), the integrability of `φ` against `μ` is
part of the statement:

* in `LaplacianLE` it is a hypothesis: if `∫ φ dμ = +∞` the inequality `⟨w, Δφ⟩ ≤ ⟨μ, φ⟩` holds trivially;
* in `LaplacianGE` and `HasLaplacian` it is a conclusion: `⟨μ, φ⟩ ≤ ⟨w, Δφ⟩ < ∞` forces it.

## Smoothness

Test functions are `ContDiff ℝ ∞`, i.e. `C^∞`, where `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` (`open scoped ContDiff`).
Note that `ContDiff ℝ ⊤` would mean `ContDiff ℝ ω` (real analytic), and a compactly supported real-analytic function
on the connected plane is zero, which would make every definition below vacuous. `IsTestFunction.exists_ne_zero`
records non-vacuity.
-/

namespace HarmonicBalls

open MeasureTheory Laplacian
open scoped ContDiff

/-- `φ : ℂ → ℝ` is a *test function on `U`*: it is smooth (`C^∞`), has compact support, and its support (the closure
of `{φ ≠ 0}`) is contained in `U`. These are the test functions of the distributional sense of line 326. -/
def IsTestFunction (U : Set ℂ) (φ : ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- `Δw ≤ μ` *in `U`* in the distributional sense (line 326): `w` is locally integrable on `U` and
`∫ w Δφ ≤ ∫ φ dμ` for every nonnegative test function `φ` on `U` (the inequality being trivial when
`∫ φ dμ = +∞`). For `μ = 0` this says that `w` is (weakly) superharmonic on `U`.
Used in the set of supersolutions `S_{B_r;z}(t)` (eq:super-solutions, line 584). -/
def LaplacianLE (w : ℂ → ℝ) (μ : Measure ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn w U ∧
    ∀ φ : ℂ → ℝ, IsTestFunction U φ → 0 ≤ φ → Integrable φ μ →
      ∫ x, w x * Δ φ x ≤ ∫ x, φ x ∂μ

/-- `Δw ≥ μ` *in `U`* in the distributional sense (line 326): `w` is locally integrable on `U` and, for every
nonnegative test function `φ` on `U`, `φ` is `μ`-integrable and `∫ φ dμ ≤ ∫ w Δφ`. For `μ = 0` this says that `w`
is (weakly) subharmonic on `U`. -/
def LaplacianGE (w : ℂ → ℝ) (μ : Measure ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn w U ∧
    ∀ φ : ℂ → ℝ, IsTestFunction U φ → 0 ≤ φ →
      Integrable φ μ ∧ ∫ x, φ x ∂μ ≤ ∫ x, w x * Δ φ x

/-- `Δw = μpos - μneg` *in `U`* in the distributional sense (line 326): `w` is locally integrable on `U` and, for every
test function `φ` on `U`, `φ` is integrable against `μpos` and `μneg` and `∫ w Δφ = ∫ φ dμpos - ∫ φ dμneg`.
Used for the Laplacians of the least supersolution and of the odometer in Lemma 3.2
(lemma:non-coincidence-open-harmonic, line 627: `Δu = -t δ_z + μ_h|_Λ + ν|_{∂Λ}` is
`HasLaplacian u (μ_h|_Λ + ν|_{∂Λ}) (t • δ_z) (B_r)`), and for `Δ q_{B_R} = -μ` (line 3540). -/
def HasLaplacian (w : ℂ → ℝ) (μpos μneg : Measure ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn w U ∧
    ∀ φ : ℂ → ℝ, IsTestFunction U φ →
      Integrable φ μpos ∧ Integrable φ μneg ∧ ∫ x, w x * Δ φ x = ∫ x, φ x ∂μpos - ∫ x, φ x ∂μneg

/-! ## Sanity lemmas -/

/-- Test functions exist: a smooth bump function supported in a ball `B_r(c) ⊆ U` is a test function on `U`
which equals `1` at `c`. In particular `IsTestFunction` is not vacuous. -/
theorem IsTestFunction.exists_ne_zero {U : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hU : Metric.ball c r ⊆ U) :
    ∃ φ : ℂ → ℝ, IsTestFunction U φ ∧ 0 ≤ φ ∧ φ c = 1 := by
  let f : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport, ?_⟩, fun x => f.nonneg, f.one_of_mem_closedBall ?_⟩
  · rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by simp [f]; linarith)).trans hU
  · simp [f]; positivity

/-- The zero function satisfies `Δ0 ≤ μ` in any set, for any measure `μ`: the zero function is a supersolution
(cf. "`S_{B_r;z}(t)` is non-empty as it contains the zero function", line 599). -/
theorem laplacianLE_zero (μ : Measure ℂ) (U : Set ℂ) : LaplacianLE 0 μ U := by
  refine ⟨locallyIntegrableOn_zero, fun φ _ hφ _ => ?_⟩
  simpa using integral_nonneg hφ

/-- `Δ0 = 0 - 0` in any set. -/
theorem hasLaplacian_zero (U : Set ℂ) : HasLaplacian 0 0 0 U :=
  ⟨locallyIntegrableOn_zero, fun φ _ => ⟨integrable_zero_measure, integrable_zero_measure, by simp⟩⟩

/-- `Δw = μpos - μneg` implies `Δw ≤ μpos`. -/
theorem HasLaplacian.laplacianLE {w : ℂ → ℝ} {μpos μneg : Measure ℂ} {U : Set ℂ}
    (h : HasLaplacian w μpos μneg U) :
    LaplacianLE w μpos U := by
  refine ⟨h.1, fun φ hφ hφ0 _ => ?_⟩
  obtain ⟨-, -, heq⟩ := h.2 φ hφ
  rw [heq]
  linarith [integral_nonneg (μ := μneg) hφ0]

/-- `Δw = μ - 0` implies `Δw ≥ μ`. -/
theorem HasLaplacian.laplacianGE {w : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ} (h : HasLaplacian w μ 0 U) :
    LaplacianGE w μ U := by
  refine ⟨h.1, fun φ hφ _ => ?_⟩
  obtain ⟨hint, -, heq⟩ := h.2 φ hφ
  exact ⟨hint, by rw [heq]; simp⟩

end HarmonicBalls
