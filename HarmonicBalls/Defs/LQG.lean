import Mathlib
import HarmonicBalls.Defs.GFF

/-! # The γ-LQG area measure

Section 2.2 of Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795),
paper/lqg_harmonic_ball-corrected.tex, lines 390-398.

The γ-LQG area (Liouville) measure `μ_h` is the a.s. weak limit (eq:measure-lim, line 396)
`μ_h = lim_{ε → 0} ε^{γ²/2} e^{γ h_ε(z)} dz`, where `h_ε(z)` is the circle average of the field. Following
Duplantier-Sheffield 2011 (Prop. 1.1), the limit is taken along the dyadic scales `ε = 2^{-k}`, along which it
holds almost surely; the convergence is vague, i.e. tested against compactly supported continuous functions.

* `lqgApprox γ hε ε = ε^{γ²/2} e^{γ hε ε z} dz` (Lebesgue measure `withDensity`), for a circle-average function
  `hε : ℝ → ℂ → ℝ` (`hε ε z = h_ε(z)`).
* `IsLQGLimit γ hε m`: the deterministic statement that `m` is locally finite (Radon) and is the vague limit of
  `lqgApprox γ hε (2^{-k})` as `k → ∞`.
* `IsLQGMeasure P γ hε μ`: a.s., `IsLQGLimit γ (hε ω) (μ ω)`.
* `IsLQGMeasureOfField P γ α₀ hcirc μ`: `μ = μ_h` for the field `h = h^ℂ - α₀ log |·|` (eq:gff, line 380) whose
  circle averages are `fieldCircleAverage α₀ (hcirc ω)`.
* `addCircleAverage hε f`: the circle averages `(h + f)_ε(z) = h_ε(z) + f_ε(z)` of `h + f` for a function `f`
  (line 398); `μ_{h+f}` for a possibly random continuous `f : Ω → ℂ → ℝ` is
  `IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) (f ω)) μf`
  (used in Fact 2.1 III-IV).

Why the dyadic limit determines the paper's limit: Duplantier-Sheffield 2011 (Prop. 1.1 and Section 3) prove a.s.
convergence along `ε = 2^{-k}` and convergence in probability as `ε → 0`; hence whenever the limit in
eq:measure-lim exists a.s. (along `ε → 0`, or along any sequence `ε_n → 0`) it agrees a.s. with the dyadic limit.
A locally finite measure is determined by its integrals of compactly supported continuous functions
(`IsLQGLimit.unique`), so `IsLQGMeasure` determines `μ` up to a `P`-null set (`IsLQGMeasure.ae_eq`).

Measurability of `ω ↦ μ ω A` is not part of the definition; it follows from the vague convergence and the a.s.
continuity of the circle averages, and is left to the statements that need it.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

/-- The dyadic scale `2^{-k}`. -/
noncomputable def dyadicScale (k : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ k

/-- The approximation `ε^{γ²/2} e^{γ h_ε(z)} dz` of the γ-LQG measure (eq:measure-lim, line 396), where
`hε ε z = h_ε(z)` is the circle average of the field. -/
noncomputable def lqgApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))

/-- `IsLQGLimit γ hε m`: the measure `m` on `ℂ` is locally finite (Radon) and is the vague limit of the
approximations `ε^{γ²/2} e^{γ hε ε z} dz` along the dyadic scales `ε = 2^{-k}` (eq:measure-lim, line 396;
Duplantier-Sheffield 2011, Prop. 1.1): for every compactly supported continuous `f : ℂ → ℝ`,
`∫ f d(lqgApprox γ hε 2^{-k}) → ∫ f dm` as `k → ∞`. -/
structure IsLQGLimit (γ : ℝ) (hε : ℝ → ℂ → ℝ) (m : Measure ℂ) : Prop where
  /-- The limit is a Radon measure. -/
  isLocallyFiniteMeasure : IsLocallyFiniteMeasure m
  /-- Vague convergence along the dyadic scales. -/
  tendsto_integral : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun k : ℕ => ∫ z, f z ∂(lqgApprox γ hε (dyadicScale k))) atTop (𝓝 (∫ z, f z ∂m))

/-- `IsLQGMeasure P γ hε μ`: the random measure `μ : Ω → Measure ℂ` is the γ-LQG measure of a random generalized
function with circle averages `hε ω ε z = h_ε(z)` (eq:measure-lim, line 396): almost surely, `μ ω` is a Radon
measure and the vague limit of `ε^{γ²/2} e^{γ h_ε(z)} dz` along `ε = 2^{-k}`. Intended for `γ ∈ (0, 2)`. -/
def IsLQGMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hε : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) : Prop :=
  ∀ᵐ ω ∂P, IsLQGLimit γ (hε ω) (μ ω)

/-- `μ = μ_h`, the γ-LQG area measure (Section 2.2, line 390) of the field `h = h^ℂ - α₀ log |·|`
(eq:gff, line 380), where `hcirc ω r z = h^ℂ_r(z)` are the circle averages of the whole-plane GFF
(`IsWholePlaneGFF`). Duplantier-Sheffield 2011 construct such `μ` for `γ ∈ (0, 2)` (Prop. 1.1, stated there for a
zero-boundary GFF on a bounded domain; the whole-plane case follows by the Markov property); the limit is locally
finite near the origin only when `α₀ < Q` (line 373), so statements using this Prop assume `0 < γ < 2` and
`α₀ < lqgQ γ`. -/
def IsLQGMeasureOfField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsLQGMeasure P γ (fun ω => fieldCircleAverage α₀ (hcirc ω)) μ

/-- The circle averages `(h + f)_r(z) = h_r(z) + f_r(z)` of `h + f`, given the circle averages `hε` of `h` and a
function `f : ℂ → ℝ` (line 398: `μ_{h+f}` for continuous `f`). -/
noncomputable def addCircleAverage (hε : ℝ → ℂ → ℝ) (f : ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => hε r z + Real.circleAverage f z r

/-! ### Sanity checks -/

theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale; positivity

/-- For the (deterministic) circle-average function `hε ε z = -(γ/2) log ε`, the approximations
`ε^{γ²/2} e^{γ hε ε z} dz` are Lebesgue measure for every `ε > 0`. -/
theorem lqgApprox_neg_log (γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    lqgApprox γ (fun r _ => -(γ / 2) * Real.log r) ε = volume := by
  have h1 : ε ^ (γ ^ 2 / 2) * Real.exp (γ * (-(γ / 2) * Real.log ε)) = 1 := by
    rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [lqgApprox, h1, ENNReal.ofReal_one]
  exact withDensity_one

/-- Non-vacuity: Lebesgue measure is the LQG limit of the circle-average function `hε ε z = -(γ/2) log ε`. -/
theorem isLQGLimit_volume (γ : ℝ) : IsLQGLimit γ (fun r _ => -(γ / 2) * Real.log r) volume where
  isLocallyFiniteMeasure := inferInstance
  tendsto_integral f _ _ := by
    simp only [lqgApprox_neg_log γ (dyadicScale_pos _)]
    exact tendsto_const_nhds

/-- The LQG limit is unique: a locally finite measure is determined by its integrals of compactly supported
continuous functions (Riesz; Mathlib's `Measure.ext_of_integral_eq_on_compactlySupported`). -/
theorem IsLQGLimit.unique {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m m' : Measure ℂ} (h : IsLQGLimit γ hε m)
    (h' : IsLQGLimit γ hε m') : m = m' := by
  have := h.isLocallyFiniteMeasure
  have := h'.isLocallyFiniteMeasure
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  exact tendsto_nhds_unique (h.tendsto_integral f f.continuous f.hasCompactSupport)
    (h'.tendsto_integral f f.continuous f.hasCompactSupport)

/-- The LQG measure is a.s. unique. -/
theorem IsLQGMeasure.ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hε : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} (h : IsLQGMeasure P γ hε μ)
    (h' : IsLQGMeasure P γ hε μ') : ∀ᵐ ω ∂P, μ ω = μ' ω := by
  filter_upwards [h, h'] with ω hω hω' using hω.unique hω'

/-- Adding `f = 0` does not change the circle averages. -/
theorem addCircleAverage_zero (hε : ℝ → ℂ → ℝ) : addCircleAverage hε 0 = hε := by
  funext r z
  simp [addCircleAverage, Real.circleAverage_def]

end HarmonicBalls
