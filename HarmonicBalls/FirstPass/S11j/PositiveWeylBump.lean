import HarmonicBalls.Steps.Sec11.SingularWeylBumpLength
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.FirstPass.S11j.PositiveWeylFinite

/-!
# Section 11: length metric after a nonnegative Weyl bump

Positive counterpart of `ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms`
(`Steps/Sec11/SingularWeylBumpLength.lean:19`), which covers nonpositive compactly supported bumps only. The shift
`u ≥ 0` of Lemma 11.15 (corrected paper lines 3659-3696) needs the bumped metric `e^{ξ u} D` to be a Euclidean length
metric.

The sign enters the nonpositive proofs only through the two-sided comparison `exp(ξ c) D ≤ e^{ξ f} D ≤ D`, which is
the zero Weyl comparison of the bump. For `0 ≤ f ≤ M` the same comparison reads `D ≤ e^{ξ f} D ≤ exp(ξ M) D`, and the
comparison with `D` is all the topology and the length property use. Deterministic: symmetry, triangle inequality and
the length identity come from the existing lemmas `weylScaling_symm`, `weylScaling_toReal_triangle` and
`weylScaling_internalMetric`, which carry no sign hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Deterministic: a nonnegative compactly supported continuous Weyl bump of a Euclidean length metric gives a
Euclidean length metric. The bumped metric is `E x y = (weylScaling D ξ f x y).toReal`. -/
theorem IsEuclideanLengthMetric.weylScaling_nonneg_bump_isLengthMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) (hl : ∀ z, 0 ≤ f z)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y)) :
    IsEuclideanLengthMetric (fun x y => (weylScaling D ξ f x y).toReal) := by
  obtain ⟨c, hc'⟩ := exists_lower_bound_of_continuous_compactSupport (fun z => -f z) hf.neg hc.neg
  have hM : ∀ z, f z ≤ -c := fun z => by
    have h : c ≤ -f z := hc' z
    linarith
  have hDnn : ∀ x y, 0 ≤ D x y := fun x y => by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  have hfin : ∀ x y, weylScaling D ξ f x y ≠ ⊤ := fun x y => by
    have hle := weylScaling_le_exp_mul_zero_of_le D hξ f hM x y
    rw [hzero x y] at hle
    exact (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne
  have hlow : ∀ x y, D x y ≤ (weylScaling D ξ f x y).toReal := fun x y => by
    have hmono : ENNReal.ofReal (D x y) ≤ weylScaling D ξ f x y := by
      rw [← hzero x y]
      exact weylScaling_mono_exponent D ξ 0 f
        (fun z => by simpa using mul_nonneg hξ (hl z)) x y
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin x y)).mp hmono
  have hup : ∀ x y, (weylScaling D ξ f x y).toReal ≤ Real.exp (ξ * (-c)) * D x y := fun x y => by
    have hle := weylScaling_le_exp_mul_zero_of_le D hξ f hM x y
    rw [hzero x y, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hle
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Real.exp_pos _).le (hDnn x y)) hle
  have hEofReal : ∀ x y, ENNReal.ofReal (weylScaling D ξ f x y).toReal = weylScaling D ξ f x y :=
    fun x y => ENNReal.ofReal_toReal (hfin x y)
  have hsymm : ∀ x y, (weylScaling D ξ f x y).toReal = (weylScaling D ξ f y x).toReal :=
    fun x y => congrArg ENNReal.toReal (hD.weylScaling_symm ξ f x y)
  refine ⟨?_, ?_, hsymm, ?_, ?_, ?_⟩
  · intro z
    have h1 := hup z z
    rw [hD.self_eq_zero, mul_zero] at h1
    have h2 : 0 ≤ (weylScaling D ξ f z z).toReal := ENNReal.toReal_nonneg
    show (weylScaling D ξ f z z).toReal = 0
    linarith
  · intro z w h
    have h' : (weylScaling D ξ f z w).toReal = 0 := h
    have h1 := hlow z w
    rw [h'] at h1
    exact hD.eq_of_eq_zero z w (le_antisymm h1 (hDnn z w))
  · exact hD.weylScaling_toReal_triangle ξ f hfin
  · intro U
    constructor
    · intro hU z hz
      obtain ⟨ε, hε, hball⟩ := (hD.isOpen_iff U).mp hU z hz
      exact ⟨ε, hε, fun w hw => hball w (lt_of_le_of_lt (hlow z w) hw)⟩
    · intro hU
      refine (hD.isOpen_iff U).mpr fun z hz => ?_
      obtain ⟨ε, hε, hball⟩ := hU z hz
      refine ⟨ε / Real.exp (ξ * (-c)), div_pos hε (Real.exp_pos _), fun w hw => hball w ?_⟩
      have h1 := hup z w
      have h2 : D z w * Real.exp (ξ * (-c)) < ε := (lt_div_iff₀ (Real.exp_pos _)).mp hw
      rw [mul_comm] at h2
      exact lt_of_le_of_lt h1 h2
  · intro z w
    exact hD.weylScaling_internalMetric ξ f hEofReal hsymm z w

/-- Almost surely, the nonnegative Weyl bump of the singular field's metric is a Euclidean length metric, for
every continuous compactly supported weight `f ≥ 0`. Positive counterpart of
`ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms`. -/
theorem ae_singularField_nonneg_weylBump_lengthMetric_of_metricFieldAxioms
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, 0 ≤ f z) →
      IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ f x y).toReal) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD] with ω hm hz
  intro f hf hc hl
  exact hm.weylScaling_nonneg_bump_isLengthMetric hξ f hf hc hl hz

/-- Almost surely, for one fixed nonnegative continuous compactly supported Weyl bump `f`, the bumped metric
`e^{ξ f} D` is a Euclidean length metric. Fixed-`f` form: the single almost-sure length property of
`D` (`ae_isEuclideanLengthMetric_of_metricFieldAxioms`) and the deterministic zero identity
`IsEuclideanLengthMetric.weylScaling_zero` suffice; no statement quantified over all `f` inside `∀ᵐ`. -/
theorem ae_fixedWeylBump_isEuclideanLengthMetric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) (hl : ∀ z, 0 ≤ f z) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ f x y).toReal) := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
      haxioms hgff hγ hγ₂ hα hD] with ω hm
  exact hm.weylScaling_nonneg_bump_isLengthMetric hξ f hf hc hl (hm.weylScaling_zero ξ)

end HarmonicBalls
