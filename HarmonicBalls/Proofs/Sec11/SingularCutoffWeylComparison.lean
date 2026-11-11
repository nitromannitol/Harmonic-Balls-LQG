import HarmonicBalls.Steps.Sec11.WeylLocalComposition
import HarmonicBalls.Steps.Sec11.ContinuousFieldShift
import HarmonicBalls.Steps.Sec11.SingularWeylBumpLength

/-! # Singular Weyl shifts via continuous cutoffs

The singular shifted metric is assumed to be a length metric. The staged
metric-field axioms provide this hypothesis for nonpositive compact bumps.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Away from zero, a continuous nonpositive shift of the singular metric
has the same internal distances as the corresponding shifted cutoff field.
The almost-sure length-metric hypotheses on the singular metric and its
shift are explicit. -/
theorem IsWholePlaneGFF.ae_internal_singularMetric_weylShift_eq_cutoff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (D ω u v) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (g : ℂ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hu : ∀ z, g z ≤ 0) (hξ : 0 ≤ ξ)
    (hshiftmetric : ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal))
    {r : ℝ} (hr : 0 < r) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (haway : ∀ n z, z ∈ U n → r ≤ ‖z‖) :
    let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
    ∀ᵐ ω ∂P, ∀ n x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal) (U n) x y =
      internalMetric (fun a b =>
        (weylScaling (𝔇 (hC ω)) ξ (fun z => g z + f z) a b).toReal) (U n) x y := by
  let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
  have hf : Continuous f := by
    apply continuous_const.mul
    apply (continuous_norm.max continuous_const).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  obtain ⟨c, hl⟩ := exists_lower_bound_of_continuous_compactSupport g hg hc
  have hbase := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ => f) (fun _ => hf) (fun _ => measurable_const)
  have hsum := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun _ z => g z + f z) (fun _ => hg.add hf) (fun _ => measurable_const)
  have hshift := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => f) h
    (fun _ => hf) (fun _ => measurable_const)).ae_weylScaling
  filter_upwards [hD, hmetric, hshiftmetric, hbase, hsum, hshift] with ω hd hm hsm hb hs hw n x y
  have hcomp : (fun a b => (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ g a b).toReal) =
      𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) := by
    funext a b
    have hn : 0 ≤ 𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) a b := by
      have ht := hs.2.1.triangle a b a
      rw [hs.2.1.self_eq_zero, hs.2.1.symm b a] at ht
      linarith
    have hw' := hw g hg a b
    rw [h𝔇.addFunPairing_addFunPairing (hC ω) hf hg] at hw'
    have hcomm : (fun z => f z + g z) = (fun z => g z + f z) := by
      funext z
      exact add_comm _ _
    rw [hcomm] at hw'
    rw [← hw', ENNReal.toReal_ofReal hn]
  have hsumcomp : (fun a b =>
      (weylScaling (𝔇 (hC ω)) ξ (fun z => g z + f z) a b).toReal) =
      𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) := by
    funext a b
    have hn : 0 ≤ 𝔇 (addFunPairing (hC ω) (fun z => g z + f z)) a b := by
      have ht := hs.2.1.triangle a b a
      rw [hs.2.1.self_eq_zero, hs.2.1.symm b a] at ht
      linarith
    rw [← hs.2.2.2.1 a b, ENNReal.toReal_ofReal hn]
  have hFshift : IsEuclideanLengthMetric
      (fun a b => (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ g a b).toReal) := by
    rw [hcomp]
    exact hs.2.1
  have heq := hb.1.internalMetric_weylScaling_twice_eq_of_eqOn hm hb.2.1 hξ
    (fun z => -α * Real.log ‖z‖) f g hg hl hu hd hb.2.2.2.1 hsm hFshift
    (hU n) (fun z hz => by simp only [f, max_eq_left (haway n z hz)]) x y
  rw [hcomp] at heq
  rwa [hsumcomp]


end HarmonicBalls
