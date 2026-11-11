import HarmonicBalls.Steps.Sec11.MetricProperGeodesics

/-! # Conditional proper metric geodesic exports

These checks expose the staged propositions and the singular representative.
They do not establish either staged input or any numbered result.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

universe u

example {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      let Dh : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω =>
        weylScaling (𝔇 (hC ω)) ξ fun x => -α₀ * Real.log ‖x‖
      (∀ᵐ ω ∂P, (∀ u v, Dh ω u v < ∞) ∧
        IsEuclideanLengthMetric fun u v => (Dh ω u v).toReal) ∧
      (∀ U : Set ℂ, IsOpen U → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
        (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC U] fun ω => G ω z w) ∧
          ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
            internalMetric (fun u v => (Dh ω u v).toReal) U z w = G ω z w) ∧
      (∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
        weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
          weylScaling (fun u v => (Dh ω u v).toReal) ξ f u v) ∧
      (∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
        Dh ω (r * u + z) (r * v + z) =
          weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) r z)
            fun _ => lqgQ γ * Real.log r)) ξ
              (fun x => -α₀ * Real.log ‖(r : ℂ) * x + z‖) u v))
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ)
    (hD : ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 ∧
      ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) =
          weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    (hcompact : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ R : ℝ,
      IsCompact {z : ℂ | D ω x z ≤ R}) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      D ω (p s) (p t) = |(s : ℝ) - (t : ℝ)| * D ω x y :=
  ae_exists_geodesic_of_metricFieldAxioms_of_compact_closedBalls
    P γ ξ α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD hcompact

example {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hproper : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 →
      ∀ 𝔇' : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇' →
        ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ R : ℝ,
          IsCompact {w : ℂ | 𝔇' (hC ω) z w ≤ R})
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      𝔇 (hC ω) (p s) (p t) = |(s : ℝ) - (t : ℝ)| * 𝔇 (hC ω) x y :=
  ae_exists_geodesic_wholePlane_of_boundedlyCompact P γ ξ hC hcirc 𝔇
    hproper hgff hγ hγ₂ h𝔇

example {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) : ∃ p : Path x y, ∀ s t : Icc (0 : ℝ) 1,
      D (p s) (p t) = |(s : ℝ) - (t : ℝ)| * D x y :=
  hD.exists_geodesic_of_compact_closedBalls hnonneg hcompact x y

/- The remaining structures in the expanded hypotheses have these fields. -/
example {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hp : ∀ φ, IsTestFunction univ φ → Measurable fun ω => hC ω φ)
    (hc : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z)
    (hg : IsGaussianProcess (fun (o : GFFObservable.Admissible) ω =>
      o.1.eval (hC ω) (hcirc ω)) P)
    (hz : ∀ o : GFFObservable, o.IsAdmissible →
      ∫ ω, o.eval (hC ω) (hcirc ω) ∂P = 0)
    (hv : ∀ o o' : GFFObservable, o.IsAdmissible → o'.IsAdmissible →
      cov[fun ω => o.eval (hC ω) (hcirc ω),
        fun ω => o'.eval (hC ω) (hcirc ω); P] = wholePlaneGFFCov o o')
    (ht : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
      (Ioi 0 ×ˢ univ)) : IsWholePlaneGFF P hC hcirc :=
  ⟨hp, hc, hg, hz, hv, ht⟩

example (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (hm : ∀ z w, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w)
    (ha : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
      (∀ x, Measurable fun ω => f ω x) →
      SatisfiesLQGMetricAxioms P γ ξ 𝔇 (fun ω => addFunPairing (hC ω) (f ω))) :
    IsLQGMetric γ ξ 𝔇 := ⟨hm, ha⟩

example {D : ℂ → ℂ → ℝ}
    (hself : ∀ z, D z z = 0) (hsep : ∀ z w, D z w = 0 → z = w)
    (hsym : ∀ z w, D z w = D w z)
    (htri : ∀ x y z, D x z ≤ D x y + D y z)
    (htop : ∀ U : Set ℂ, IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w, D z w < ε → w ∈ U)
    (hlen : ∀ z w, ENNReal.ofReal (D z w) = internalMetric D univ z w) :
    IsEuclideanLengthMetric D := ⟨hself, hsep, hsym, htri, htop, hlen⟩

#print axioms IsEuclideanLengthMetric.exists_geodesic_of_compact_closedBalls
#print axioms ae_exists_geodesic_of_metricFieldAxioms_of_compact_closedBalls
#print axioms ae_exists_geodesic_wholePlane_of_boundedlyCompact

end HarmonicBalls
