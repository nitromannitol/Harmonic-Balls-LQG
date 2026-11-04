import HarmonicBalls.Proofs.Sec8.RootedSamplingBallMass
import HarmonicBalls.Proofs.Sec8.CommonNormalizedMassApproximation
import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance

/-! # Rooted normalized mass approximations

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. A common decoder's identity for
translated circle-average approximations remains an explicit condition.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A decoder which represents translated normalized circle-average
approximations converges under the normalized weighted rooted law on common
continuity sets. Translation covariance supplies the recentered LQG limit. -/
theorem tendstoInMeasure_rooted_normalizedMass_of_approximation
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P] {γ ε : ℝ}
    (hε : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hm : AEMeasurable μ P)
    (hμ : IsLQGMeasure P γ hε μ)
    (hc : ∀ᵐ ω ∂P, ∀ n, Continuous (hε ω (dyadicScale n)))
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    (hεpos : 0 < ε) (E : ℕ → Set ℂ) (hmono : Monotone E)
    (hunion : (⋃ n, E n) = ball 0 ε)
    (S : Set (Set ℂ)) (hsets : ∀ A ∈ S, MeasurableSet A)
    (hfront : ∀ A ∈ S, ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hm B hB w hw),
      let ν := (μ x.1).map (fun v : ℂ => v - x.2)
      (∀ n, ν (frontier (E n)) = 0 ∧ ν (frontier (A ∩ E n)) = 0) ∧
        ν (frontier (⋃ n, E n)) = 0 ∧ ν (frontier (A ∩ ⋃ n, E n)) = 0)
    (X : Ω × ℂ → F) (hX : Measurable X) (Fapprox : ℕ → F → Measure ℂ)
    (hFm : ∀ n, Measurable (Fapprox n))
    (hFeq : ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hm B hB w hw), ∀ n,
      Fapprox n (X x) = normalizedRestriction
        (lqgApprox γ (fun r z => hε x.1 r (z + x.2)) (dyadicScale n)) (E n)) :
    ∀ A : S, TendstoInMeasure (P ⊗ₘ weightedRestrictionKernel P μ hm B hB w hw)
      (fun n x => (Fapprox n (X x) A.val).toReal) atTop
      (fun x => (normalizedRestriction
        ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal) := by
  let K := weightedRestrictionKernel P μ hm B hB w hw
  let : IsProbabilityMeasure (P ⊗ₘ K) :=
    isProbabilityMeasure_weightedRestriction_compProd P μ hm B hB w hw hmass
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hbdd : Bornology.IsBounded (⋃ n, E n) := by rw [hunion]; exact isBounded_ball
  intro A
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => (ENNReal.measurable_toReal.comp
      (((Measure.measurable_coe (hsets A A.property)).comp (hFm n)).comp hX)).aestronglyMeasurable)
  filter_upwards [ae_fst_of_ae_compProd P K hμ, ae_fst_of_ae_compProd P K hc,
    hfront A A.property, hFeq,
    ae_recentered_ball_mass_weightedRestriction_compProd P μ hm hloc B hB w hw hεpos]
    with x hx hcx hfrontx hFx hpos
  let ν := (μ x.1).map (fun v : ℂ => v - x.2)
  have hlim := (Section6.isLQGLimit_translate hx hcx x.2).tendsto_normalizedRestriction_exhaustion
    (fun n => (hcx n).comp (continuous_id.add continuous_const)) E hmono hbdd A.val
    (hsets A A.property) hfrontx.1 hfrontx.2 (by simpa only [hunion] using hpos.1)
      (by simpa only [hunion] using hpos.2)
  have ht : ν (A.val ∩ ⋃ n, E n) / ν (⋃ n, E n) =
      normalizedRestriction ν (ball 0 ε) A.val := by
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (hsets A A.property), ENNReal.div_eq_inv_mul, hunion]
  rw [ht] at hlim
  have hlim' := (ENNReal.tendsto_toReal (measure_ne_top
    (normalizedRestriction ν (ball 0 ε)) A.val)).comp hlim
  change Tendsto (fun n => (Fapprox n (X x) A.val).toReal) atTop
    (𝓝 ((normalizedRestriction ν (ball 0 ε) A.val).toReal))
  simp_rw [hFx]
  exact hlim'

#print axioms tendstoInMeasure_rooted_normalizedMass_of_approximation

end HarmonicBalls
