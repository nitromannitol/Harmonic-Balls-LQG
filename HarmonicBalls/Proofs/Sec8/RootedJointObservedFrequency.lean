import HarmonicBalls.Proofs.Sec8.RootedJointContinuityApproximation
import HarmonicBalls.Proofs.Sec8.ObservedFrequencyApproximation

/-! # Observable rooted frequency under a joint field comparison

The phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The joint comparison remains an
explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Under joint local comparison, the rooted frequency event is measurable
through the translated local field and the sampled root. -/
theorem IsWholePlaneGFF.exists_rooted_observed_frequency_of_joint_domination
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} {Q : Measure Ω} {γ α α₀ R : ℝ}
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {gC : Ω → (ℂ → ℝ) → ℝ} {gcirc : Ω → ℝ → ℂ → ℝ}
    {ν : Ξ → Measure ℂ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hν : IsLQGMeasureOfField P γ α₀ hcirc ν)
    (hμ : IsLQGMeasureOfField Q γ α gcirc μ) (hm : AEMeasurable μ Q)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂Q, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    (hR : 0 < R)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ν ω (ball (0 : ℂ) r) ≠ 0)
    (Y : ∀ ε : ℝ, Ω × ℂ → (Section6.LocalTest (ball 0 ε) → ℝ))
    (hY : ∀ ε, Measurable (Y ε))
    (hdom : ∀ ε ∈ Ioo (0 : ℝ) R, ∀ n z,
      closedBall z (dyadicScale n) ⊆ ball 0 ε →
      (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw).map (fun x => (Y ε x,
        fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
          fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2)) ≪
      P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0)))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ ε ∈ Ioo (0 : ℝ) R,
      ∃ E : Set ((Section6.LocalTest (ball 0 ε) → ℝ) × ℂ), MeasurableSet E ∧
        ∀ᵐ x ∂(Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw),
          ((Y ε x, x.2) ∈ E ↔ ∀ᶠ N : ℕ in atTop,
            (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ x.1) β x.2 N₀
              a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) := by
  let : IsProbabilityMeasure Q := gGFF.isProbabilityMeasure
  let K := weightedRestrictionKernel Q μ hm B hB w hw
  let : IsProbabilityMeasure (Q ⊗ₘ K) :=
    isProbabilityMeasure_weightedRestriction_compProd Q μ hm B hB w hw hmass
  have hloc : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hμQ : AEMeasurable (fun x : Ω × ℂ => μ x.1) (Q ⊗ₘ K) := by
    apply (hm.measurable_mk.comp measurable_fst).aemeasurable.congr
    filter_upwards [ae_fst_of_ae_compProd Q K hm.ae_eq_mk] with x hx
    exact hx.symm
  have hlocQ : ∀ᵐ x ∂(Q ⊗ₘ K), IsLocallyFiniteMeasure (μ x.1) :=
    ae_fst_of_ae_compProd Q K hloc
  obtain ⟨ε, hε, S, hc, hp, hu, hs, hg, f, hfm, href, hroot, hball⟩ :=
    hGFF.exists_rooted_common_continuity_approximations gGFF hν hμ hm B hB w hw
      hmass hR hpos Y hY hdom
  let f' : S → ℕ → ((Section6.LocalTest (ball 0 ε) → ℝ) × ℂ) → ℝ :=
    fun A n p => f A n p.1
  have hfm' : ∀ A n, Measurable (f' A n) := fun A n => (hfm A n).comp measurable_fst
  have hlim : ∀ A, TendstoInMeasure (Q ⊗ₘ K)
      (fun n x => f' A n (Y ε x, x.2)) atTop
      (fun x => (normalizedRestriction
        ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal) := hroot
  obtain ⟨E, hE, he⟩ := exists_observed_frequency_event_of_mass_approximations
    (Q ⊗ₘ K) (fun x : Ω × ℂ => (Y ε x, x.2)) ((hY ε).prodMk measurable_snd)
    (fun x => μ x.1) ε hε.1 hμQ hlocQ hball S hc hg hp hs f' hfm' hlim
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  exact ⟨ε, hε, E, hE, he⟩

end HarmonicBalls
