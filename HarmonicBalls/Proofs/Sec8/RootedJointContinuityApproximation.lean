import HarmonicBalls.Proofs.Sec8.RootedJointMassApproximation
import HarmonicBalls.Proofs.Sec8.RootedSamplingBallMass

/-! # Shared continuity systems for rooted mass approximations

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The rooted joint comparison is an
explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A reference field and a weighted rooted field have common continuity
sets and common normalized mass approximations when their joint local
observations satisfy the stated domination. -/
theorem IsWholePlaneGFF.exists_rooted_common_continuity_approximations
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
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0))) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ S : Set (Set ℂ), S.Countable ∧ IsPiSystem S ∧
      univ ∈ S ∧ (∀ A ∈ S, MeasurableSet A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S ∧
      ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
        (∀ A n, Measurable (f A n)) ∧
        (∀ A, TendstoInMeasure P
          (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω)) atTop
          (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal)) ∧
        (∀ A, TendstoInMeasure (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw)
          (fun n x => f A n (Y ε x)) atTop
          (fun x => (normalizedRestriction
            ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal)) ∧
        ∀ᵐ x ∂(Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw),
          ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) ≠ 0 ∧
          ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) ≠ ∞ := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let : IsProbabilityMeasure Q := gGFF.isProbabilityMeasure
  let K := weightedRestrictionKernel Q μ hm B hB w hw
  let : IsProbabilityMeasure (Q ⊗ₘ K) :=
    isProbabilityMeasure_weightedRestriction_compProd Q μ hm B hB w hw hmass
  have hlocν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  have hlocμ : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hroot := aemeasurable_recentered_of_weightedRestriction_compProd Q μ hm hlocμ B hB w hw
  obtain ⟨ε, hε, S, hc, hp, hu, ho, hg, E, hEm, hmono, hunion, hb, hfν, hfμ⟩ :=
    exists_common_continuity_system_of_ae_locallyFinite P (Q ⊗ₘ K) ν
      (fun x : Ω × ℂ => (μ x.1).map (fun v : ℂ => v - x.2))
      (hGFF.aemeasurable_lqgMeasure hν) hroot.1 hlocν hroot.2 hR
  have hsets : ∀ A ∈ S, MeasurableSet A := fun A hA => (ho A hA).measurableSet
  have hpositive : ∀ᵐ ω ∂P, ν ω (⋃ n, E n) ≠ 0 ∧ ν ω (⋃ n, E n) ≠ ∞ := by
    filter_upwards [hlocν, hpos] with ω hl hω
    let : IsLocallyFiniteMeasure (ν ω) := hl
    rw [hunion]
    exact ⟨hω ε hε.1, measure_ball_lt_top.ne⟩
  obtain ⟨f, hfm, hfref, hfroot⟩ :=
    hGFF.common_rooted_normalizedMass_of_joint_domination gGFF hν hμ hm B hB w hw
      hmass hε.1 E hmono hunion S hsets
      (fun A hA => hfν.mono fun _ h => h A hA) hpositive
      (fun A hA => hfμ.mono fun _ h => h A hA) (Y ε) (hY ε) hEm hb
      (fun n z hz => hdom ε hε n z (hb n z hz))
  exact ⟨ε, hε, S, hc, hp, hu, hsets, hg, f, hfm, hfref, hfroot,
    ae_recentered_ball_mass_weightedRestriction_compProd Q μ hm hlocμ B hB w hw hε.1⟩

#print axioms IsWholePlaneGFF.exists_rooted_common_continuity_approximations

end HarmonicBalls
