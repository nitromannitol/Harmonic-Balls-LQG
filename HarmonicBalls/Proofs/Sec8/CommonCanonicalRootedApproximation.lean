import HarmonicBalls.Proofs.Sec8.CanonicalRootedApproximation
import HarmonicBalls.Proofs.Sec8.CommonContinuityApproximation

/-! # Common continuity sets for canonical rooted approximations

The distribution-valued reconstruction and imported Section 8 arguments use
Leonardo Bonanno's LatticeProb formalization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A reference singular measure and a unit-ball sampled measure have a
common deterministic continuity system. On it, their normalized masses are
limits of measurable field observables, with the rooted observable using the
original canonical field and the root. No joint law comparison is assumed. -/
theorem IsWholePlaneGFF.exists_common_canonical_rooted_mass_approximations
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} {Q : Measure Ω} {γ α α₀ R : ℝ}
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {gC : Ω → (ℂ → ℝ) → ℝ} {gcirc : Ω → ℝ → ℂ → ℝ}
    {ν : Ξ → Measure ℂ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hν : IsLQGMeasureOfField P γ α₀ hcirc ν)
    (hμ : IsLQGMeasureOfField Q γ α gcirc μ)
    (H : Ω → LQGMetric.DistC) (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[Q] (fun ω => gC ω φ.1))
    (hmass : ∀ᵐ ω ∂Q, μ ω (ball 0 1) ≠ 0)
    (hR : 0 < R)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ν ω (ball (0 : ℂ) r) ≠ 0) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ S : Set (Set ℂ), S.Countable ∧ IsPiSystem S ∧
      univ ∈ S ∧ (∀ A ∈ S, MeasurableSet A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S ∧
      ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
      ∃ g : S → ℕ → (LQGMetric.DistC × ℂ) → ℝ,
        (∀ A n, Measurable (f A n)) ∧ (∀ A n, Measurable (g A n)) ∧
        (∀ A, TendstoInMeasure P
          (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω)) atTop
          (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal)) ∧
        (∀ A, TendstoInMeasure (Q ⊗ₘ weightedRestrictionKernel Q μ
          (gGFF.aemeasurable_lqgMeasure hμ) (ball 0 1) measurableSet_ball
          (fun _ => 1) measurable_const)
          (fun n x => g A n (H x.1, x.2)) atTop
          (fun x => (normalizedRestriction
            ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal)) ∧
        (∀ (H₀ : Ξ → LQGMetric.DistC),
          (∀ φ : LQGMetric.TestC0,
            (fun ω => H₀ ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) →
          ∀ A, TendstoInMeasure P
            (fun n ω => f A n (fun φ : Section6.LocalTest (ball 0 ε) => H₀ ω φ.1.1)) atTop
            (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let : IsProbabilityMeasure Q := gGFF.isProbabilityMeasure
  let hm := gGFF.aemeasurable_lqgMeasure hμ
  let K := weightedRestrictionKernel Q μ hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  have hmass' : ∀ᵐ ω ∂Q, ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hmass, hμ] with ω hω hμω
    let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
    simp only [withDensity_const, one_smul]
    exact ⟨hω, measure_ball_ne_top⟩
  let : IsProbabilityMeasure (Q ⊗ₘ K) :=
    isProbabilityMeasure_weightedRestriction_compProd Q μ hm (ball 0 1)
      measurableSet_ball (fun _ => 1) measurable_const hmass'
  have hloc : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hroot := aemeasurable_recentered_of_weightedRestriction_compProd Q μ hm hloc
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  obtain ⟨ε, hε, S, hc, hp, hu, hs, hg, E, hEm, hmono, hunion, hbuffer,
    hfront, f, hfm, hflim⟩ :=
    hGFF.exists_common_continuity_reference_approximations (Q ⊗ₘ K)
      (fun x : Ω × ℂ => (μ x.1).map (fun v : ℂ => v - x.2))
      hν hroot.1 hroot.2 hR hpos
  obtain ⟨g, hgm, hglim⟩ := gGFF.exists_canonical_unitBall_rooted_mass_approximations
    hμ H hH hversion hmass hε.1 E hEm hmono hunion S hs
    (fun A hA => hfront.mono fun _ h => h A hA)
  refine ⟨ε, hε, S, hc, hp, hu, hs, hg, f, g, hfm, hgm, hflim, hglim, ?_⟩
  intro H₀ hversion₀ A
  apply TendstoInMeasure.congr_left ?_ (hflim A)
  intro n
  have heq := ae_forall_joint_functional_eq_of_coordinatewise_ae_eq
    (fun φ : Section6.LocalTest (ball 0 ε) => (hversion₀ φ.1).symm)
    (fun x (_ : Unit) => f A n x) ((hfm A n).comp measurable_fst)
  exact heq.mono (fun _ h => h ())

#print axioms IsWholePlaneGFF.exists_common_canonical_rooted_mass_approximations

end HarmonicBalls
