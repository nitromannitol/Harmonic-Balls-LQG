import HarmonicBalls.Proofs.Sec8.CommonCanonicalRootedApproximation

/-! # Common approximations for the inserted reference field

The distribution-valued reconstruction uses Leonardo Bonanno's LatticeProb
formalization. The reference decoder observes the field including its
logarithmic insertion; the rooted decoder observes the original canonical
field and the sampled root. Their identification remains open.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The reference and rooted normalized masses have separate measurable
approximations on a common continuity system. The reference input is the
local field with its origin insertion, which is the field appearing in the
rooted-law comparison. -/
theorem IsWholePlaneGFF.exists_common_inserted_canonical_rooted_mass_approximations
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
          (fun n ω => f A n (fun φ : Section6.LocalTest (ball 0 ε) =>
            hC ω φ.1.1 + ∫ x, φ.1.1 x * (-α₀ * Real.log ‖x‖))) atTop
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
            (fun n ω => f A n (fun φ : Section6.LocalTest (ball 0 ε) =>
              H₀ ω φ.1.1 + ∫ x, φ.1.1 x * (-α₀ * Real.log ‖x‖))) atTop
            (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal)) := by
  obtain ⟨ε, hε, S, hc, hp, hu, hs, hg, f, g, hfm, hgm, hf, hroot, hfversion⟩ :=
    hGFF.exists_common_canonical_rooted_mass_approximations gGFF hν hμ H hH hversion hmass hR hpos
  let undo : (Section6.LocalTest (ball 0 ε) → ℝ) → (Section6.LocalTest (ball 0 ε) → ℝ) :=
    fun v φ => v φ - ∫ x, φ.1.1 x * (-α₀ * Real.log ‖x‖)
  have hundo : Measurable undo := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply φ).sub_const _
  refine ⟨ε, hε, S, hc, hp, hu, hs, hg, (fun A n v => f A n (undo v)), g,
    (fun A n => (hfm A n).comp hundo), hgm, ?_, hroot, ?_⟩
  · intro A
    convert hf A using 1
    simp only [undo, add_sub_cancel_right]
    rfl
  · intro H₀ hversion₀ A
    convert hfversion H₀ hversion₀ A using 1
    simp only [undo, add_sub_cancel_right]

#print axioms IsWholePlaneGFF.exists_common_inserted_canonical_rooted_mass_approximations

end HarmonicBalls
