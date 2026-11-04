import HarmonicBalls.Proofs.Sec5.FieldLocalExactHorizon
import HarmonicBalls.Proofs.Sec5.CenteredDiscLocality
import HarmonicBalls.Proofs.Sec5.RestrictedContainmentTest

/-! # A positive field-local time for the cluster family -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A positive field-local time at which the regularized family centred at
all points of the half-disc is compactly contained in the unit disc. The
stopped family has a simultaneous field-local representative. The
field-locality input is proposed and awaits source review. -/
theorem exists_positive_fieldLocal_time_and_family
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ τ : Ω → Ioi (0 : ℝ), ∃ F : Ω → (ball (0 : ℂ) (1 / 2) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] τ ∧
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] F ∧
      ∀ᵐ ω ∂P, ∀ z : ball (0 : ℂ) (1 / 2),
        closure (Λ ω z (τ ω)) ⊆ ball 0 1 ∧ F ω z = Λ ω z (τ ω) := by
  classical
  obtain ⟨H, hH, hHgood⟩ := exists_fieldLocal_exact_dyadic_containment_horizon
    hI2 h71 hγ hγ2 hα hGFF hμ hloc
  obtain ⟨E, G, hE, hG, hGeq⟩ := exists_local_lqg_bounded_stoppedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc (U := ball (0 : ℂ) 1) isOpen_ball isBounded_ball hΛ
  let T : Ω → ℝ := fun ω => if 0 < H ω then H ω / 2 else 1
  have hTpos (ω : Ω) : 0 < T ω := by
    dsimp [T]
    split <;> positivity
  let τ : Ω → Ioi (0 : ℝ) := fun ω => ⟨T ω, hTpos ω⟩
  have hτ : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] τ := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 1)
    apply Measurable.subtype_mk
    exact Measurable.ite (measurableSet_lt measurable_const hH) (hH.div_const 2) measurable_const
  let F : Ω → (ball (0 : ℂ) (1 / 2) → Set ℂ) := fun ω z =>
    {x | ∃ n : ℕ, H ω = (2 : ℝ)⁻¹ ^ n ∧
      x ∈ G ω (⟨z, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) z.property⟩,
        ⟨(2 : ℝ)⁻¹ ^ n / 2, by change 0 < (2 : ℝ)⁻¹ ^ _ / 2; positivity⟩)}
  have hF : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 1)
    apply Measurable.of_eval
    intro z
    apply Measurable.of_eval
    intro x
    apply Measurable.exists
    intro n
    apply Measurable.and
    · exact measurableSet_setOfPred.mp (measurableSet_eq_fun hH measurable_const)
    · change Measurable (fun ω => x ∈ G ω
        ((⟨z, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) z.property⟩ : ball (0 : ℂ) 1),
          (⟨(2 : ℝ)⁻¹ ^ n / 2, by change 0 < (2 : ℝ)⁻¹ ^ n / 2; positivity⟩ : Ioi (0 : ℝ))))
      exact (measurable_pi_apply x).comp ((measurable_pi_apply _).comp hG)
  refine ⟨τ, F, hτ, hF, ?_⟩
  filter_upwards [hHgood, hGeq,
    ae_regularizedClusterFamily_centeredDisc_compatibility hI2 hγ hγ2 hα hGFF hμ Λ hΛ]
    with ω hHω hGω hcompat
  intro z
  obtain ⟨n, hn⟩ := hHω.2.1
  have hτeq : (τ ω : ℝ) = H ω / 2 := by simp [τ, T, hHω.1]
  have htpos : 0 < (τ ω : ℝ) := (τ ω).property
  have htz : (τ ω : ℝ) < H ω := by rw [hτeq]; linarith [hHω.1]
  have hz1 : (z : ℂ) ∈ ball (0 : ℂ) 1 :=
    ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) z.property
  have hcl : closure (cluster (μ ω) 1 z (τ ω)) ⊆ ball 0 1 :=
    hHω.2.2.1 z z.property (τ ω) ⟨htpos, htz⟩
  have hclΛ : closure (Λ ω z (τ ω)) ⊆ ball 0 1 := by
    rw [hcompat 1 zero_lt_one z hz1 (τ ω) htpos (Or.inr hcl)]
    exact hcl
  refine ⟨hclΛ, ?_⟩
  have htime : (τ ω : ℝ) = (2 : ℝ)⁻¹ ^ n / 2 := by rw [hτeq, hn]
  have hGval : ∀ m : ℕ, H ω = (2 : ℝ)⁻¹ ^ m →
      G ω (⟨z, hz1⟩, ⟨(2 : ℝ)⁻¹ ^ m / 2, by change 0 < (2 : ℝ)⁻¹ ^ _ / 2; positivity⟩) = Λ ω z (τ ω) := by
    intro m hm
    have htime' : (τ ω : ℝ) = (2 : ℝ)⁻¹ ^ m / 2 := by rw [hτeq, hm]
    have hp := hGω (⟨z, hz1⟩, ⟨(2 : ℝ)⁻¹ ^ m / 2, by change 0 < (2 : ℝ)⁻¹ ^ _ / 2; positivity⟩)
    have hinside : closure (Λ ω z ((2 : ℝ)⁻¹ ^ m / 2)) ⊆ ball 0 1 := by
      simpa only [← htime'] using hclΛ
    have hg := hp.2 (hp.1.mpr hinside)
    simpa only [← htime'] using hg
  ext x
  constructor
  · rintro ⟨m, hm, hx⟩
    exact (hGval m hm) ▸ hx
  · intro hx
    exact ⟨n, hn, (hGval n hn).symm ▸ hx⟩

#print axioms exists_positive_fieldLocal_time_and_family

end HarmonicBalls
