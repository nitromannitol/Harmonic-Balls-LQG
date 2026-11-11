import HarmonicBalls.Proofs.Sec6.Section6FromExistence

/-! # Section 6 from a cofinal sequence of singularities

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller lemma
in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The literature inputs
below are explicit hypotheses and remain (PENDING TRUTH CHECK).
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter
open scoped ENNReal

universe u

/-- On one full-measure event, every subcritical LQG limit formed from these
circle averages has no atom at the origin. No joint measurability of the
family of limits is required. -/
theorem ae_origin_nonatomic_for_all_subcritical_limits
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ → ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ → μ {0} = 0 := by
  have hex (n : ℕ) : ∃ ν : Ω → Measure ℂ,
      IsLQGMeasureOfField P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hcirc ν := by
    apply hE n hG hγ hγ2
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  let ν : ℕ → Ω → Measure ℂ := fun n => Classical.choose (hex n)
  have hν (n : ℕ) : IsLQGMeasureOfField P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hcirc (ν n) :=
    Classical.choose_spec (hex n)
  have hνall : ∀ᵐ ω ∂P, ∀ n : ℕ, IsLQGLimit γ
      (fieldCircleAverage (lqgQ γ - 1 / ((n : ℝ) + 1)) (hcirc ω)) (ν n ω) :=
    ae_all_iff.mpr hν
  have hcall : ∀ᵐ ω ∂P, ∀ n k : ℕ, Continuous
      (fieldCircleAverage (lqgQ γ - 1 / ((n : ℝ) + 1)) (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k =>
      hG.ae_continuous_fieldCircleAverage _ (dyadicScale_pos k)))
  filter_upwards [hνall, hcall] with ω hνall hcall α hα μ hμ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hα)
  have hαn : α < lqgQ γ - 1 / ((n : ℝ) + 1) := by linarith
  exact origin_nonatomic_of_stronger_singularity hγ hαn (hcirc ω) μ (ν n ω)
    hμ (hνall n) (hcall n)

/-- On a single full-measure event, every subcritical LQG limit formed from
the same circle averages is non-atomic. This conclusion does not require a
jointly measurable family of limiting measures. -/
theorem ae_nonatomic_for_all_subcritical_limits
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ → ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ → ∀ z : ℂ, μ {z} = 0 := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE0 hG hγ hγ2 hQ
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [ae_origin_nonatomic_for_all_subcritical_limits P γ hγ hγ2 hC hcirc hG hE,
      hμ₀, hc0, ae_wholePlane_nonatomic_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀]
    with ω hzero hm₀ hc₀ hno α hα μ hm z
  by_cases hz : z = 0
  · simpa [hz] using hzero α hα μ hm
  · have hW : ∀ f : ℂ → ℝ, Continuous f →
        IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
          ((μ₀ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
      fun f hf => isLQGLimit_addCircleAverage hm₀ hc₀ f hf
    have hweight := restrict_compl_zero_eq_withDensity hm hW
    have heq := congrArg (fun ν : Measure ℂ => ν {z}) hweight
    rw [Measure.restrict_apply (measurableSet_singleton z),
      Measure.restrict_apply (measurableSet_singleton z)] at heq
    have hs : ({z} : Set ℂ) ∩ ({0} : Set ℂ)ᶜ = {z} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_compl_iff]
      constructor
      · exact And.left
      · intro hx
        exact ⟨hx, by simpa [hx] using hz⟩
    rw [hs] at heq
    rw [heq]
    exact (withDensity_absolutelyContinuous (μ₀ ω) _) (hno z)

/-- Whole-plane ball-mass bounds and the existence of LQG measures at zero
and at a countable sequence approaching the Seiberg bound imply non-atomicity
at every subcritical singularity. -/
theorem lqgMeasureNonatomic_of_cofinal_existence
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    LQGMeasureNonatomic P γ α hC hcirc := by
  intro hG hγ hγ2 hα μ hμ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hα)
  let β := lqgQ γ - 1 / ((n : ℝ) + 1)
  have hαβ : α < β := by dsimp [β]; linarith
  have hβ : β < lqgQ γ := by
    dsimp [β]
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  filter_upwards [ae_origin_nonatomic_of_stronger_existence P γ α β hγ hγ2 hαβ hβ
      hC hcirc (hE n) μ hG hμ,
    ae_singular_nonatomic_off_origin_of_scaledBallMass hS P γ α hγ hγ2 hα
      hC hcirc hE0 μ hG hμ] with ω h0 hoff z
  by_cases hz : z = 0
  · simpa [hz] using h0
  · exact hoff z hz

/-- The frozen Section 6 statements follow from the whole-plane mass
bounds, affine and coordinate-change laws, existence at zero, and existence at
a countable cofinal sequence of subcritical singularity strengths. -/
theorem section6_of_cofinal_existence
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (n : ℕ),
      LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    HarnackTypeEstimateStmt.{u} ∧ HarnackTypeComponentStmt.{u} ∧
    ManyGoodAnnuliStmt.{u} ∧ GoodAnnulusProbabilityStmt.{u} ∧
    AnnulusIterationStmt.{u} ∧ ManyVeryGoodAnnuliStmt.{u} ∧
    VeryGoodAnnulusProbabilityStmt.{u} ∧ AnnulusMassBoundByOdometerStmt.{u} ∧
    OdometerHarmonicMeasureBoundStmt.{u} ∧ OdometerBoundByAnnulusMassStmt.{u} ∧
    VeryGoodAnnulusHarnackTypeStmt.{u} ∧ ShellDecompositionStmt ∧
    LowMassSmallOdometerStmt.{u} := by
  have hS : WholePlaneScaledBallMassStep.{u} :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG hAff hCC wholePlaneGFFMixtureStep_holds)
  apply section6_of_literature_without_weyl hDG hAff hCC hE0
  intro Ω _ P γ α hC hcirc _
  exact lqgMeasureNonatomic_of_cofinal_existence hS P γ α hC hcirc
    (hE0 Ω P γ hC hcirc) (hE Ω P γ hC hcirc)

end HarmonicBalls.Section6
