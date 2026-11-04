import HarmonicBalls.Proofs.Sec6.WeakerSingularityCanonicalFamily
import HarmonicBalls.Proofs.Sec6.SingularWeightChangeAwayFromOrigin

/-! # Non-atomicity below an existing logarithmic singularity

The imported Section 6 annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Existence at the stronger
singularity is a staged literature input pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal

universe u

/-- A single stronger singularity removes the atom at zero simultaneously
for every existing weaker limit of the same circle averages. -/
theorem ae_weaker_limits_origin_nonatomic_of_stronger_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : LQGMeasureExistence P γ β hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, α < β → ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ → μ {0} = 0 := by
  obtain ⟨ν, hν⟩ := hE hG hγ hγ2 hβ
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Continuous (fieldCircleAverage β (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage β (dyadicScale_pos k))
  filter_upwards [hν, hc] with ω hν hc α hα μ hμ
  exact origin_nonatomic_of_stronger_singularity hγ hα (hcirc ω) μ (ν ω) hμ hν hc

/-- Under the whole-plane mass bound, every existing weaker limit is
non-atomic and has full support, simultaneously in the singularity strength.
Only existence at a single nonnegative stronger strength is assumed. -/
theorem ae_weaker_limits_nonatomic_fullSupport_of_stronger_existence
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ0 : 0 ≤ β) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : LQGMeasureExistence P γ β hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, α < β → ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      (∀ z : ℂ, μ {z} = 0) ∧
      (∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U) := by
  have hE0 := lqgMeasureExistence_of_stronger P γ 0 β hβ0 hβ hC hcirc hE
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc hG hE0
  filter_upwards [hrepr,
    ae_wholePlane_nonatomic_of_scaledBallMass hS P γ hγ hγ2 hC hcirc μ₀ hG hμ₀,
    ae_weaker_limits_origin_nonatomic_of_stronger_existence P γ β hγ hγ2 hβ hC hcirc hG hE,
    ae_fullSupport_all_singular_limits hS P γ hγ hγ2 hC hcirc hG hE0]
    with ω hrepr hno hzero hfull α hα μ hμ
  constructor
  · intro z
    by_cases hz : z = 0
    · simpa [hz] using hzero α hα μ hμ
    · have heq := congrArg (fun ν : Measure ℂ => ν {z}) (hrepr α μ hμ)
      rw [Measure.restrict_apply (measurableSet_singleton z),
        Measure.restrict_apply (measurableSet_singleton z)] at heq
      have hs : ({z} : Set ℂ) ∩ ({0} : Set ℂ)ᶜ = {z} := by
        ext x
        simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff]
        constructor
        · exact And.left
        · intro hx
          exact ⟨hx, by simpa [hx] using hz⟩
      rw [hs] at heq
      rw [heq]
      exact (withDensity_absolutelyContinuous (μ₀ ω) _) (hno z)
  · exact hfull α μ hμ

/-- Two existing limits below a nonnegative stronger singularity differ by
an explicit weight on the whole plane, and are mutually absolutely continuous. -/
theorem ae_weaker_limits_change_singularity_of_stronger_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ0 : 0 ≤ β) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : LQGMeasureExistence P γ β hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α δ : ℝ, α < β → δ < β → ∀ μ ν : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      IsLQGLimit γ (fieldCircleAverage δ (hcirc ω)) ν →
      μ = ν.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (δ - α)))) ∧
        μ ≪ ν ∧ ν ≪ μ := by
  have hE0 := lqgMeasureExistence_of_stronger P γ 0 β hβ0 hβ hC hcirc hE
  filter_upwards [ae_existing_limits_change_singularity_away_zero_of_zero_existence
      P γ hγ hγ2 hC hcirc hG hE0,
    ae_existing_limits_mutually_absolutelyContinuous_away_zero_of_zero_existence
      P γ hγ hγ2 hC hcirc hG hE0,
    ae_weaker_limits_origin_nonatomic_of_stronger_existence P γ β hγ hγ2 hβ hC hcirc hG hE]
    with ω hchange hac hzero α δ hα hδ μ ν hμ hν
  have hm : ∀ᵐ z ∂μ, z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hzero α hα μ hμ
  have hn : ∀ᵐ z ∂ν, z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hzero δ hδ ν hν
  have heq := hchange α δ μ ν hμ hν
  rw [Measure.restrict_eq_self_of_ae_mem hm, Measure.restrict_eq_self_of_ae_mem hn] at heq
  have habs := hac α δ μ ν hμ hν
  rw [Measure.restrict_eq_self_of_ae_mem hm, Measure.restrict_eq_self_of_ae_mem hn] at habs
  exact ⟨heq, habs⟩

end HarmonicBalls.Section6
