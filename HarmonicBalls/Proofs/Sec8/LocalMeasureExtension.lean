import HarmonicBalls.Proofs.Sec8.RegularLocalVersions
import HarmonicBalls.Proofs.Sec8.LocalMeasureRatios
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Full-support extensions of local measure representatives -/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Adding Lebesgue measure outside an open set preserves the restriction to
that set and gives full support whenever the original measure charges its
nonempty open subsets. -/
theorem local_measure_fullSupport_extension
    (ν : Measure ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hatom : ∀ x : ℂ, ν {x} = 0) (hloc : IsLocallyFiniteMeasure ν)
    (hpos : ∀ V : Set ℂ, IsOpen V → V.Nonempty → V ⊆ U → 0 < ν V) :
    let η := ν + (volume : Measure ℂ).restrict Uᶜ
    (∀ x : ℂ, η {x} = 0) ∧ IsLocallyFiniteMeasure η ∧
      (∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < η V) ∧ η.restrict U = ν.restrict U := by
  let : IsLocallyFiniteMeasure ν := hloc
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have hv : (volume : Measure ℂ) ({x} ∩ Uᶜ) = 0 :=
      measure_mono_null inter_subset_left (measure_singleton x)
    simp [hatom x, Measure.restrict_apply (measurableSet_singleton x), hv]
  · refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩⟩
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_ball_lt_top,
      lt_of_le_of_lt (Measure.restrict_apply_le _ _) measure_ball_lt_top⟩
  · intro V hV hne
    by_cases h : (V ∩ U).Nonempty
    · have hp := hpos (V ∩ U) (hV.inter hU) h inter_subset_right
      rw [Measure.add_apply]
      exact lt_of_lt_of_le hp (le_trans (measure_mono inter_subset_left) (le_add_right le_rfl))
    · have hsub : V ⊆ Uᶜ := by
        intro x hx hxU
        exact h ⟨x, hx, hxU⟩
      have hp : 0 < (volume : Measure ℂ) V := hV.measure_pos volume hne
      have hv : ((volume : Measure ℂ).restrict Uᶜ) V = volume V := by
        rw [Measure.restrict_apply hV.measurableSet, inter_eq_left.mpr hsub]
      rw [Measure.add_apply, hv]
      exact lt_of_lt_of_le hp (le_add_left le_rfl)
  · rw [Measure.restrict_add, Measure.restrict_restrict hU.measurableSet]
    simp

open Classical MarkovProcess in
/-- Locally proportional atomless, locally finite representatives yield the
local indicator versions whenever the original measures have full support. -/
theorem ae_local_veryGoodComparable_indicators_of_local_finite_measures
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (βminus : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      (∀ᵐ ω ∂P, (∀ x : ℂ, ν ω {x} = 0) ∧ IsLocallyFiniteMeasure (ν ω)) ∧
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        (μ ω).restrict (ball 0 ε) = c • (ν ω).restrict (ball 0 ε)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  apply ae_local_veryGoodComparable_indicators_of_regular_local_measures P germ μ βminus N₀
    a b C₁m C₁p C₂m C₂p C₃ m ha hpolar
  intro ε hε
  obtain ⟨ν, hν, hreg, heq⟩ := hrep ε hε
  let η : Ω → Measure ℂ := fun ω => ν ω + (volume : Measure ℂ).restrict (ball 0 ε)ᶜ
  have hη : @Measurable Ω (Measure ℂ) (germ ε) _ η := by
    let : MeasurableSpace Ω := germ ε
    exact hν.add measurable_const
  refine ⟨η, hη, ?_, ?_⟩
  · filter_upwards [hfull, hreg, heq] with ω hfullω hregω ⟨c, hc, hct, heqω⟩
    have hpos : ∀ V : Set ℂ, IsOpen V → V.Nonempty → V ⊆ ball 0 ε → 0 < ν ω V := by
      intro V hV hVne hVU
      have hμpos := hfullω V hV hVne
      have he : μ ω V = c * ν ω V := by
        have he' := congrArg (fun ξ : Measure ℂ => ξ V) heqω
        simpa only [Measure.restrict_apply hV.measurableSet, inter_eq_left.mpr hVU,
          Measure.smul_apply, smul_eq_mul] using he'
      by_contra hh
      have hz : ν ω V = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hh)
      rw [he, hz, mul_zero] at hμpos
      exact (lt_irrefl _ hμpos)
    obtain ⟨hatom, hloc, hfull, _⟩ := local_measure_fullSupport_extension
      (ν ω) (ball 0 ε) isOpen_ball hregω.1 hregω.2 hpos
    exact ⟨hatom, hloc, hfull⟩
  · filter_upwards [hreg, heq] with ω hregω ⟨c, hc, hct, heqω⟩
    refine ⟨c, hc, hct, ?_⟩
    have hηeq : (η ω).restrict (ball 0 ε) = (ν ω).restrict (ball 0 ε) := by
      simp [η, Measure.restrict_add, Measure.restrict_restrict isOpen_ball.measurableSet]
    rw [hηeq]
    exact heqω

open Classical MarkovProcess in
/-- Germ-measurable normalized masses give local joint-indicator versions for
atomless, locally finite full-support measures. -/
theorem ae_local_veryGoodComparable_indicators_of_mass_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (βminus : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hratio : ∀ ε, 0 < ε → ∀ V : Set ℂ, IsOpen V →
      @Measurable Ω ℝ≥0∞ (germ ε) _
        (fun ω => μ ω (V ∩ ball 0 ε) / μ ω (ball 0 ε))) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  apply ae_local_veryGoodComparable_indicators_of_local_finite_measures P germ μ βminus N₀
    a b C₁m C₁p C₂m C₂p C₃ m ha hpolar hfull
  intro ε hε
  refine ⟨fun ω => normalizedRestriction (μ ω) (ball 0 ε), ?_, ?_, ?_⟩
  · exact @measurable_normalizedRestriction Ω (germ ε) μ (ball 0 ε) (hratio ε hε)
  · filter_upwards [hatom] with ω hω
    refine ⟨?_, inferInstance⟩
    intro x
    have hz : μ ω ({x} ∩ ball 0 ε) = 0 := measure_mono_null inter_subset_left (hω x)
    simp [normalizedRestriction, Measure.smul_apply,
      Measure.restrict_apply (measurableSet_singleton x), hz]
  · filter_upwards [ae_referenceBall_pos_finite P μ hfull hloc] with ω hω
    exact ⟨μ ω (ball 0 ε), (hω ε hε).1, (hω ε hε).2,
      restrict_eq_smul_normalizedRestriction (μ ω) isOpen_ball.measurableSet
        (hω ε hε).1 (hω ε hε).2⟩

end HarmonicBalls
