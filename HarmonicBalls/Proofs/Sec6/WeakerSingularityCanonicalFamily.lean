import HarmonicBalls.Proofs.Sec6.WeakerSingularityExistence
import HarmonicBalls.Proofs.Sec6.SingularMassContinuity

/-! # Existence at weaker logarithmic singularities

The imported Section 6 annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Existence at the stronger singularity is a staged literature input
pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal Topology

universe u

/-- A limit at a given strength constructs every weaker-strength limit
simultaneously, and each such limit is unique. -/
theorem exists_ae_canonical_weaker_limits_of_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : LQGMeasureExistence P γ β hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ β hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, α ≤ β →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω))
          ((μ₀ ω).withDensity fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))) ∧
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
          μ = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))) := by
  obtain ⟨μ₀, hμ₀⟩ := hE hG hγ hγ2 hβ
  have hc0 : ∀ᵐ ω ∂P, ∀ n : ℕ,
      Continuous (fieldCircleAverage β (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => hG.ae_continuous_fieldCircleAverage β (dyadicScale_pos n))
  refine ⟨μ₀, hμ₀, ?_⟩
  filter_upwards [hμ₀, hc0] with ω hμ₀ hc0 α hα
  have hm := isLQGLimit_of_weaker_singularity hγ.le hα (hcirc ω) hμ₀ hc0
  exact ⟨hm, fun _ h => h.unique hm⟩

/-- A jointly measurable family realizes all weaker-strength limits on a
single full-measure event; test integrals vary continuously below the given strength. -/
theorem exists_jointly_measurable_vaguely_continuous_weaker_limits_of_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : LQGMeasureExistence P γ β hC hcirc) :
    ∃ M : Ω × ℝ → Measure ℂ, Measurable M ∧
      ∀ᵐ ω ∂P, (∀ α : ℝ, α ≤ β →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α))) ∧
      ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
        ContinuousOn (fun α => ∫ z, φ z ∂(M (ω, α))) (Iio β) := by
  obtain ⟨μ₀, hμ₀, hcanonical⟩ :=
    exists_ae_canonical_weaker_limits_of_existence P γ β hγ hγ2 hβ hC hcirc hG hE
  have hl : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ₀ ω) := by
    filter_upwards [hμ₀] with ω hω
    exact hω.isLocallyFiniteMeasure
  let w : ℝ → ℂ → ℝ≥0∞ := fun α z =>
    if z = 0 then (if α = β then 1 else 0) else ENNReal.ofReal (Real.exp ((γ * (β - α)) * Real.log ‖z‖))
  have hw : Measurable (Function.uncurry w) := by
    apply Measurable.ite (measurableSet_singleton 0 |>.preimage measurable_snd)
      (Measurable.ite (measurableSet_singleton β |>.preimage measurable_fst) measurable_const measurable_const)
    exact ((measurable_const.mul (measurable_const.sub measurable_fst)).mul
      (Real.measurable_log.comp measurable_snd.norm)).exp.ennreal_ofReal
  obtain ⟨M, hM, hMeq⟩ := exists_jointly_measurable_weighted_modification P μ₀
    (hG.aemeasurable_lqgMeasure hμ₀) hl w hw
  refine ⟨M, hM, ?_⟩
  filter_upwards [hμ₀, hcanonical, hMeq] with ω hm₀ hcanonical hMeq
  have heq (α : ℝ) (hα : α ≤ β) : M (ω, α) = (μ₀ ω).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))) := by
    rw [hMeq α]
    by_cases hα0 : α = β
    · subst α
      congr 1
      funext z
      by_cases hz : z = 0 <;> simp [w, hz]
    have hαlt : α < β := lt_of_le_of_ne hα hα0
    congr 1
    funext z
    by_cases hz : z = 0
    · subst z
      have hp : γ * (β - α) ≠ 0 := ne_of_gt (mul_pos hγ (sub_pos.mpr hαlt))
      simp only [w, ite_eq_left rfl, ite_eq_right hα0, norm_zero, Real.zero_rpow hp, ENNReal.ofReal_zero]
    · simp only [w, ite_eq_right hz]
      rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
      congr 2
      ring
  constructor
  · intro α hα
    rw [heq α hα]
    exact (hcanonical α hα).1
  · intro φ hφ hφc
    let : IsLocallyFiniteMeasure (μ₀ ω) := hm₀.isLocallyFiniteMeasure
    have hcont := continuousOn_integral_weaker_singularity (μ₀ ω) (β := β) hγ φ hφ hφc
    apply hcont.congr
    intro α hα
    change (∫ z, φ z ∂(M (ω, α))) = _
    rw [heq α hα.le]

/-- A jointly measurable family obtained from one stronger singularity has
continuous mass on every bounded measurable set below that strength. -/
theorem exists_jointly_measurable_mass_continuous_weaker_limits_of_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : LQGMeasureExistence P γ β hC hcirc) :
    ∃ M : Ω × ℝ → Measure ℂ, Measurable M ∧
      ∀ᵐ ω ∂P, (∀ α : ℝ, α ≤ β →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α))) ∧
      (∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
        ContinuousOn (fun α => ∫ z, φ z ∂(M (ω, α))) (Iio β)) ∧
      ∀ s : Set ℂ, MeasurableSet s → Bornology.IsBounded s →
        ContinuousOn (fun α => (M (ω, α) s).toReal) (Iio β) := by
  obtain ⟨M, hM, hlim⟩ :=
    exists_jointly_measurable_vaguely_continuous_weaker_limits_of_existence
      P γ β hγ hγ2 hβ hC hcirc hG hE
  have hc : ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ n,
      Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale n)) := by
    filter_upwards [ae_all_iff.mpr (fun n => hG.ae_continuous_fieldCircleAverage 0
      (dyadicScale_pos n))] with ω hω α n
    have hbase : Continuous (hcirc ω (dyadicScale n)) := by
      simpa [fieldCircleAverage] using hω n
    have hlog : Continuous (fun z : ℂ => Real.log (max (dyadicScale n) ‖z‖)) :=
      (continuous_const.max continuous_norm).log
        (fun z => (lt_max_of_lt_left (dyadicScale_pos n)).ne')
    have hcont : Continuous (fun z : ℂ => hcirc ω (dyadicScale n) z -
        α * Real.log (max (dyadicScale n) ‖z‖)) :=
      hbase.sub (continuous_const.mul hlog)
    convert hcont using 1
    funext z
    exact fieldCircleAverage_eq α (hcirc ω) (dyadicScale_pos n) z
  refine ⟨M, hM, ?_⟩
  filter_upwards [hlim, hc] with ω hlim hc
  refine ⟨hlim.1, hlim.2, ?_⟩
  intro s hs hbounded
  exact continuousOn_mass_subcritical_limits hγ (hcirc ω) (fun α => M (ω, α))
    (fun α hα => hlim.1 α hα.le) (fun α _ n => hc α n) hs hbounded

end HarmonicBalls.Section6
