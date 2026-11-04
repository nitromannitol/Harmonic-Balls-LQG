import HarmonicBalls.Proofs.Sec6.SingularityParameterContinuity

/-! # Continuity of bounded singular LQG masses

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Cofinal existence inputs
remain subject to operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- On every bounded measurable set, the mass of a simultaneous family of
subcritical LQG limits depends continuously on the singularity strength. -/
theorem continuousOn_mass_subcritical_limits {γ Q : ℝ} (hγ : 0 < γ)
    (hcirc : ℝ → ℂ → ℝ) (M : ℝ → Measure ℂ)
    (hM : ∀ α < Q, IsLQGLimit γ (fieldCircleAverage α hcirc) (M α))
    (hc : ∀ α < Q, ∀ n, Continuous (fieldCircleAverage α hcirc (dyadicScale n)))
    {s : Set ℂ} (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) :
    ContinuousOn (fun α => (M α s).toReal) (Iio Q) := by
  have hK : IsCompact (closure s) := hbounded.isCompact_closure
  obtain ⟨φ, hφone, _, hφc, _⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty _)
  rw [isOpen_Iio.continuousOn_iff]
  intro α hα
  have hαQ : α < Q := hα
  let β := (α + Q) / 2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβQ : β < Q := by dsimp [β]; linarith
  let ν := M β
  let : IsLocallyFiniteMeasure ν := (hM β hβQ).isLocallyFiniteMeasure
  let νs := ν.restrict s
  have hi := continuousOn_integral_weaker_singularity νs (β := β) hγ φ φ.continuous hφc
  have hic : ContinuousAt (fun a : ℝ => ∫ z, φ z ∂(νs.withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - a)))))) α :=
    (isOpen_Iio.continuousOn_iff.mp hi) hαβ
  apply hic.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hαβ] with a ha
  have haQ : a < Q := ha.trans hβQ
  have heq : M a = ν.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - a)))) :=
    (hM a haQ).unique (isLQGLimit_of_weaker_singularity hγ.le ha.le hcirc
      (hM β hβQ) (hc β hβQ))
  rw [heq]
  dsimp [νs]
  rw [← restrict_withDensity hs]
  symm
  calc
    (∫ z, φ z ∂((ν.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - a)))).restrict s)) =
        ∫ _z, (1 : ℝ) ∂((ν.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - a)))).restrict s) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hs] with z hz
          exact hφone (subset_closure hz)
    _ = _ := by simp [measureReal_def, hs]

universe u

/-- A jointly measurable subcritical family can be chosen with continuous
mass in the singularity strength for every bounded measurable set, on a
single full-measure event. -/
theorem exists_jointly_measurable_mass_continuous_subcritical_lqgMeasures
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∃ M : Ω × ℝ → Measure ℂ, Measurable M ∧
      ∀ᵐ ω ∂P, (∀ α : ℝ, α < lqgQ γ →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α))) ∧
      ∀ s : Set ℂ, MeasurableSet s → Bornology.IsBounded s →
        ContinuousOn (fun α => (M (ω, α) s).toReal) (Iio (lqgQ γ)) := by
  obtain ⟨M, hM, hlim⟩ :=
    exists_jointly_measurable_subcritical_lqgMeasures P γ hγ hγ2 hC hcirc hG hE
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
  refine ⟨hlim, ?_⟩
  intro s hs hbounded
  exact continuousOn_mass_subcritical_limits hγ (hcirc ω) (fun α => M (ω, α))
    hlim (fun α _ n => hc α n) hs hbounded

end HarmonicBalls.Section6
