import HarmonicBalls.Proofs.Sec6.JointSingularMeasureMeasurability

/-! # Vague continuity in the logarithmic singularity strength

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The cofinal existence
hypotheses below are staged literature inputs pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Integration against a positive power of distance varies continuously
with the power, for compactly supported continuous tests. -/
theorem continuousOn_integral_weaker_singularity (ν : Measure ℂ)
    [IsLocallyFiniteMeasure ν] {γ β : ℝ} (hγ : 0 < γ)
    (φ : ℂ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ContinuousOn (fun α : ℝ => ∫ z, φ z ∂(ν.withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - α)))))) (Iio β) := by
  let f : ℝ → ℂ → ℝ := fun α z => φ z * ‖z‖ ^ (γ * (β - α))
  have hf : ContinuousOn (Function.uncurry f) (Iio β ×ˢ univ) := by
    have hp : Continuous (fun p : ℝ × ℂ => γ * (β - p.1)) := by fun_prop
    have hw : ContinuousOn (fun p : ℝ × ℂ => ‖p.2‖ ^ (γ * (β - p.1)))
        (Iio β ×ˢ univ) := by
      apply (continuous_norm.comp continuous_snd).continuousOn.rpow hp.continuousOn
      intro p hp'
      exact Or.inr (mul_pos hγ (sub_pos.mpr hp'.1))
    exact (hφ.comp continuous_snd).continuousOn.mul hw
  have hs : ∀ α z, α ∈ Iio β → z ∉ tsupport φ → f α z = 0 := by
    intro α z _ hz
    simp [f, image_eq_zero_of_notMem_tsupport hz]
  have hi := continuousOn_integral_of_compact_support hφc hf hs (μ := ν)
  apply hi.congr
  intro α hα
  exact integral_withDensity_nonnegative ν _ φ
    ((Real.continuous_rpow_const (mul_nonneg hγ.le (sub_nonneg.mpr hα.le))).comp
      continuous_norm) (fun z => Real.rpow_nonneg (norm_nonneg z) _)

/-- Any simultaneous family of subcritical limits is vaguely continuous in
its singularity strength, as tested against compactly supported functions. -/
theorem continuousOn_integral_subcritical_limits {γ Q : ℝ} (hγ : 0 < γ)
    (hcirc : ℝ → ℂ → ℝ) (M : ℝ → Measure ℂ)
    (hM : ∀ α < Q, IsLQGLimit γ (fieldCircleAverage α hcirc) (M α))
    (hc : ∀ α < Q, ∀ n, Continuous (fieldCircleAverage α hcirc (dyadicScale n)))
    (φ : ℂ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ContinuousOn (fun α => ∫ z, φ z ∂(M α)) (Iio Q) := by
  rw [isOpen_Iio.continuousOn_iff]
  intro α hα
  have hαQ : α < Q := hα
  let β := (α + Q) / 2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβQ : β < Q := by dsimp [β]; linarith
  let ν := M β
  let : IsLocallyFiniteMeasure ν := (hM β hβQ).isLocallyFiniteMeasure
  have hi := continuousOn_integral_weaker_singularity ν (β := β) hγ φ hφ hφc
  have hic : ContinuousAt (fun a : ℝ => ∫ z, φ z ∂(ν.withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - a)))))) α :=
    (isOpen_Iio.continuousOn_iff.mp hi) hαβ
  apply hic.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hαβ] with a ha
  have haQ : a < Q := ha.trans hβQ
  have heq : M a = ν.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (γ * (β - a)))) :=
    (hM a haQ).unique (isLQGLimit_of_weaker_singularity hγ.le ha.le hcirc
      (hM β hβQ) (hc β hβQ))
  rw [heq]

universe u

/-- A jointly measurable family of subcritical LQG measures can be chosen
so that its compactly supported test integrals are simultaneously continuous
in the singularity parameter on a single full-measure event. -/
theorem exists_jointly_measurable_vaguely_continuous_subcritical_lqgMeasures
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) :
    ∃ M : Ω × ℝ → Measure ℂ, Measurable M ∧
      ∀ᵐ ω ∂P, (∀ α : ℝ, α < lqgQ γ →
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (M (ω, α))) ∧
      ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
        ContinuousOn (fun α => ∫ z, φ z ∂(M (ω, α))) (Iio (lqgQ γ)) := by
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
  intro φ hφ hφc
  exact continuousOn_integral_subcritical_limits hγ (hcirc ω) (fun α => M (ω, α))
    hlim (fun α _ n => hc α n) φ hφ hφc

end HarmonicBalls.Section6
