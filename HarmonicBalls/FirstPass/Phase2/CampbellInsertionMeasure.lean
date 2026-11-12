import HarmonicBalls.FirstPass.Phase2.CampbellInsertion

/-!
# The LQG measure with a logarithmic insertion, as a measure away from the insertion point

If `μ₀` is the vague limit of the regularized measures of `h` and `μ` that of the field `h - α₀ log |·|`, then on every
bounded open set `W` not containing the origin, `μ = |z|^{-γα₀} μ₀` as measures
(`IsLQGLimit.restrict_fieldCircleAverage_eq`). The identity `∫ f dμ = ∫ f(z) |z|^{-γα₀} dμ₀(z)` for continuous compactly
supported `f` vanishing near `0` (`IsLQGLimit.integral_fieldCircleAverage_eq`) passes to indicators of open subsets of `W`
by monotone convergence along continuous cutoffs (`IsLQGLimit.measure_open_fieldCircleAverage_eq`), and open sets form a
generating π-system of the Borel σ-algebra.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- **Open sets away from the insertion point.** If `μ₀` is the vague limit of the regularized measures of `h` and `μ`
that of the field with insertion `α₀`, then `μ V = ∫_V |z|^{-γα₀} dμ₀(z)` for every bounded open `V` not containing `0`. -/
theorem IsLQGLimit.measure_open_fieldCircleAverage_eq {γ α₀ : ℝ} {h : ℝ → ℂ → ℝ} {μ₀ μ : Measure ℂ}
    (hm : ∀ k : ℕ, Measurable (h (dyadicScale k))) (hL0 : IsLQGLimit γ h μ₀)
    (hL : IsLQGLimit γ (fieldCircleAverage α₀ h) μ) {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (h0 : (0 : ℂ) ∉ V) :
    μ V = μ₀.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α₀)))) V := by
  have := hL.isLocallyFiniteMeasure
  have := hL0.isLocallyFiniteMeasure
  obtain ⟨F, hFc, hF0, -, hFm, hFsup, hFs⟩ := CampbellKernel.exists_cutoff_iSup_eq_indicator hV
  have hqm : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (-(γ * α₀))) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  have hcs : ∀ j, HasCompactSupport (F j) := fun j =>
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) (hVb.subset (hFs j))
  have h0j : ∀ j, (0 : ℂ) ∉ tsupport (F j) := fun j hj => h0 (hFs j hj)
  have hFmeas : ∀ j, Measurable fun z => ENNReal.ofReal (F j z) := fun j =>
    ENNReal.measurable_ofReal.comp (hFc j).measurable
  have hmono : Monotone fun j z => ENNReal.ofReal (F j z) := fun i j hij z =>
    ENNReal.ofReal_le_ofReal (hFm z hij)
  have hprodm : ∀ j, Measurable fun z => ENNReal.ofReal (F j z) * ENNReal.ofReal (‖z‖ ^ (-(γ * α₀))) :=
    fun j => (hFmeas j).mul hqm
  have hmono' : Monotone fun j z => ENNReal.ofReal (F j z) * ENNReal.ofReal (‖z‖ ^ (-(γ * α₀))) :=
    fun i j hij z => by
      dsimp only
      gcongr
      exact hFm z hij
  have hterm : ∀ j, ∫⁻ z, ENNReal.ofReal (F j z) ∂μ =
      ∫⁻ z, ENNReal.ofReal (F j z) * ENNReal.ofReal (‖z‖ ^ (-(γ * α₀))) ∂μ₀ := by
    intro j
    have hg := continuous_mul_norm_rpow_of_zero_notMem (hFc j) (h0j j) (-(γ * α₀))
    calc ∫⁻ z, ENNReal.ofReal (F j z) ∂μ = ENNReal.ofReal (∫ z, F j z ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal ((hFc j).integrable_of_hasCompactSupport (hcs j))
            (Eventually.of_forall fun z => hF0 j z)).symm
      _ = ENNReal.ofReal (∫ z, F j z * ‖z‖ ^ (-(γ * α₀)) ∂μ₀) := by
          rw [IsLQGLimit.integral_fieldCircleAverage_eq hm hL0 hL (hFc j) (hcs j) (h0j j)]
      _ = ∫⁻ z, ENNReal.ofReal (F j z * ‖z‖ ^ (-(γ * α₀))) ∂μ₀ :=
          ofReal_integral_eq_lintegral_ofReal (hg.integrable_of_hasCompactSupport (hcs j).mul_right)
            (Eventually.of_forall fun z => mul_nonneg (hF0 j z) (by positivity))
      _ = ∫⁻ z, ENNReal.ofReal (F j z) * ENNReal.ofReal (‖z‖ ^ (-(γ * α₀))) ∂μ₀ :=
          lintegral_congr fun z => ENNReal.ofReal_mul (hF0 j z)
  have hL1 : μ V = ⨆ j, ∫⁻ z, ENNReal.ofReal (F j z) ∂μ := by
    rw [← lintegral_iSup hFmeas hmono, ← lintegral_indicator_one hV.measurableSet]
    exact lintegral_congr fun z => (hFsup z).symm
  have hR1 : μ₀.withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α₀)))) V =
      ⨆ j, ∫⁻ z, ENNReal.ofReal (F j z) * ENNReal.ofReal (‖z‖ ^ (-(γ * α₀))) ∂μ₀ := by
    rw [withDensity_apply _ hV.measurableSet, ← lintegral_indicator hV.measurableSet,
      ← lintegral_iSup hprodm hmono']
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.iSup_mul, hFsup z]
    by_cases hz : z ∈ V <;> simp [hz]
  rw [hL1, hR1]
  exact iSup_congr hterm

/-- **The inserted LQG measure away from the insertion point (L9c).** If `μ₀` is the vague limit of the regularized
measures of `h` and `μ` that of the field `h - α₀ log |·|`, then on every bounded open set `W` not containing `0`,
`μ = |z|^{-γα₀} μ₀`: `μ.restrict W = (μ₀.withDensity |·|^{-γα₀}).restrict W`. The dyadic slices `h (2^{-k})` are
assumed measurable. -/
theorem IsLQGLimit.restrict_fieldCircleAverage_eq {γ α₀ : ℝ} {h : ℝ → ℂ → ℝ} {μ₀ μ : Measure ℂ}
    (hm : ∀ k : ℕ, Measurable (h (dyadicScale k))) (hL0 : IsLQGLimit γ h μ₀)
    (hL : IsLQGLimit γ (fieldCircleAverage α₀ h) μ) {W : Set ℂ} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (h0 : (0 : ℂ) ∉ W) :
    μ.restrict W = (μ₀.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α₀)))).restrict W := by
  have := hL.isLocallyFiniteMeasure
  have hfin : μ W < ∞ := (measure_mono subset_closure).trans_lt hWb.isCompact_closure.measure_lt_top
  have : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.2 hfin.ne
  have hopen : ∀ s : Set ℂ, IsOpen s → μ.restrict W s =
      (μ₀.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α₀)))).restrict W s := by
    intro s hs
    rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
    exact IsLQGLimit.measure_open_fieldCircleAverage_eq hm hL0 hL (hs.inter hW) (hWb.subset inter_subset_right)
      fun h => h0 h.2
  exact ext_of_generate_finite {s : Set ℂ | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
    (fun s hs => hopen s hs) (hopen univ isOpen_univ)

end HarmonicBalls
