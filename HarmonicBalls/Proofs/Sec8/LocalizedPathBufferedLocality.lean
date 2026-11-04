import HarmonicBalls.Proofs.Sec8.LocalizedNormalizedMeasurePath

/-! # Buffered locality for normalized dyadic paths

The imported Section 8 ergodic development uses Leonardo Bonanno's
LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- Normalizing a restriction to a smaller measurable set ignores a preceding
restriction to a larger set. -/
theorem normalizedRestriction_restrict_of_subset (μ : Measure ℂ) {U V : Set ℂ}
    (hU : MeasurableSet U) (hUV : U ⊆ V) :
    normalizedRestriction (μ.restrict V) U = normalizedRestriction μ U := by
  unfold normalizedRestriction
  rw [Measure.restrict_apply hU, inter_eq_left.mpr hUV,
    Measure.restrict_restrict_of_subset hUV]

/-- A normalized restriction to a smaller set is unchanged by first
normalizing on a larger set of positive finite mass. -/
theorem normalizedRestriction_normalizedRestriction_of_subset (μ : Measure ℂ)
    {U V : Set ℂ} (hU : MeasurableSet U) (hUV : U ⊆ V)
    (hzero : μ V ≠ 0) (htop : μ V ≠ ∞) :
    normalizedRestriction (normalizedRestriction μ V) U = normalizedRestriction μ U := by
  change normalizedRestriction ((μ V)⁻¹ • μ.restrict V) U = normalizedRestriction μ U
  rw [normalizedRestriction_smul _ _ (ENNReal.inv_ne_zero.mpr htop)
    (ENNReal.inv_ne_top.mpr hzero), normalizedRestriction_restrict_of_subset μ hU hUV]

/-- Local versions on arbitrarily small reference balls, measurable in the
larger prescribed neighborhood, give local versions of the dyadic tail. -/
theorem ae_local_localizedDyadicMeasure_of_buffered_versions
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (R : ℝ) (hR : 0 < R)
    (hpositive : ∀ᵐ ω ∂P, ∀ r, 0 < r → μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞)
    (hrep : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → Measure ℂ,
      (∀ n, K ≤ n → @Measurable Ω (Measure ℂ) (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω => localizedDyadicMeasure (ball 0 R) (μ ω) n) =ᵐ[P] Y n) := by
  intro ε hε
  obtain ⟨r, hr, ν, hνm, hνeq⟩ := hrep ε hε
  obtain ⟨K, hK⟩ := dyadicScale_germ_cofinal.2 (r / R) (div_pos hr.1 hR)
  refine ⟨K, (fun n ω => (normalizedRestriction (ν ω) (ball 0 (dyadicScale n * R))).map
    (fun z : ℂ => (dyadicScale n)⁻¹ • z)), ?_, ?_⟩
  · intro n _
    let : MeasurableSpace Ω := germ ε
    exact (Measure.measurable_map _ (by fun_prop)).comp
      ((measurable_normalizedRestriction_measure _ isOpen_ball.measurableSet).comp hνm)
  · intro n hn
    have hle : dyadicScale n * R ≤ r := by
      apply (le_div_iff₀ hR).1
      exact (dyadicScale_germ_cofinal.1 hn).trans hK
    filter_upwards [hνeq, hpositive] with ω hω hpos
    rw [localizedDyadicMeasure_ball, hω,
      normalizedRestriction_normalizedRestriction_of_subset _ isOpen_ball.measurableSet
        (ball_subset_ball hle) (hpos r hr.1).1 (hpos r hr.1).2]

universe u

/-- Buffered local normalized-restriction versions imply ergodicity of the
stationary LQG path. -/
theorem IsWholePlaneGFF.ergodic_localizedDyadicMeasure_shift_of_buffered_versions
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμm : Measurable μ) (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc) (R : ℝ) (hR : 0 < R)
    (hpositive : ∀ᵐ ω ∂P, ∀ r, 0 < r → μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞)
    (hrep : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r)) :
    Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let germ := fun r => Section6.fieldSigmaAlgebraModConst α hC (ball 0 r)
  have hXm : ∀ n, Measurable (fun ω => localizedDyadicMeasure (ball 0 R) (μ ω) n) := by
    intro n
    exact (measurable_pi_apply n).comp
      ((measurable_localizedDyadicMeasure _ isOpen_ball.measurableSet).comp hμm)
  have hstat : P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) (n + 1)) =
      P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n) :=
    (hGFF.identDistrib_localizedDyadicMeasure_shift hγ hγ2 hα hμ hAff hCC _
      isOpen_ball.measurableSet).map_eq.symm
  exact ergodic_shift_of_stationary_ae_local_germ P germ dyadicScale dyadicScale_pos
    dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α hC 0) _ hXm hstat
    (ae_local_localizedDyadicMeasure_of_buffered_versions P germ μ R hR hpositive hrep)
    (hGFF.origin_germ_trivial α)

/-- The same conclusion holds for the LQG measure without assuming an
exactly measurable representative of the random measure. -/
theorem IsWholePlaneGFF.ergodic_localizedDyadicMeasure_shift_of_ae_buffered_versions
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc) (R : ℝ) (hR : 0 < R)
    (hpositive : ∀ᵐ ω ∂P, ∀ r, 0 < r → μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞)
    (hrep : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r)) :
    Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n)) := by
  let hμa := hGFF.aemeasurable_lqgMeasure hμ
  let μ' := hμa.mk μ
  have heq : μ =ᵐ[P] μ' := hμa.ae_eq_mk
  have hμ' : IsLQGMeasureOfField P γ α hcirc μ' := by
    filter_upwards [hμ, heq] with ω hω he
    simpa only [← he] using hω
  have hp' : ∀ᵐ ω ∂P, ∀ r, 0 < r → μ' ω (ball 0 r) ≠ 0 ∧ μ' ω (ball 0 r) ≠ ∞ := by
    filter_upwards [hpositive, heq] with ω hω he
    simpa only [← he] using hω
  have hr' : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ' ω) (ball 0 r) := by
    intro ε hε
    obtain ⟨r, hr, ν, hν, hνeq⟩ := hrep ε hε
    refine ⟨r, hr, ν, hν, ?_⟩
    filter_upwards [hνeq, heq] with ω hω he
    simpa only [← he] using hω
  have he' : (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n) =ᵐ[P]
      (fun ω n => localizedDyadicMeasure (ball 0 R) (μ' ω) n) := by
    filter_upwards [heq] with ω he
    simp only [he]
  rw [Measure.map_congr he']
  exact hGFF.ergodic_localizedDyadicMeasure_shift_of_buffered_versions hγ hγ2 hα
    hμ' hμa.measurable_mk hAff hCC R hR hp' hr'

/-- Full support and local finiteness supply the positive finite ball masses
needed for buffered local versions. -/
theorem IsWholePlaneGFF.ergodic_localizedDyadicMeasure_shift_of_fullSupport
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc) (R : ℝ) (hR : 0 < R)
    (hrep : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r)) :
    Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n)) := by
  have hp := ae_referenceBall_pos_finite P μ
    (hfull γ α hγ hγ2 hα Ω P hC hcirc μ hGFF hμ)
    (hμ.mono (fun _ h => h.isLocallyFiniteMeasure))
  exact hGFF.ergodic_localizedDyadicMeasure_shift_of_ae_buffered_versions
    hγ hγ2 hα hμ hAff hCC R hR hp hrep

end HarmonicBalls
