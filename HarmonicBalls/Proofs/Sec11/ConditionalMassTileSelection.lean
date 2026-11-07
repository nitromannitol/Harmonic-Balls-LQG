import HarmonicBalls.Proofs.Sec11.ConditionalAbsoluteMass
import HarmonicBalls.Proofs.Sec11.MassDiameterTileUnionBound
import HarmonicBalls.Proofs.Sec11.MassDiameterScaleSelection

/-! # Selecting tiles from conditional mass positivity

The conditional mass result uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal BigOperators
namespace HarmonicBalls

/-- Strict positivity of a conditional indicator implies that the underlying
event has positive measure, even without assuming that event is measurable. -/
theorem measure_pos_of_condExp_indicator_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (H : Set Ω)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[H.indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P H := by
  by_contra hn
  have hz : P H = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
  have hae : ∀ᵐ ω ∂P, ω ∉ H := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hz
  have hi : H.indicator (fun _ => (1 : ℝ)) =ᵐ[P] 0 := by
    filter_upwards [hae] with ω hω
    simp [hω]
  have he := condExp_congr_ae (m := m) hi
  have hfalse : ∀ᵐ ω ∂P, False := by
    filter_upwards [hcond, he] with ω hp he
    simp only [condExp_zero, Pi.zero_apply] at he
    linarith
  obtain ⟨ω, hw⟩ := hfalse.exists
  exact hw

/-- Conditional positivity of mass above `8c` and a summable tile-failure
bound give a deterministic scale and parity class with mass above `2c` and
all tile bounds holding simultaneously with positive probability. -/
theorem exists_mass_tile_class_of_conditional_mass_and_union_bound
    {Ω X : Type*} [m₀ : MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω)
    (μ : Ω → Measure X) (S : Set X) (C : ℕ → Fin 4 → Set X)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (E : ∀ n, ι n → Set Ω)
    (c : ℝ≥0∞) (hcover : ∀ n, S ⊆ ⋃ j, C n j)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω S}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hsum : Tendsto (fun n => ∑ i : ι n, P (E n i)ᶜ) atTop (𝓝 0)) :
    ∃ n j, 0 < P {ω | (∀ i : ι n, ω ∈ E n i) ∧
      (2 : ℝ≥0∞) * c < μ ω (C n j)} := by
  let : MeasurableSpace Ω := m₀
  have hp := measure_pos_of_condExp_indicator_pos P m
    {ω | (8 : ℝ≥0∞) * c < μ ω S} hcond
  have ht := tendsto_all_tiles_failure_of_sum_failure P ι E hsum
  have hp' : 0 < P {ω | ω ∈ (univ : Set Ω) ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
    simpa using hp
  have hsmall : ∃ n, P {ω | ∀ i : ι n, ω ∈ E n i}ᶜ <
      P {ω | ω ∈ (univ : Set Ω) ∧ (8 : ℝ≥0∞) * c < μ ω S} :=
    ((tendsto_order.1 ht).2 _ hp').exists
  obtain ⟨n, j, hj⟩ := exists_positive_measure_scale_and_four_tile_class_of_failure_bound
    P μ univ S C (fun n => {ω | ∀ i : ι n, ω ∈ E n i}) c hcover hsmall
  exact ⟨n, j, by simpa using hj⟩

#print axioms measure_pos_of_condExp_indicator_pos
#print axioms exists_mass_tile_class_of_conditional_mass_and_union_bound

/-- For every prescribed finite mass threshold, conditional LQG mass
positivity and the tile union bound select one positive-probability class. -/
theorem IsWholePlaneGFF.exists_mass_tile_class_of_full_support
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {ε α γ t : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (ht : 0 ≤ t) (S V O U : Set ℂ)
    (hScompact : IsCompact S) (hS : MeasurableSet S)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVS : V ⊆ S)
    (hO : IsOpen O) (hSO : S ⊆ O) (hOU : Disjoint O U)
    (hpin : sphere (0 : ℂ) 1 ⊆ U)
    (hbuffer : ∀ n z, z ∈ S → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier S) = 0)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    (C : ℕ → Fin 4 → Set ℂ) (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (E : ∀ n, ι n → Set Ω) (hcover : ∀ n, S ⊆ ⋃ j, C n j)
    (hsum : Tendsto (fun n => ∑ i : ι n, P (E n i)ᶜ) atTop (𝓝 0)) :
    ∃ n j, 0 < P {ω | (∀ i : ι n, ω ∈ E n i) ∧
      (2 : ℝ≥0∞) * ENNReal.ofReal t < μ ω (C n j)} := by
  let : MeasurableSpace Ω := m₀
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hc := h.condExp_absolute_mass_pos_of_full_support hμ hγ (show 0 ≤ 8 * t by positivity)
    S V O U hScompact hS hV hVne hVS hO hSO hOU hpin hbuffer hfront hfull
  apply exists_mass_tile_class_of_conditional_mass_and_union_bound P
    (MeasurableSpace.comap (localModConstPairings α hC U) inferInstance)
    μ S C ι E (ENNReal.ofReal t) hcover ?_ hsum
  simpa [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 by norm_num)] using hc

#print axioms IsWholePlaneGFF.exists_mass_tile_class_of_full_support
end HarmonicBalls
