import HarmonicBalls.Proofs.Sec11.MassDiameterDyadicAsymptotic

/-! # Dyadic diameter estimates and mass-carrying classes -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

/-- Any positive dyadic exponent makes a finite multiple of the scale
smaller than a fixed positive diameter threshold at sufficiently fine scales. -/
theorem eventually_dyadic_scale_lt (s : ℝ) (hs : 0 < s)
    (C d : ℝ≥0∞) (hC : C ≠ ∞) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      C * (ENNReal.ofReal ((1 / 2 : ℝ) ^ s)) ^ n < d := by
  have hq : ENNReal.ofReal ((1 / 2 : ℝ) ^ s) < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hs
  have ht := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Or.inr hC)
  have ht' : Tendsto (fun n : ℕ => C * (ENNReal.ofReal ((1 / 2 : ℝ) ^ s)) ^ n)
      atTop (𝓝 0) := by simpa using ht
  exact (tendsto_order.1 ht').2 d hd

#print axioms eventually_dyadic_scale_lt

/-- A uniform dyadic power estimate with exponent greater than two makes
all comparison-scale tile failures simultaneously unlikely. -/
theorem IsWholePlaneGFF.tendsto_dyadic_square_diameters_of_power_error
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (d : ℝ≥0∞) (p : ℝ) (hp : 2 < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hmargin : ∀ᶠ n in atTop, a n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    Tendsto (fun n => P {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      X n i ω < d}ᶜ) atTop (𝓝 0) := by
  let p' : ℝ := (2 + p) / 2
  have hp' : 2 < p' := by dsimp [p']; linarith
  have hlt : p' < p := by dsimp [p']; linarith
  apply h.tendsto_dyadic_square_diameters_of_eventual_margin ξ X a d 1
    (ENNReal.ofReal ((1 / 2 : ℝ) ^ p')) (by simp)
    (dyadic_decay_rate_lt_quarter p' hp') hmargin
  filter_upwards [hbound, dyadic_power_error_eventually_le p p' hlt e he] with n hn he'
  intro i
  simpa only [one_mul] using (hn i).trans he'

/-- Conditional mass positivity and a dyadic power estimate select a
mass-carrying class at a deterministic scale with all tile bounds holding. -/
theorem IsWholePlaneGFF.exists_mass_class_of_dyadic_power_error
    {Ω Y : Type*} [m₀ : MeasurableSpace Ω] [MeasurableSpace Y]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (m : MeasurableSpace Ω)
    (μ : Ω → Measure Y) (S : Set Y) (C : ℕ → Fin 4 → Set Y)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (c d : ℝ≥0∞) (p : ℝ) (hp : 2 < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcover : ∀ n, S ⊆ ⋃ j, C n j)
    (hcond : ∀ᵐ ω ∂P, 0 < (P[({ω | (8 : ℝ≥0∞) * c < μ ω S}).indicator
      (fun _ => (1 : ℝ)) | m]) ω)
    (hmargin : ∀ᶠ n in atTop, a n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∃ n j, 0 < P {ω | (∀ i : Fin (2 ^ n) × Fin (2 ^ n), X n i ω < d) ∧
      (2 : ℝ≥0∞) * c < μ ω (C n j)} := by
  let : MeasurableSpace Ω := m₀
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hp0 := measure_pos_of_condExp_indicator_pos P m
    {ω | (8 : ℝ≥0∞) * c < μ ω S} hcond
  have hp0' : 0 < P {ω | ω ∈ (univ : Set Ω) ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
    simpa using hp0
  have hlim := h.tendsto_dyadic_square_diameters_of_power_error ξ X a d p hp e he hmargin hbound
  have hsmall : ∃ n, P {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n), X n i ω < d}ᶜ <
      P {ω | ω ∈ (univ : Set Ω) ∧ (8 : ℝ≥0∞) * c < μ ω S} :=
    ((tendsto_order.1 hlim).2 _ hp0').exists
  obtain ⟨n, j, hj⟩ := exists_positive_measure_scale_and_four_tile_class_of_failure_bound
    P μ univ S C (fun n => {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n), X n i ω < d})
    c hcover hsmall
  exact ⟨n, j, by simpa using hj⟩

#print axioms IsWholePlaneGFF.tendsto_dyadic_square_diameters_of_power_error
#print axioms IsWholePlaneGFF.exists_mass_class_of_dyadic_power_error
end HarmonicBalls
