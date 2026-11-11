import HarmonicBalls.Proofs.Sec11.RadialCirclePairingApproximation

/-! # Absolute test-function pairings of the pinned field

The Section 8 development uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ProbabilityTheory
namespace HarmonicBalls

/-- A normalized test pairing is determined by the field modulo constants
when the unit-circle average is pinned. The same decoder works for all
continuous shifts preserving that normalization. -/
theorem IsWholePlaneGFF.exists_global_absolute_pairing_shift_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) =
          hC ω ψ + ∫ x, g x * ψ x := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let b := radialAnnularTest 1 one_pos
  have hb (n : ℕ) : IsTestFunction univ (b n) := radialAnnularTest_isTestFunction one_pos n
  have hp := hGFF.tendstoInMeasure_circleDensity_pairing one_pos one_pos 0
  change TendstoInMeasure P (fun n ω => hC ω (b n)) atTop (fun ω => hcirc ω 1 0) at hp
  obtain ⟨s, hs, hsae⟩ := hp.exists_seq_tendsto_ae
  let φ : ℕ → ℂ → ℝ := fun n x => ψ x - b (s n) x
  have hφ (n : ℕ) : IsTestFunction univ (φ n) ∧ ∫ x, φ n x = 0 := by
    have hi : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
    have hj : Integrable (b (s n)) := (hb (s n)).1.continuous.integrable_of_hasCompactSupport (hb (s n)).2.1
    refine ⟨⟨hψ.1.sub (hb (s n)).1, hψ.2.1.sub (hb (s n)).2.1, subset_univ _⟩, ?_⟩
    change ∫ x, (ψ x - b (s n) x) = 0
    rw [integral_sub hi hj, hψint, radialAnnularTest_integral one_pos]
    exact sub_self _
  have hlin : ∀ᵐ ω ∂P, ∀ n, hC ω (φ n) = hC ω ψ - hC ω (b (s n)) := by
    apply ae_all_iff.mpr
    intro n
    have h := hGFF.ae_pairing_linear_combination hψ (hb (s n)) 1 (-1)
    filter_upwards [h] with ω hω
    simpa [φ, sub_eq_add_neg] using hω
  let f : ℕ → (LocalZeroMeanTest univ → ℝ) → ℝ :=
    fun n v => v ⟨φ n, hφ n⟩
  let F := fun v => limUnder atTop (fun n => f n v)
  have hF : Measurable F := by
    apply (StronglyMeasurable.limUnder ?_).measurable
    intro n
    exact (measurable_pi_apply (⟨φ n, hφ n⟩ : LocalZeroMeanTest univ)).stronglyMeasurable
  refine ⟨F, hF, ?_⟩
  filter_upwards [hsae, hlin, hGFF.ae_circleAverage_one_zero] with ω hω hl hp0 g hg hpin
  have hb_lim := (circleDensity_integral_tendsto_circleAverage one_pos one_pos 0 hg).comp hs.tendsto_atTop
  have hi : Integrable (fun x => g x * ψ x) :=
    (hg.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left
  have hj (n : ℕ) : Integrable (fun x => g x * b (s n) x) :=
    (hg.mul (hb (s n)).1.continuous).integrable_of_hasCompactSupport (hb (s n)).2.1.mul_left
  have ht : Tendsto (fun n => f n (localModConstPairings 0
      (fun ω => addFunPairing (hC ω) g) univ ω)) atTop
      (𝓝 (hC ω ψ + ∫ x, g x * ψ x)) := by
    have hc1 : Tendsto (fun _ : ℕ => hC ω ψ) atTop (𝓝 (hC ω ψ)) := tendsto_const_nhds
    have hc2 : Tendsto (fun _ : ℕ => ∫ x, g x * ψ x) atTop (𝓝 (∫ x, g x * ψ x)) := tendsto_const_nhds
    have hlim := (hc1.sub hω).add (hc2.sub hb_lim)
    convert hlim using 1
    · funext n
      simp only [f, localModConstPairings, fieldPairing, addFunPairing, zero_mul, sub_zero, hl]
      change hC ω ψ - hC ω (b (s n)) + ∫ x, g x * (ψ x - b (s n) x) = _
      simp_rw [mul_sub]
      rw [integral_sub hi (hj n)]
      congr 1
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      simp [b, radialAnnularTest, mul_comm]
    · simp [hp0, hpin]
  exact ht.limUnder_eq

end HarmonicBalls
