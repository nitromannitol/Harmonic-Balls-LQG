import HarmonicBalls.Proofs.Sec11.CircleDensityPairingConvergence
import HarmonicBalls.Proofs.Sec11.AbsoluteCircleDecoderReduction
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-! # Radial circle-average differences from zero-integral tests

The Section 8 development uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ProbabilityTheory
namespace HarmonicBalls

/-- A normalized annular test centered at the origin. -/
def radialAnnularTest (r : ℝ) (hr : 0 < r) (n : ℕ) (x : ℂ) : ℝ :=
  (∫ y, circleDensity r (circleDensityWidth r 1 n)
    (circleDensityWidth_pos hr one_pos n) 0 y)⁻¹ *
    circleDensity r (circleDensityWidth r 1 n) (circleDensityWidth_pos hr one_pos n) 0 x

theorem radialAnnularTest_isTestFunction {r : ℝ} (hr : 0 < r) (n : ℕ) :
    IsTestFunction univ (radialAnnularTest r hr n) := by
  refine ⟨contDiff_const.mul (circleDensity_contDiff _ _ _ _), ?_, subset_univ _⟩
  exact (circleDensity_hasCompactSupport hr.le (circleDensityWidth_pos hr one_pos n) 0).mul_left

theorem radialAnnularTest_integral {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∫ x, radialAnnularTest r hr n x = 1 :=
  circleDensity_normalized_integral hr.le (circleDensityWidth_pos hr one_pos n) 0

/-- A common subsequence of zero-integral annular tests approximates a pinned
radial circle average and gives the correct limit against continuous shifts. -/
theorem IsWholePlaneGFF.exists_radial_zeroMean_test_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∃ ψ : ℕ → ℂ → ℝ,
      (∀ n, IsTestFunction univ (ψ n) ∧ ∫ x, ψ n x = 0) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => hC ω (ψ n)) atTop (𝓝 (hcirc ω r 0))) ∧
      ∀ g : ℂ → ℝ, Continuous g →
        Tendsto (fun n => ∫ x, g x * ψ n x) atTop
          (𝓝 (Real.circleAverage g 0 r - Real.circleAverage g 0 1)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let a := radialAnnularTest r hr
  let b := radialAnnularTest 1 one_pos
  have ha (n : ℕ) : IsTestFunction univ (a n) := radialAnnularTest_isTestFunction hr n
  have hb (n : ℕ) : IsTestFunction univ (b n) := radialAnnularTest_isTestFunction one_pos n
  have hp := hGFF.tendstoInMeasure_circleDensity_pairing hr one_pos 0
  change TendstoInMeasure P (fun n ω => hC ω (a n)) atTop (fun ω => hcirc ω r 0) at hp
  obtain ⟨s, hs, hsae⟩ := hp.exists_seq_tendsto_ae
  have hq := hGFF.tendstoInMeasure_circleDensity_pairing one_pos one_pos 0
  change TendstoInMeasure P (fun n ω => hC ω (b n)) atTop (fun ω => hcirc ω 1 0) at hq
  obtain ⟨t, ht, htae⟩ := (hq.comp hs.tendsto_atTop).exists_seq_tendsto_ae
  let k := s ∘ t
  let ψ : ℕ → ℂ → ℝ := fun n x => a (k n) x - b (k n) x
  have hlin : ∀ᵐ ω ∂P, ∀ n, hC ω (ψ n) = hC ω (a (k n)) - hC ω (b (k n)) := by
    apply ae_all_iff.mpr
    intro n
    have h := hGFF.ae_pairing_linear_combination (ha (k n)) (hb (k n)) 1 (-1)
    filter_upwards [h] with ω hω
    simpa [ψ, sub_eq_add_neg] using hω
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro n
    have hia : Integrable (a (k n)) :=
      (ha (k n)).1.continuous.integrable_of_hasCompactSupport (ha (k n)).2.1
    have hib : Integrable (b (k n)) :=
      (hb (k n)).1.continuous.integrable_of_hasCompactSupport (hb (k n)).2.1
    refine ⟨⟨(ha (k n)).1.sub (hb (k n)).1,
      (ha (k n)).2.1.sub (hb (k n)).2.1, subset_univ _⟩, ?_⟩
    change ∫ x, (a (k n) x - b (k n) x) = 0
    rw [integral_sub hia hib, radialAnnularTest_integral hr, radialAnnularTest_integral one_pos]
    exact sub_self _
  · filter_upwards [hsae, htae, hlin, hGFF.ae_circleAverage_one_zero] with ω hω hω' hl hp0
    have hlim := (hω.comp ht.tendsto_atTop).sub hω'
    simpa [k, Function.comp_def, hl, hp0] using hlim
  · intro g hg
    have h1 := circleDensity_integral_tendsto_circleAverage hr one_pos 0 hg
    have h2 := circleDensity_integral_tendsto_circleAverage one_pos one_pos 0 hg
    have h := (h1.sub h2).comp (hs.tendsto_atTop.comp ht.tendsto_atTop)
    apply h.congr'
    filter_upwards with n
    have hi (f : ℂ → ℝ) (hf : IsTestFunction univ f) : Integrable (fun x => f x * g x) :=
      (hf.1.continuous.mul hg).integrable_of_hasCompactSupport hf.2.1.mul_right
    dsimp [ψ, k, a, b, radialAnnularTest]
    simp_rw [mul_sub, mul_comm (g _)]
    exact (integral_sub (hi _ (ha (k n))) (hi _ (hb (k n)))).symm


/-- The pinned radial circle average is a measurable function of the
whole-plane field modulo constants, consistently under all continuous shifts
preserving its unit-circle normalization. -/
theorem IsWholePlaneGFF.exists_global_radial_circle_shift_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) :
    ∃ F : (LocalZeroMeanTest univ → ℝ) → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → Real.circleAverage g 0 1 = 0 →
        F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω) =
          fieldCircleAverage α (hcirc ω) r 0 + Real.circleAverage g 0 r := by
  obtain ⟨ψ, hψ, hae, hdet⟩ := hGFF.exists_radial_zeroMean_test_approximation hr
  let φ : ℕ → LocalZeroMeanTest univ := fun n => ⟨ψ n, hψ n⟩
  let c := α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) 0 r
  let f : ℕ → (LocalZeroMeanTest univ → ℝ) → ℝ := fun n v =>
    v (φ n) + α * (∫ x, ψ n x * Real.log ‖x‖) - c
  let F := fun v => limUnder atTop (fun n => f n v)
  have hF : Measurable F := by
    apply (StronglyMeasurable.limUnder ?_).measurable
    intro n
    exact (((measurable_pi_apply (φ n)).add_const _).sub_const _).stronglyMeasurable
  refine ⟨F, hF, ?_⟩
  filter_upwards [hae] with ω hω g hg hpin
  have hlim := (hω.add (hdet g hg)).sub_const c
  have ht : Tendsto (fun n => f n (localModConstPairings α
      (fun ω => addFunPairing (hC ω) g) univ ω)) atTop
      (𝓝 (fieldCircleAverage α (hcirc ω) r 0 + Real.circleAverage g 0 r)) := by
    convert hlim using 1
    · funext n
      simp only [f, localModConstPairings, fieldPairing, addFunPairing, φ]
      ring
    · simp only [fieldCircleAverage, c, hpin, sub_zero]
      ring
  exact ht.limUnder_eq


/-- The global modulo-constant field jointly decodes absolute circle averages
at countably many radii and all centers buffered in a fixed ball, on one event
valid for every continuous shift preserving the pinning. -/
theorem IsWholePlaneGFF.exists_global_joint_absolute_circle_shift_decoders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ε α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∃ D : ℕ → (LocalZeroMeanTest univ → ℝ) → ℂ → ℝ,
      (∀ n, Measurable (Function.uncurry (D n))) ∧
      ∀ᵐ ω ∂P, ∀ n (g : ℂ → ℝ), Continuous g → Real.circleAverage g 0 1 = 0 → ∀ z,
        closedBall z (r n) ⊆ ball 0 ε →
        D n (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω) z =
          fieldCircleAverage α (hcirc ω) (r n) z + Real.circleAverage g z (r n) := by
  choose C hCm hCe using fun n =>
    hGFF.exists_joint_local_singular_circle_shift_decoder (α := α) (ε := ε) (hr n)
  choose R hRm hRe using fun n =>
    hGFF.exists_global_radial_circle_shift_decoder (α := α) (hr n)
  let W : (LocalZeroMeanTest univ → ℝ) → LocalZeroMeanTest (ball 0 ε) → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩
  have hW : Measurable W := measurable_pi_iff.mpr fun φ => measurable_pi_apply _
  refine ⟨fun n v z => C n (W v) z + R n v, ?_, ?_⟩
  · intro n
    have hm : Measurable (fun p : (LocalZeroMeanTest univ → ℝ) × ℂ => (W p.1, p.2)) :=
      (hW.comp measurable_fst).prodMk measurable_snd
    exact ((hCm n).comp hm).add ((hRm n).comp measurable_fst)
  · filter_upwards [ae_all_iff.mpr hCe, ae_all_iff.mpr hRe] with ω hCω hRω n g hg hpin z hz
    have heq : W (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ ω) =
        localModConstPairings α (fun ω => addFunPairing (hC ω) g) (ball 0 ε) ω := rfl
    rw [heq, hCω n g hg z hz, hRω n g hg hpin]
    ring

end HarmonicBalls
