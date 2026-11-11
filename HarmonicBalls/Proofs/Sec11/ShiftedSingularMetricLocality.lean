import HarmonicBalls.Proofs.Sec11.SingularMetricConstantShift
import HarmonicBalls.Steps.Sec11.CountableCoordinateObservables
import HarmonicBalls.Steps.Sec11.ContinuousMetricVersions
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-! # Shifted singular metric locality

Locality for the field shifted by a reference pairing transfers to locality
modulo constants without samplewise linearity of pairings. The Section 8
inputs use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- A shifted-field local representative of the singular metric yields a
simultaneous modulo-constant representative of the normalized metric. The
shifted singular-metric locality hypothesis is kept explicit. -/
theorem IsWholePlaneGFF.exists_modConst_internalMetric_of_shifted_locality
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (hlocal : ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[fieldSigmaAlgebra α
        (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun u v =>
          (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => -hC ω ψ))) ξ
            (fun z => -α * Real.log ‖z‖) u v).toReal) V x y = G ω x y) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y) := by
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  have hscale := h.ae_internal_singularMetric_add_random_constant 𝔇 h𝔇 hD c hc
  have hmetric' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => Real.exp (ξ * c ω) * D ω x y) := by
    filter_upwards [hmetric] with ω hω
    exact hω.const_mul (Real.exp_pos _)
  obtain ⟨G, hG, hGeq⟩ := hlocal
  have hcount (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ V ∧ (p n).2 ∈ V) :
      ∃ H : Ω → ℕ → ℝ≥0∞,
        Measurable[Section6.fieldSigmaAlgebraModConst α hC U] H ∧
        ∀ᵐ ω ∂P, ∀ n, internalMetric
          (fun x y => Real.exp (ξ * c ω) * D ω x y) V (p n).1 (p n).2 = H ω n := by
    have hGmeas : Measurable[fieldSigmaAlgebra α
        (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U]
        (fun ω n => G ω (p n).1 (p n).2) := by
      let : MeasurableSpace Ω := fieldSigmaAlgebra α
        (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) U
      exact measurable_pi_iff.mpr (fun n => hG (p n).1 (p n).2)
    obtain ⟨H, hH, hHeq⟩ := h.exists_modConst_observable_of_reference_shift ψ hψ hψint
      (fun ω n => G ω (p n).1 (p n).2) hGmeas
    refine ⟨H, hH, ?_⟩
    filter_upwards [hscale, hGeq, hHeq] with ω hs hg hh n
    rw [internalMetric_const_mul (D ω) (Real.exp_pos _), ← hs V (p n).1 (p n).2,
      hg (p n).1 (hp n).1 (p n).2 (hp n).2]
    exact (congrFun hh n).symm
  obtain ⟨H, hH, hHeq⟩ := exists_internalMetric_version_of_countable
    (Section6.fieldSigmaAlgebraModConst α hC U) hV hne hmetric' hcount
  exact ⟨fun ω => Real.exp (ξ * c ω), H,
    Filter.Eventually.of_forall (fun _ => Real.exp_pos _), hH, hHeq⟩

/-- Shifted-field locality on nested balls gives the normalized dyadic
internal-metric locality used by the pinch-frequency argument. -/
theorem IsWholePlaneGFF.exists_modConst_dyadic_internalMetrics_of_shifted_locality
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hlocal : ∀ ε, 0 < ε → ∃ ψ : ℂ → ℝ,
      IsTestFunction (ball 0 ε) ψ ∧ (∫ x, ψ x) = 1 ∧
      ∀ V : Set ℂ, IsOpen V → V ⊆ ball 0 ε →
      ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
        (∀ x y, Measurable[fieldSigmaAlgebra α
          (fun ω => addFunPairing (hC ω) (fun _ => -hC ω ψ)) (ball 0 ε)]
            (fun ω => G ω x y)) ∧
        ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
          internalMetric (fun u v =>
            (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => -hC ω ψ))) ξ
              (fun z => -α * Real.log ‖z‖) u v).toReal) V x y = G ω x y) :
    ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y) := by
  intro ε hε
  obtain ⟨ψ, hψ, hψint, hlocalψ⟩ := hlocal ε hε
  have hlim : Tendsto (fun n : ℕ => 6 * ((2 : ℝ)⁻¹ ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨K, ?_⟩
  intro n hn
  have hr : 0 < 6 * ((2 : ℝ)⁻¹ ^ n) := by positivity
  have hsub : ball (0 : ℂ) (6 * ((2 : ℝ)⁻¹ ^ n)) ⊆ ball 0 ε :=
    ball_subset_ball (le_of_lt (hK n hn))
  exact h.exists_modConst_internalMetric_of_shifted_locality 𝔇 h𝔇 hD hmetric isOpen_ball
    ⟨0, mem_ball_self hr⟩ ψ hψ hψint (hlocalψ _ isOpen_ball hsub)



end HarmonicBalls
