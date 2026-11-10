import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-!
# Generator-level composition for the exterior mass (fp-S11p, owner n4)

At exponent `α = 0` the pairing `fieldPairing 0 (hC ω) φ` is `hC ω φ`. For a whole-plane GFF, a pairing with a test
function `φ` supported in `O` is almost surely equal to a `comap (localModConstPairings 0 hC O)`-measurable function,
provided a sequence of unit-mass test functions `ψ_j` in `O` has `hC ω (ψ_j) → hcirc ω 1 0` almost surely. The
constant is removed by `hcirc ω 1 0 = 0` a.s. (`IsWholePlaneGFF.ae_circleAverage_one_zero`), and the reference pairing
`hC ψ_0` is recovered as the limit of the mean-zero differences `hC ψ_0 - hC ψ_k` (`IsWholePlaneGFF.ae_centeredTestPairing_eq`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology

/-- A pairing with a unit-mass reference test function is, modulo a mean-zero pairing, the reference pairing. -/
theorem ae_pairing_eq_meanZero_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {O : Set ℂ}
    {f g : ℂ → ℝ} (hf : IsTestFunction O f) (hg : IsTestFunction O g) (hgint : ∫ x, g x = 1) :
    ∃ D : Ω → ℝ, Measurable[MeasurableSpace.comap (localModConstPairings 0 hC O) inferInstance] D ∧
      ∀ᵐ ω ∂P, hC ω f = D ω + (∫ x, f x) * hC ω g := by
  have hfi : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  have hgi : Integrable g := hg.1.continuous.integrable_of_hasCompactSupport hg.2.1
  have hρt : IsTestFunction O (fun x => 1 * f x + (-(∫ y, f y)) * g x) :=
    IsTestFunction.const_mul_add_const_mul hf hg 1 (-(∫ y, f y))
  have hρint : ∫ x, (1 * f x + (-(∫ y, f y)) * g x) = 0 := by
    simp only [one_mul]
    rw [integral_add hfi (hgi.const_mul _), integral_const_mul, hgint]
    ring
  refine ⟨fun ω => localModConstPairings 0 hC O ω ⟨_, hρt, hρint⟩, ?_, ?_⟩
  · exact (measurable_pi_apply (⟨_, hρt, hρint⟩ : LocalZeroMeanTest O)).comp
      (comap_measurable (localModConstPairings 0 hC O))
  · filter_upwards [hGFF.ae_centeredTestPairing_eq hf hg] with ω hω
    unfold centeredTestPairing at hω
    simp only [localModConstPairings, fieldPairing, zero_mul, sub_zero] at hω ⊢
    rw [hω]
    ring

/-- Generator-level composition at exponent `0`: the pairing of a test function in `O` is a.s. equal to a
`comap (localModConstPairings 0 hC O)`-measurable function, given the unit-mass sequence `ψ_j` in `O` with
`hC ω (ψ_j) → hcirc ω 1 0` a.s. -/
theorem ae_pairing_exists_meanZero_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {O : Set ℂ} {ψ : ℕ → ℂ → ℝ} (hψt : ∀ j, IsTestFunction O (ψ j)) (hψint : ∀ j, ∫ x, ψ j x = 1)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω 1 0)))
    {φ : ℂ → ℝ} (hφ : IsTestFunction O φ) :
    ∃ g : Ω → ℝ, Measurable[MeasurableSpace.comap (localModConstPairings 0 hC O) inferInstance] g ∧
      ∀ᵐ ω ∂P, hC ω φ = g ω := by
  -- Mean-zero representations of `hC ψ_0 - hC ψ_k`, one for each `k`.
  have hk : ∀ k, ∃ D : Ω → ℝ,
      Measurable[MeasurableSpace.comap (localModConstPairings 0 hC O) inferInstance] D ∧
        ∀ᵐ ω ∂P, hC ω (ψ 0) = D ω + (∫ x, ψ 0 x) * hC ω (ψ k) :=
    fun k => ae_pairing_eq_meanZero_add hGFF (hψt 0) (hψt k) (hψint k)
  choose D hDm hDa using hk
  -- The limit of the mean-zero representations is the reference pairing `hC ψ_0`.
  have hGl : ∀ᵐ ω ∂P, Tendsto (fun k => D k ω) atTop (𝓝 (hC ω (ψ 0))) := by
    filter_upwards [hlim, hGFF.ae_circleAverage_one_zero, ae_all_iff.2 hDa] with ω h1 h2 h3
    have h4 : Tendsto (fun k => hC ω (ψ 0) - hC ω (ψ k)) atTop (𝓝 (hC ω (ψ 0) - hcirc ω 1 0)) :=
      tendsto_const_nhds.sub h1
    rw [h2, sub_zero] at h4
    refine h4.congr fun k => ?_
    have := h3 k
    rw [hψint 0, one_mul] at this
    linarith
  -- Represent `hC φ` through its mean-zero part and the reference pairing `hC ψ_0`, which is the limsup of `D k`.
  obtain ⟨Dφ, hDφm, hDφa⟩ := ae_pairing_eq_meanZero_add hGFF hφ (hψt 0) (hψint 0)
  refine ⟨fun ω => Dφ ω + (∫ x, φ x) * limsup (fun k => D k ω) atTop, ?_, ?_⟩
  · exact hDφm.add (measurable_const.mul (Measurable.limsup hDm))
  · filter_upwards [hDφa, hGl] with ω h1 h2
    rw [h1, h2.limsup_eq]

end HarmonicBalls
