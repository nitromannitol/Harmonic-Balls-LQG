import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Proofs.Sec8.ContinuousLocalVersions

/-!
# First pass, Lemma 11.7: jointly measurable local circle averages (task fp-S11c-11-7-redo-11-10, owner n1; B2 route,
CHATGPT-11-7-B2.md section 3.1.3; referee notes CHATGPT-11-7-B2-referee.md §1.3)

On a disk `D`, the centred-by-a-fixed-bump circle averages `z ↦ h_r(z) - (h, ρ)` of the whole-plane GFF have a version
`d(ω, z)` that is measurable for the observation σ-algebra of `D` (`Section6.fieldSigmaAlgebraModConst α₀ hC D`, the
σ-algebra of the mean-zero pairings with test functions in `D`, i.e. constants drop out). This is the measurability
input of the common local decoder `K_D` (B2 sec 3). The argument is the generic version of
`IsWholePlaneGFF.exists_joint_centered_circle_version_of_pairing_approximation` (Proofs/Sec8/ContinuousLocalVersions.lean:153),
with the centre `0` replaced by an arbitrary open disk `D` and the base point `0` replaced by a fixed bump `ρ`
(so that the base is itself a pairing with a test function in `D`, and no circle outside `D` is used).

The pointwise approximation `happrox` is an input (`LocalCircleAverageMeanZeroApproxFrozen`, Frozen/S11c.lean, not yet
approved): this file contains no GFF covariance computation.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

universe u

/-- Joint measurable version of the local circle averages of the whole-plane GFF on an open set `D` (B2 sec 3.1.3).
If each circle average `h_r(z)` (with `closedBall z r ⊆ D`), shifted by a fixed bump pairing `(h, ρ)`, is an in-probability
limit of mean-zero pairings with test functions in `D`, then there is a version `d` of `(ω, z) ↦ h_r(z) - (h, ρ)`,
jointly measurable for the observation σ-algebra of `D`, which is a.s. equal to it for all admissible `z`. -/
theorem exists_joint_local_circleAverage_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {D : Set ℂ} (hD : IsOpen D) {r : ℝ} (hr : 0 < r)
    {ρ : ℂ → ℝ}
    (happrox : ∀ z, closedBall z r ⊆ D → ∃ φ : ℕ → ℂ → ℝ,
      (∀ n, IsTestFunction D (φ n) ∧ ∫ x, φ n x = 0) ∧
      TendstoInMeasure P (fun n ω => fieldPairing α₀ (hC ω) (φ n)) atTop
        (fun ω => fieldCircleAverage α₀ (hcirc ω) r z - fieldPairing α₀ (hC ω) ρ)) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ ((Section6.fieldSigmaAlgebraModConst α₀ hC D).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ D →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z - fieldPairing α₀ (hC ω) ρ := by
  apply exists_joint_local_version_of_pointwise
    (Section6.fieldSigmaAlgebraModConst α₀ hC D) (isOpen_centers_closedBall_subset r hD)
  · filter_upwards [hGFF.ae_continuous_fieldCircleAverage α₀ hr] with ω hω
    exact hω.sub continuous_const
  · intro z hz
    obtain ⟨φ, hφ, hlim⟩ := happrox z hz
    exact exists_measurable_version_of_tendstoInMeasure _ _ _
      (fun n => measurable_fieldPairing_modConst α₀ hC _ (φ n) (hφ n)) hlim

/-- The local joint version (`exists_joint_local_circleAverage_version`) with its pointwise input taken from the pending
frozen approximation `LocalCircleAverageMeanZeroApproxFrozen` (Frozen/S11c.lean). -/
theorem local_circleAverage_version_of_frozen {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hF : LocalCircleAverageMeanZeroApproxFrozen.{u}) (hGFF : IsWholePlaneGFF P hC hcirc)
    {D : Set ℂ} (hD : IsOpen D) {r : ℝ} (hr : 0 < r) {ρ : ℂ → ℝ} (hρ : IsTestFunction D ρ) (hint : ∫ x, ρ x = 1) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ ((Section6.fieldSigmaAlgebraModConst α₀ hC D).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ D →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z - fieldPairing α₀ (hC ω) ρ :=
  exists_joint_local_circleAverage_version hGFF hD hr
    (fun z hz => hF α₀ Ω P hC hcirc hGFF D hD r hr ρ hρ hint z hz)

end HarmonicBalls.S11c
