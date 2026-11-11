import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11i.SingularWeyl
import HarmonicBalls.FirstPass.S11k.GreenWeight

/-!
# Outside-measurable Green potential at insertion `α`

Route for the outside version `N2` of `annulusGreenPotentialSup (μ_α) 0 3 6` in `PinchSecondExteriorEventStep`:
the singular Weyl change `μ_α = μ_0.withDensity |z|^{-γα}` (a.s., `SingularWeyl.singular_weyl_measure_ae`) and the weighted
comparison `annulusGreenPotentialSup_weylLog_le` give `S(μ_α) ≤ exp(|γα| log 6) · S(μ_0)` a.s. Only an upper bound is
needed. Hence an outside-measurable bound at insertion `0` transfers to insertion `α`.

The insertion-`0` outside bound for the buffered geometry `IsBufferedPinchGeometry` is NOT proved here: the Proofs chain
(`Proofs/Sec11/PinchGreenAnnularLocality.lean`, `PinchOutsideAnnulusMass.lean`, `PinchOutsideCircleAverage.lean`) is stated
for `IsCorrectedPinchConfiguration`, which carries the extra field `corridor_contains`. It is therefore an explicit hypothesis
`hbase` of `exists_outside_green_of_singular_weyl`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- For a buffered pinch geometry, `W̄ ⊆ 𝔸_{1,2}` (`buffer_W`), so the Green annulus `𝔸_{3,6}` lies outside `W̄`.
This is the only geometric input of the outside Green lemma at insertion `0`
(the same statement as `IsCorrectedPinchConfiguration.green_annulus_subset_outside`). -/
theorem annulus_subset_compl_closure_W_of_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ) :
    annulus 0 3 6 ⊆ (closure W)ᶜ := by
  have hW : closure W ⊆ annulus 0 1 2 := by
    have ht : closure W ⊆ thickening (10 * δ) (closure W) :=
      self_subset_thickening (by linarith [hG.delta_pos]) _
    exact ht.trans (subset_closure.trans (hG.buffer_W.trans inter_subset_right))
  intro x hx hxW
  have hx2 : dist x (0 : ℂ) < 2 := (hW hxW).1
  have hx3 : x ∈ closedBall (0 : ℂ) 3 := by
    rw [mem_closedBall]
    linarith
  exact hx.2 hx3

/-- Singular Weyl transfer of an outside Green bound. If `μ_α = μ_0.withDensity |z|^{-γα}` a.s. (the identity of
`SingularWeyl.singular_weyl_measure_ae`), then an outside-measurable bound `M · S(μ_0)` at insertion `0` yields an
outside-measurable bound `M · S(μ_α)` at insertion `α`, with constant `exp(|γα| log 6)` from
`annulusGreenPotentialSup_weylLog_le`. -/
theorem exists_outside_green_of_singular_weyl {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {m : MeasurableSpace Ω} {γ α : ℝ} {μ0 μα : Ω → Measure ℂ}
    (hW : ∀ᵐ ω ∂P, μα ω = (μ0 ω).withDensity (fun z => ENNReal.ofReal (SingularWeyl.weylFactor γ α z)))
    (hbase : ∀ M' : ℝ, 0 < M' → ∃ b : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ b ∧
      b =ᵐ[P] fun ω => ENNReal.ofReal M' * annulusGreenPotentialSup (μ0 ω) 0 3 6)
    (M : ℝ) (hM : 0 < M) :
    ∃ b : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ b ∧
      ∀ᵐ ω ∂P, ENNReal.ofReal M * annulusGreenPotentialSup (μα ω) 0 3 6 ≤ b ω := by
  obtain ⟨b, hbm, hbe⟩ := hbase (M * Real.exp (|γ * α| * Real.log 6)) (by positivity)
  refine ⟨b, hbm, ?_⟩
  filter_upwards [hW, hbe] with ω hωW hbω
  have key : annulusGreenPotentialSup
      ((μ0 ω).withDensity (fun z => ENNReal.ofReal (SingularWeyl.weylFactor γ α z))) 0 3 6 ≤
      ENNReal.ofReal (Real.exp (|γ * α| * Real.log 6)) * annulusGreenPotentialSup (μ0 ω) 0 3 6 :=
    annulusGreenPotentialSup_weylLog_le (μ0 ω) (γ * α)
  rw [hbω, hωW, ENNReal.ofReal_mul hM.le]
  calc ENNReal.ofReal M * annulusGreenPotentialSup
        ((μ0 ω).withDensity (fun z => ENNReal.ofReal (SingularWeyl.weylFactor γ α z))) 0 3 6
      ≤ ENNReal.ofReal M * (ENNReal.ofReal (Real.exp (|γ * α| * Real.log 6)) *
          annulusGreenPotentialSup (μ0 ω) 0 3 6) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = ENNReal.ofReal M * ENNReal.ofReal (Real.exp (|γ * α| * Real.log 6)) *
          annulusGreenPotentialSup (μ0 ω) 0 3 6 := (mul_assoc _ _ _).symm

end HarmonicBalls
