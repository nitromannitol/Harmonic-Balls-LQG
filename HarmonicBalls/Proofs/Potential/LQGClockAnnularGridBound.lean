import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIntegrability

/-! # Annular clock increments under the product law

The product-law expectation of an annular increment agrees with its iterated
field and Brownian expectation.
-/

open MeasureTheory MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The joint nonnegative integral of the annular increment is the annealed
expectation of its field-averaged absolute value. -/
theorem lintegral_prod_annularIncrementSample_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    (∫⁻ p : Ω × ContinuousPath ℂ,
      ENNReal.ofReal |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|
      ∂(P.prod (planarBrownianMotion x))) =
      ENNReal.ofReal (∫ b, stoppedAnnularIncrement P hcirc γ α δ ε τ b
        ∂(planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, _, hFae⟩ :=
    exists_integrable_annularIncrementSample hh hγ0 hγ2 α x hε hεhalf hεδ τ hτ
  have heq : (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |F (p.2,p.1)|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae hFae] with p hp
    rw [hp p.2]
  rw [lintegral_congr_ae heq]
  have hmeas : Measurable (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |F (p.2,p.1)|) :=
    ENNReal.measurable_ofReal.comp ((hFm.comp measurable_swap).abs)
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b, ω)) P := by
    apply (integrable_stopped_annular_increment_field hh hε hεhalf hεδ γ α τ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have hinner (b : ContinuousPath ℂ) :
      (∫⁻ ω, ENNReal.ofReal |F (b,ω)| ∂P) =
        ENNReal.ofReal (stoppedAnnularIncrement P hcirc γ α δ ε τ b) := by
    simp_rw [← Real.norm_eq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal (hfield b).norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    congr 1
    unfold stoppedAnnularIncrement
    apply integral_congr_ae
    filter_upwards [hFae] with ω hω
    rw [hω b]
    rfl
  simp_rw [hinner]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_stopped_annular_inserted_increment_annealed_le hh hγ0 hγ2 α x
      (hε.trans_le hεδ) τ hτ
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact (hb ε hε hεhalf hεδ).1
  · exact Filter.Eventually.of_forall (fun b => integral_nonneg (fun ω => abs_nonneg _))

end HarmonicBalls
