import HarmonicBalls.Proofs.GFF.ContinuousCircleAffineLaw
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder

/-! # Joint law of continuous circle profiles and LQG approximations

The GFF and continuous circle-average construction used here are due to Leonardo Bonanno.
The affine map acts on the profile; no spatial covariance of measures or limit law is asserted.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Topology
namespace HarmonicBalls

/-- The spatial field profile at a positive dyadic radius. -/
def dyadicFieldProfile (α : ℝ) (F : C(CircleParameter, ℝ)) (n : ℕ) : ℂ → ℝ :=
  fun z => F (⟨dyadicScale n, dyadicScale_pos n⟩, z) -
    α * Real.log (max (dyadicScale n) ‖z‖)

/-- Every dyadic field profile is continuous. -/
theorem continuous_dyadicFieldProfile (α : ℝ) (F : C(CircleParameter, ℝ)) (n : ℕ) :
    Continuous (dyadicFieldProfile α F n) := by
  exact (F.continuous.comp (continuous_const.prodMk continuous_id)).sub
    (continuous_const.mul ((continuous_const.max continuous_norm).log
      fun z => (lt_max_of_lt_left (dyadicScale_pos n)).ne'))

/-- A measurable decoder for the whole dyadic approximation sequence. -/
def continuousCircleLQGDecoder (γ α : ℝ) : C(CircleParameter, ℝ) → ℕ → Measure ℂ :=
  fun F n => Classical.choose (exists_measurable_lqgApprox_decoder γ (dyadicScale n))
    (dyadicFieldProfile α F n)

/-- The decoder is measurable jointly as a countable sequence. -/
theorem measurable_continuousCircleLQGDecoder (γ α : ℝ) :
    Measurable (continuousCircleLQGDecoder γ α) := by
  apply Measurable.of_eval
  intro n
  apply (Classical.choose_spec (exists_measurable_lqgApprox_decoder γ (dyadicScale n))).1.comp
  apply Measurable.of_eval
  intro z
  exact ((ContinuousMap.measurable_eval ((⟨dyadicScale n, dyadicScale_pos n⟩, z) : CircleParameter)).sub
    measurable_const)

/-- For every continuous profile, decoding gives its literal approximation sequence. -/
theorem continuousCircleLQGDecoder_eq (γ α : ℝ) (F : C(CircleParameter, ℝ)) (n : ℕ) :
    continuousCircleLQGDecoder γ α F n =
      lqgApprox γ (fieldCircleAverage α (circleProfile F)) (dyadicScale n) := by
  rw [continuousCircleLQGDecoder,
    (Classical.choose_spec (exists_measurable_lqgApprox_decoder γ (dyadicScale n))).2 _
      (continuous_dyadicFieldProfile α F n)]
  unfold lqgApprox
  congr 1
  funext z
  rw [fieldCircleAverage_eq _ _ (dyadicScale_pos n)]
  simp only [dyadicFieldProfile, circleProfile, dite_eq_left (dyadicScale_pos n)]

/-- The continuous profile and its entire decoded sequence have the joint affine law. -/
theorem IsWholePlaneGFF.identDistrib_continuousCircleAffine_joint_lqgApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    (γ α : ℝ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IdentDistrib
      (fun ω => (continuousCircleAffine a b ha (F ω),
        continuousCircleLQGDecoder γ α (continuousCircleAffine a b ha (F ω))))
      (fun ω => (F ω, continuousCircleLQGDecoder γ α (F ω))) P P := by
  exact (h.identDistrib_continuousCircleAffine hF hversion ha b).comp
    (measurable_id.prodMk (measurable_continuousCircleLQGDecoder γ α))

/-- On one event the decoded sequence agrees at every index with the raw approximations. -/
theorem IsWholePlaneGFF.ae_continuousCircleLQGDecoder_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {F : Ω → C(CircleParameter, ℝ)}
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ n, continuousCircleLQGDecoder γ α (F ω) n =
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale n) := by
  filter_upwards [ae_lqgApprox_circleProfile_eq (h.ae_circle_map_eq_raw hversion)] with ω hω n
  exact (continuousCircleLQGDecoder_eq γ α (F ω) n).trans
    (hω γ α _ (dyadicScale_pos n)).symm

#print axioms continuousCircleLQGDecoder
#print axioms continuousCircleLQGDecoder_eq
#print axioms measurable_continuousCircleLQGDecoder
#print axioms IsWholePlaneGFF.identDistrib_continuousCircleAffine_joint_lqgApprox
#print axioms IsWholePlaneGFF.ae_continuousCircleLQGDecoder_eq_raw
end HarmonicBalls
