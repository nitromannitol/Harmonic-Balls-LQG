import HarmonicBalls.FirstPass.S11i.Certificate
import HarmonicBalls.FirstPass.S11i.CertMeasurable
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-!
# The certificate window implies the pinch event at every rescaled centre (fp-S11i-11-13, round 32)

Hypothesis `hcert` of `CertWindow.pinch_window_ae_of_cert` (eq. (40) of `notes/fp-gaps/CHATGPT-n3-step12-gaps.md`,
section 8): the window certificate of index `n` at a centre `w` of the rescaled model `(μk k ω, Dk k ω)` is the
deterministic event `CertificateEvent` at Euclidean radius `(2⁻¹)^n`. By `certificate_subset_pinchPointEvent`
(`Certificate.lean`, Step 4 of the corrected Lemma 11.13) it forces the pinch event at `w`. No probability is used.

The rescaled metric is `Dk k ω u v = b D ω (2^k u) (2^k v)` with `b > 0` (the scaling clause of `hscale`); it is a
Euclidean length metric when `D ω` is one (`isEuclideanLengthMetric_dilate`).
-/

namespace FirstPassS11i

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open HarmonicBalls

/-- The window certificate of index `n` at the centre `w` for the rescaled model `(μk k ω, Dk k ω)`: the event
`CertificateEvent` at Euclidean radius `(2⁻¹)^n`. -/
def windowCert {Ω : Type*} (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (μk : ℕ → Ω → Measure ℂ)
    (Dk : ℕ → Ω → ℂ → ℂ → ℝ) : ℕ → Ω → ℕ → ℂ → Prop :=
  fun k ω n w => CertificateEvent (μk k ω) (Dk k ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) w

/-- A positive constant multiple of the Euclidean length metric, pulled back by the homothety `u ↦ c u` (`c > 0`), is a
Euclidean length metric. -/
lemma isEuclideanLengthMetric_dilate {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {b c : ℝ} (hb : 0 < b)
    (hc : 0 < c) : IsEuclideanLengthMetric (fun u v => b * D ((c : ℂ) * u) ((c : ℂ) * v)) :=
  (hD.comp_homeomorph (Homeomorph.mulLeft₀ (c : ℂ) (by exact_mod_cast hc.ne'))).const_mul hb

/-- The rescaled certificate implies the pinch event at every centre, almost surely (hypothesis `hcert` of
`pinch_window_ae_of_cert`). The non-emptiness clauses are the geometric hypotheses of
`certificate_subset_pinchPointEvent`. -/
theorem hcert_of_scale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ℂ → ℂ → ℝ)
    (hDlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ)
    (hDk : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v))
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (hη : 0 < η) (h3η : 3 * η < 5)
    (hQ' : Q'.Nonempty) (hF : (frontier Q).Nonempty)
    (hK02 : (certK0 T W η ∩ certK2 V W η).Nonempty) (hK21 : (certK2 V W η ∩ certK1 V).Nonempty) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), ∀ n : ℕ,
      windowCert Ostar U V W T Q' Q η M μk Dk k ω n w →
        pinchPointEvent (μk k ω) (Dk k ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w := by
  intro k
  filter_upwards [hDlen, hDk k] with ω hω hbk
  obtain ⟨b, hb, hDkω⟩ := hbk
  have hc : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hLen : IsEuclideanLengthMetric (Dk k ω) := by
    have hfun : Dk k ω = fun u v => b * D ω (((2 : ℝ) ^ k : ℝ) * u) (((2 : ℝ) ^ k : ℝ) * v) := by
      funext u v
      exact hDkω u v
    rw [hfun]
    exact isEuclideanLengthMetric_dilate hω hb hc
  refine ae_of_all _ fun w n hcw => ?_
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hr0 : (2 : ℝ)⁻¹ ^ n ≠ 0 := hr.ne'
  -- the rescaled sets are affine images of the scale-one sets
  have hQ'r : (rescaledSet Q' ((2 : ℝ)⁻¹ ^ n) w).Nonempty := hQ'.image _
  have hFr : (frontier (rescaledSet Q ((2 : ℝ)⁻¹ ^ n) w)).Nonempty := by
    have hres : rescaledSet Q ((2 : ℝ)⁻¹ ^ n) w = affHomeo ((2 : ℝ)⁻¹ ^ n) hr0 w '' Q := by
      unfold rescaledSet
      congr 1
    rw [hres, ← Homeomorph.image_frontier]
    exact hF.image _
  exact certificate_subset_pinchPointEvent hLen (μk k ω) hη hr h3η hQ'r hFr hK02 hK21 hcw

end FirstPassS11i

#print axioms FirstPassS11i.hcert_of_scale
