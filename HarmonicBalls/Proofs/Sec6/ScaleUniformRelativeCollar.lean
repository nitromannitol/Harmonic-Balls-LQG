import HarmonicBalls.Proofs.Sec6.ScaleUniformGoodAnnulus
import HarmonicBalls.Proofs.Sec6.SingularRelativeCollar

/-! # Scale-uniform transfer from relative collar mass

The Brownian modulus depends only on the relative core margin and the
avoidance error. A relative collar-mass estimate supplies the witness bound
at each individual scale and centre.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric
open scoped ENNReal

/-- A relative collar-mass estimate and threshold slack imply good-annulus
stability uniformly over centres and scales. The relative collar estimate is
an explicit hypothesis at the given scale. -/
theorem exists_scale_uniform_goodAnnulus_of_relative_collar
    {κ : ℝ} (hκ : 0 < κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure ℂ) (r : ℝ), 0 < r → ∀ z w : ℂ,
      dist w z < δ*r → ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      0 < μ (annulus z (3*r) (5*r)) →
      μ (annulus z (3*r) (5*r)) ≠ ∞ →
      IsGoodAnnulus μ r z a b →
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      μ (annulus z (3*r-κ*r) (5*r+κ*r) \ annulus z (3*r+κ*r) (5*r-κ*r)) ≤
        d * μ (annulus z (3*r) (5*r)) →
      IsGoodAnnulus μ r w a' b' := by
  obtain ⟨δ₀, hδ₀, htransfer⟩ := exists_scale_uniform_goodAnnulus_of_collar_mass hκ hε
  let δ := min δ₀ κ
  refine ⟨δ, lt_min hδ₀ hκ, ?_⟩
  intro μ r hr z w hw a a' amid b b' d hpos hfin hg hbudget hmid hslack hcollar
  have hw₀ : dist w z < δ₀*r := hw.trans_le
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  have hwκ : dist w z < κ*r := hw.trans_le
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le)
  apply htransfer μ r hr z w hw₀ a a' b b' hfin hg hbudget
  intro Y hY hYsub hYmass
  let A := annulus z (3*r) (5*r)
  let O := annulus z (3*r-κ*r) (5*r+κ*r)
  let I := annulus z (3*r+κ*r) (5*r-κ*r)
  let C : Set ℂ := {q | r*(3+κ) ≤ dist q z ∧ dist q z ≤ r*(5-κ)}
  have hBO : annulus w (3*r) (5*r) ⊆ O := (annulus_nearby_center_sandwich hwκ).2
  have hAO : A ⊆ O := (annulus_nearby_center_sandwich
    (show dist z z < κ*r by simpa using mul_pos hκ hr)).2
  have hIC : I ⊆ C := by
    intro q hq
    simp only [I, annulus, mem_sdiff, mem_ball, mem_closedBall, not_le] at hq
    change r*(3+κ) ≤ dist q z ∧ dist q z ≤ r*(5-κ)
    constructor <;> nlinarith [hq.1, hq.2]
  have hAC : A \ C ⊆ O \ I := by
    intro q hq
    exact ⟨hAO hq.1, fun hi => hq.2 (hIC hi)⟩
  have henvelope := annulus_mass_envelope_le_of_relative_collar μ z (mul_pos hκ hr) d hcollar hslack
  have hbound : μ ((A ∩ Y) ∪ (A \ C)) ≤ ENNReal.ofReal amid * μ A := by
    calc
      _ ≤ μ (A ∩ Y) + μ (A \ C) := measure_union_le _ _
      _ ≤ μ Y + μ (O \ I) := add_le_add (measure_mono inter_subset_right) (measure_mono hAC)
      _ ≤ ENNReal.ofReal a' * μ O + μ (O \ I) :=
        add_le_add (hYmass.trans (by gcongr)) le_rfl
      _ ≤ _ := henvelope
  exact hbound.trans_lt (ENNReal.mul_lt_mul_left hpos.ne' hfin hmid)

/-- On a separated size annulus, a relative collar bound for a singularly
weighted measure implies stability for good annuli of the unweighted measure.
The weight distortion is retained in the mass-threshold condition. -/
theorem exists_scale_uniform_goodAnnulus_of_singular_relative_collar
    {κ : ℝ} (hκ : 0 < κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ ν : Measure ℂ) (r ρ e : ℝ), 0 < r → 0 < ρ →
      ∀ z w x₀ : ℂ, dist w z < δ*r → ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      0 < ν (annulus z (3*r) (5*r)) →
      ν (annulus z (3*r) (5*r)) ≠ ∞ →
      IsGoodAnnulus ν r z a b →
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) *
        (ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2) * d) ≤ ENNReal.ofReal amid →
      ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)) →
      μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ →
      annulus z (3*r) (5*r) ⊆ annulus x₀ (ρ/4) (2*ρ) →
      annulus z (3*r-κ*r) (5*r+κ*r) ⊆ annulus x₀ (ρ/4) (2*ρ) →
      μ (annulus z (3*r-κ*r) (5*r+κ*r) \ annulus z (3*r+κ*r) (5*r-κ*r)) ≤
        d * μ (annulus z (3*r) (5*r)) →
      IsGoodAnnulus ν r w a' b' := by
  obtain ⟨δ, hδ, htransfer⟩ := exists_scale_uniform_goodAnnulus_of_relative_collar hκ hε
  refine ⟨δ, hδ, ?_⟩
  intro μ ν r ρ e hr hρ z w x₀ hw a a' amid b b' d hpos hfin hg hbudget hmid
    hslack hdist hweight hA hO hcollar
  apply htransfer ν r hr z w hw a a' amid b b'
    (ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2) * d) hpos hfin hg hbudget hmid hslack
  exact (relative_mass_bounds_of_singular_weight hρ hdist hweight hA
    (sdiff_subset.trans hO)).2 hcollar

end HarmonicBalls.Section6
