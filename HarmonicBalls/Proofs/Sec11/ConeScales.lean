import HarmonicBalls.Proofs.Sec11.ConeAnnulus
import HarmonicBalls.Proofs.Sec11.PinchScales
import HarmonicBalls.Steps.Sec11.ConeNonzero

/-! # Cone-condition contradiction at infinitely many scales -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- The deterministic conclusion of Lemma 11.5 at a point. The bad scales
are assumed simultaneously for every cone; arranging that countable reduction
is a separate step. -/
theorem not_satisfiesConeCondition_of_frequently_coneMass
    (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) (C : ℝ) (hC : 0 < C) (hz : z ≠ 0)
    (hscales : ∀ Q : Set ℂ, IsCone Q → ∃ᶠ n : ℕ in atTop,
      coneMassEvent μ Q (2 * C) ((2 : ℝ)⁻¹ ^ n) z)
    (hgreen : ∀ r : ℝ, 0 < r →
      0 < annulusGreenPotentialSup μ z (3 * r) (6 * r) ∧
      annulusGreenPotentialSup μ z (3 * r) (6 * r) ≠ ⊤)
    (hbound : ∀ r : ℝ, 0 < r → (0 : ℂ) ∉ closedBall z (10 * r) →
      (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ Λ) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    ¬ SatisfiesConeCondition Λ z := by
  rintro ⟨⟨R, hR, Q, hQ, hinterior⟩, ⟨S, hS, Q', hQ', hexterior⟩⟩
  have hε : 0 < min (R / 2) (S / 5) := by positivity
  have hp : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ)⁻¹ ^ n < min (R / 2) (S / 5) := hp.eventually (Iio_mem_nhds hε)
  obtain ⟨n, ⟨hevent, ⟨hr, h0, _⟩⟩, hsmall⟩ :=
    ((hscales Q hQ).and_eventually (eventually_dyadic_balls_exclude z 0 hz (Ne.symm hz))).and_eventually hsmall |>.exists
  let r : ℝ := (2 : ℝ)⁻¹ ^ n
  have hR' : 2 * r ≤ R := by
    have := min_le_left (R / 2) (S / 5)
    dsimp [r]; linarith
  have hS' : 5 * r ≤ S := by
    have := min_le_right (R / 2) (S / 5)
    dsimp [r]; linarith
  have hgreen' := hgreen r hr
  have hfull : annulus z (4 * r) (5 * r) ⊆ Λ :=
    annulus_subset_of_coneMassEvent μ Λ Q z C r R hC hR' hinterior hgreen'.1 hgreen'.2
      (hbound r hr h0) hevent
  obtain ⟨x, hxann, hxcompl⟩ :=
    outer_annulus_inter_compl_nonempty_of_exterior_cone Q' Λ z r S hQ' hr hS' hexterior
  exact hxcompl (hfull hxann)

end HarmonicBalls
