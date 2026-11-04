import HarmonicBalls.Proofs.Sec11.ConeScales

/-! # Finiteness of the Green potential at cone-mass scales -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Local finiteness and a positive cone-mass event imply that the Green
potential supremum is finite at that scale. -/
theorem annulusGreenPotentialSup_ne_top_of_coneMassEvent
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hM : 0 < M) (hevent : coneMassEvent μ Q M r z) :
    annulusGreenPotentialSup μ z (3 * r) (6 * r) ≠ ⊤ := by
  have hmeasure : μ (annulus z r (2 * r) ∩ coneAt Q z) ≠ ⊤ := by
    have hsub : annulus z r (2 * r) ∩ coneAt Q z ⊆ closedBall z (2 * r) := by
      intro x hx
      exact ball_subset_closedBall hx.1.1
    exact ne_top_of_le_ne_top (IsCompact.measure_lt_top (μ := μ) (isCompact_closedBall z (2 * r) :
      IsCompact (closedBall z (2 * r)))).ne (measure_mono hsub)
  have hprod : ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r) ≠ ⊤ :=
    ne_top_of_le_ne_top hmeasure hevent
  have hcoeff : ENNReal.ofReal M ≠ 0 := (ENNReal.ofReal_pos.mpr hM).ne'
  intro htop
  apply hprod
  simp [htop, hcoeff]

/-- At a locally finite measure, cone-mass events provide the finiteness
needed for the contradiction at the chosen scale. -/
theorem not_satisfiesConeCondition_of_frequently_coneMass_locallyFinite
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (Λ : Set ℂ) (z : ℂ)
    (C : ℝ) (hC : 0 < C) (hz : z ≠ 0)
    (hscales : ∀ Q : Set ℂ, IsCone Q → ∃ᶠ n : ℕ in atTop,
      coneMassEvent μ Q (2 * C) ((2 : ℝ)⁻¹ ^ n) z)
    (hgreen : ∀ r : ℝ, 0 < r →
      0 < annulusGreenPotentialSup μ z (3 * r) (6 * r))
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
  have hfin := annulusGreenPotentialSup_ne_top_of_coneMassEvent μ Q (2 * C) r z
    (by linarith) hevent
  have hfull : annulus z (4 * r) (5 * r) ⊆ Λ :=
    annulus_subset_of_coneMassEvent μ Λ Q z C r R hC hR' hinterior (hgreen r hr) hfin
      (hbound r hr h0) hevent
  obtain ⟨x, hxann, hxcompl⟩ :=
    outer_annulus_inter_compl_nonempty_of_exterior_cone Q' Λ z r S hQ' hr hS' hexterior
  exact hxcompl (hfull hxann)

end HarmonicBalls
