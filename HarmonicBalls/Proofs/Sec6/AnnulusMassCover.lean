import HarmonicBalls.Proofs.Sec6.AnnulusCoverScaling

/-! # Finite-cover mass estimate

The measure pigeonhole estimate used in Lemma 6.8 follows from finite
subadditivity and holds also for measures taking the value infinity.
-/

namespace HarmonicBalls.Section6

open Set Metric MeasureTheory
open scoped BigOperators ENNReal

/-- A nonempty finite disc cover contains a disc whose mass controls the mass
of the covered set, with a factor equal to the number of discs. -/
theorem exists_disc_mass_ge_of_finite_cover {μ : Measure ℂ} {A L : Set ℂ}
    (T : Finset ℂ) (hT : T.Nonempty) (f : ℂ → ℂ) (d : ℝ)
    (hcover : A ⊆ ⋃ x ∈ T, ball (f x) d) :
    ∃ x ∈ T, μ (A ∩ L) ≤ (T.card : ℝ≥0∞) * μ (ball (f x) d ∩ L) := by
  classical
  let m : ℂ → ℝ≥0∞ := fun x => μ (ball (f x) d ∩ L)
  obtain ⟨x, hx, hmax⟩ := T.exists_max_image m hT
  refine ⟨x, hx, ?_⟩
  calc
    μ (A ∩ L) ≤ μ (⋃ x ∈ T, (ball (f x) d ∩ L)) := by
      apply measure_mono
      intro y hy
      obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy.1)
      exact mem_iUnion₂.mpr ⟨z, hz, hyz, hy.2⟩
    _ ≤ ∑ z ∈ T, m z := measure_biUnion_finset_le T _
    _ ≤ T.card • m x := Finset.sum_le_card_nsmul T m (m x) hmax
    _ = (T.card : ℝ≥0∞) * μ (ball (f x) d ∩ L) := by simp [m, nsmul_eq_mul]

/-- Uniformly over centres, scales, measures and sets, one disc in a fixed
finite family controls the mass in the middle annulus and has its doubled
closed disc inside the outer annulus. -/
theorem exists_uniform_annulus_mass_disc {s₁ s₂ s₃ s₄ : ℝ}
    (h12 : s₁ < s₂) (h23 : s₂ < s₃) (h34 : s₃ < s₄) (hs₂ : 0 ≤ s₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : Finset ℂ, T.Nonempty ∧
      ∀ (w : ℂ) (r : ℝ), 0 < r → ∀ (μ : Measure ℂ) (L : Set ℂ),
        ∃ x ∈ T,
          r • x + w ∈ annulus w (s₂ * r) (s₃ * r) ∧
          closedBall (r • x + w) (2 * δ * r) ⊆ annulus w (s₁ * r) (s₄ * r) ∧
          μ (annulus w (s₂ * r) (s₃ * r) ∩ L) ≤
            (T.card : ℝ≥0∞) * μ (ball (r • x + w) (δ * r) ∩ L) := by
  classical
  obtain ⟨δ, hδ, S, hSf, hSsub, hscaled⟩ := exists_uniform_scaled_annulus_cover h12 h34
  have hA : (annulus (0 : ℂ) s₂ s₃).Nonempty := by
    refine ⟨(((s₂ + s₃) / 2 : ℝ) : ℂ), ?_⟩
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm,
      sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ (s₂ + s₃) / 2)]
    constructor <;> linarith
  have hSne : S.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hc := (hscaled 0 1 (by norm_num)).2.1
    have ha' : a ∈ annulus (0 : ℂ) (s₂ * 1) (s₃ * 1) := by simpa using ha
    obtain ⟨x, hx, _⟩ := mem_iUnion₂.mp (hc ha')
    exact ⟨x, hx⟩
  refine ⟨δ, hδ, hSf.toFinset, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hSne
    exact ⟨x, hSf.mem_toFinset.mpr hx⟩
  · intro w r hr μ L
    obtain ⟨hcent, hcov, hout⟩ := hscaled w r hr
    have hfin : hSf.toFinset.Nonempty := by
      obtain ⟨x, hx⟩ := hSne
      exact ⟨x, hSf.mem_toFinset.mpr hx⟩
    have hcov' : annulus w (s₂ * r) (s₃ * r) ⊆
        ⋃ x ∈ hSf.toFinset, ball (r • x + w) (δ * r) := by
      simpa only [hSf.mem_toFinset] using hcov
    obtain ⟨x, hx, hmass⟩ := exists_disc_mass_ge_of_finite_cover
      hSf.toFinset hfin (fun x => r • x + w) (δ * r) hcov'
    exact ⟨x, hx, hcent x (hSf.mem_toFinset.mp hx), hout x (hSf.mem_toFinset.mp hx), hmass⟩

end HarmonicBalls.Section6
