import HarmonicBalls.Proofs.Sec6.SizeRatioLocalComparison

/-! # Separated annuli around nearby centres -/

namespace HarmonicBalls.Section6

open Metric Set

/-- A nearby good-annulus ring lies in the enlarged ring about the original
centre whenever the displacement is smaller than the radial margin. -/
theorem nearby_annulus_subset_enlarged {z w : ℂ} {r η : ℝ}
    (hd : dist w z < η * r) :
    annulus w (3*r) (5*r) ⊆ annulus z (3*r-η*r) (5*r+η*r) := by
  intro y hy
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le] at hy ⊢
  have h₁ := dist_triangle y w z
  have h₂ := dist_triangle y z w
  rw [dist_comm z w] at h₂
  constructor <;> linarith [hy.1, hy.2]

/-- The enlarged ring lies in the separated size annulus if its centre is in
the middle annulus and its outer radius is smaller than the margin. -/
theorem enlarged_annulus_subset_size_annulus {x₀ z : ℂ} {ρ r η : ℝ}
    (hρ : 0 < ρ) (hz : z ∈ annulus x₀ (ρ/2) ρ)
    (hr : 0 < r) (hη : 0 ≤ η) (hsmall : 5*r+η*r < ρ/4) :
    annulus z (3*r-η*r) (5*r+η*r) ⊆ annulus x₀ (ρ/4) (2*ρ) := by
  apply Set.Subset.trans ?_ (annulusBallMassSize_ball_subset_annulus hρ hz ⟨by positivity, hsmall⟩)
  intro y hy
  exact hy.1

/-- Separation of the size annulus transfers to every nearby good-annulus
ring whose enlarged ring fits inside it. -/
theorem nearby_annulus_separated_of_size_annulus {x₀ z w : ℂ} {ρ r η : ℝ}
    (hρ : 0 < ρ) (hz : z ∈ annulus x₀ (ρ/2) ρ)
    (hr : 0 < r) (hη : 0 ≤ η) (hsmall : 5*r+η*r < ρ/4)
    (hd : dist w z < η*r)
    (hsep : ρ/100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ/4) (2*ρ))) :
    r/100 ≤ infDist (0 : ℂ) (annulus w (3*r) (5*r)) := by
  have hsub := (nearby_annulus_subset_enlarged hd).trans
    (enlarged_annulus_subset_size_annulus hρ hz hr hη hsmall)
  have hne : (annulus w (3*r) (5*r)).Nonempty := by
    refine ⟨w + ((4*r : ℝ) : ℂ), ?_⟩
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le]
    have he : dist (w + ((4*r : ℝ) : ℂ)) w = 4*r := by
      simp [dist_eq_norm, hr.le]
    rw [he]
    constructor <;> linarith
  have hm := infDist_le_infDist_of_subset hsub hne (x := (0 : ℂ))
  have hmarg : r ≤ ρ := by nlinarith [mul_nonneg hη hr.le]
  linarith

/-- The three geometric conditions used in the singular count transfer follow
from the middle-annulus and margin conditions, simultaneously at each scale. -/
theorem finite_annulus_separation_of_margin {x₀ z w : ℂ} {ρ η : ℝ}
    (r : ℕ → ℝ) (s : Finset ℕ)
    (hρ : 0 < ρ) (hz : z ∈ annulus x₀ (ρ/2) ρ) (hη : 0 ≤ η)
    (hr : ∀ i ∈ s, 0 < r i)
    (hsmall : ∀ i ∈ s, 5*r i+η*r i < ρ/4)
    (hd : ∀ i ∈ s, dist w z < η*r i)
    (hsep : ρ/100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ/4) (2*ρ))) :
    (∀ i ∈ s, annulus z (3*r i) (5*r i) ⊆ annulus x₀ (ρ/4) (2*ρ)) ∧
    (∀ i ∈ s, annulus z (3*r i-η*r i) (5*r i+η*r i) ⊆ annulus x₀ (ρ/4) (2*ρ)) ∧
    (∀ i ∈ s, r i/100 ≤ infDist (0 : ℂ) (annulus w (3*r i) (5*r i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hsmall' : 5*r i < ρ/4 := by
      have := mul_nonneg hη (hr i hi).le
      linarith [hsmall i hi]
    intro y hy
    exact annulusBallMassSize_ball_subset_annulus hρ hz
      (r := 5*r i) ⟨mul_pos (by norm_num) (hr i hi), hsmall'⟩ hy.1
  · intro i hi
    exact enlarged_annulus_subset_size_annulus hρ hz (hr i hi) hη (hsmall i hi)
  · intro i hi
    exact nearby_annulus_separated_of_size_annulus hρ hz (hr i hi) hη (hsmall i hi) (hd i hi) hsep

end HarmonicBalls.Section6
