import HarmonicBalls.Proofs.Sec6.CriterionThreeLatticeApprox
import HarmonicBalls.Proofs.Sec6.ScaledCriterionThreeCount

/-! # Rescaling the lattice for the third criterion -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- The lattice in an annulus of arbitrary positive radius embeds in a
translated copy of the unit-scale prevalence grid. -/
theorem scaled_annulus_lattice_subset_prevalenceGrid
    {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 9 ≤ n) (x : ℂ) :
    ∃ y : ℂ, ∀ z ∈ scaledLattice (dyadicScale n * s / 100) ∩ annulus x (s / 2) s,
      s⁻¹ • z - y ∈ prevalenceGrid (dyadicScale n) := by
  have hinj : Function.Injective (fun z : ℂ => s • z) := by
    intro z w h
    have h' := congrArg (fun z : ℂ => s⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using h'
  have hscale (j l : ℤ) :
      s • (((dyadicScale n / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) =
        (((dyadicScale n * s / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) := by
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 1
    congr 1
    ring
  have hlat (z : ℂ) : z ∈ scaledLattice (dyadicScale n / 100) ↔
      s • z ∈ scaledLattice (dyadicScale n * s / 100) := by
    change (∃ j l : ℤ, z = ((dyadicScale n / 100 : ℝ) : ℂ) *
      ((j : ℂ) + (l : ℂ) * Complex.I)) ↔
      (∃ j l : ℤ, s • z = ((dyadicScale n * s / 100 : ℝ) : ℂ) *
      ((j : ℂ) + (l : ℂ) * Complex.I))
    constructor
    · rintro ⟨j, l, rfl⟩
      exact ⟨j, l, hscale j l⟩
    · rintro ⟨j, l, h⟩
      exact ⟨j, l, hinj (h.trans (hscale j l).symm)⟩
  have hmem (z : ℂ) : z ∈ annulus (s⁻¹ • x) (1 / 2) 1 ↔
      s • z ∈ annulus x (s / 2) s := by
    have hx : s • (s⁻¹ • x) = x := by simp [hs.ne']
    conv_rhs => rw [← hx]
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, dist_smul₀,
      Real.norm_eq_abs, abs_of_pos hs]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith
  obtain ⟨y, hy, hxy⟩ := exists_scaledLattice_dist_lt (s⁻¹ • x) (δ := dyadicScale n / 100)
    (div_pos (dyadicScale_pos n) (by norm_num))
  refine ⟨y, ?_⟩
  intro z hz
  apply shifted_annulus_lattice_subset_prevalenceGrid hn hy hxy (s⁻¹ • z)
  constructor
  · apply (hlat _).mpr
    simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] using hz.1
  · apply (hmem _).mpr
    simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] using hz.2

end HarmonicBalls.Section6
