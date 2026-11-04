import HarmonicBalls.Draft.Section6
import HarmonicBalls.Proofs.Sec7.OriginAvoidingCircle
import HarmonicBalls.Proofs.Sec7.ShellBarrier

/-!
# Approximation by the planar lattice

The mesh used in Proposition 6.1 covers the plane at a radius much smaller
than the annulus radii in the Section 7 covering arguments.
-/

namespace HarmonicBalls

open Metric Set Section6

/-- Every point is within twice the mesh of the scaled square lattice. -/
theorem exists_scaledLattice_dist_lt (δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    ∃ w ∈ scaledLattice δ, dist z w < 2 * δ := by
  let j : ℤ := ⌊z.re / δ⌋
  let k : ℤ := ⌊z.im / δ⌋
  let w : ℂ := (δ : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)
  have hre₀ : 0 ≤ z.re - (j : ℝ) * δ := Int.sub_floor_div_mul_nonneg z.re hδ
  have hre₁ : z.re - (j : ℝ) * δ < δ := Int.sub_floor_div_mul_lt z.re hδ
  have him₀ : 0 ≤ z.im - (k : ℝ) * δ := Int.sub_floor_div_mul_nonneg z.im hδ
  have him₁ : z.im - (k : ℝ) * δ < δ := Int.sub_floor_div_mul_lt z.im hδ
  have hre : (z - w).re = z.re - (j : ℝ) * δ := by
    simp only [w, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : (z - w).im = z.im - (k : ℝ) * δ := by
    simp only [w, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.intCast_re, Complex.intCast_im,
      Complex.I_re, Complex.I_im]
    ring
  refine ⟨w, ⟨j, k, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  calc
    ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < 2 * δ := by rw [hre, him, abs_of_nonneg hre₀, abs_of_nonneg him₀]; linarith

/-- Points in the unit ball with a margin from the excluded origin disk can
be approximated by points of the prevalence grid. -/
theorem exists_prevalenceGrid_dist_lt {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hunit : dist z 0 < 1) (haway : 10 * Real.sqrt ε + ε ≤ dist z 0) :
    ∃ w ∈ prevalenceGrid ε, dist z w < ε / 50 := by
  obtain ⟨w, hw, hclose⟩ := exists_scaledLattice_dist_lt (ε / 100) (by positivity) z
  have hclose' : dist z w < ε / 50 := by linarith
  refine ⟨w, ⟨⟨?_, ?_⟩, hw⟩, hclose'⟩
  · rw [mem_ball]
    have ht := dist_triangle w z (0 : ℂ)
    rw [dist_comm w z] at ht
    linarith
  · rw [mem_ball, not_lt]
    have ht := dist_triangle z w (0 : ℂ)
    linarith

/-- A choice of intermediate radius with a quantitative outer margin. -/
theorem exists_radius_separated_with_outer_margin {r : ℝ} (hr : 0 < r) (d : ℝ) :
    ∃ q : ℝ, r / 4 < q ∧ q ≤ 7 * r / 16 ∧ r / 32 ≤ |q - d| := by
  by_cases h : d ≤ 3 * r / 8
  · refine ⟨7 * r / 16, by linarith, le_rfl, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨5 * r / 16, by linarith, by linarith, ?_⟩
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The origin-avoiding circle admits the lattice-ball cover required for
Proposition 7.1, with every closed Harnack ball inside the punctured domain. -/
theorem exists_origin_avoiding_lattice_circle_cover
    {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hsmall : 10 * Real.sqrt ε + ε < r / 32) {z : ℂ} (hz : dist z 0 < 1 / 2)
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w) :
    ∃ q : ℝ, r / 4 < q ∧ q < r / 2 ∧
      ∀ y ∈ sphere z q, ∃ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε),
        P ρ w ∧ y ∈ ball w (ρ / 2) ∧ closedBall w ρ ⊆ ball 0 1 \ {z} := by
  obtain ⟨q, hq₁, hqbound, hsep⟩ := exists_radius_separated_with_outer_margin hr (dist z 0)
  have hq₂ : q < r / 2 := by linarith
  refine ⟨q, hq₁, hq₂, fun y hy => ?_⟩
  have hyq : dist y z = q := mem_sphere.1 hy
  have hsqrt : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hyunit : dist y 0 < 1 := by
    have ht := dist_triangle y z (0 : ℂ)
    linarith
  have hyaway : r / 32 ≤ dist y 0 := by
    have ht := abs_dist_sub_le y (0 : ℂ) z
    rw [hyq, dist_comm (0 : ℂ) z] at ht
    exact hsep.trans ht
  obtain ⟨w, hw, hclose⟩ := exists_prevalenceGrid_dist_lt hε hyunit (by linarith)
  obtain ⟨ρ, hρ, hP⟩ := hgood w hw
  refine ⟨w, hw, ρ, hρ, hP, ?_, ?_⟩
  · rw [mem_ball]
    linarith [hρ.1]
  · apply closedBall_subset_unitBall_sdiff_pole_of_near_sphere hy (δ := ε / 50)
    · simpa only [dist_comm w y] using hclose
    · linarith [hρ.2]
    · linarith [hρ.2]

/-- The lattice-circle cover and Harnack exclusion confine a connected cluster.
The lower annulus-mass and Harnack conditions remain explicit. -/
theorem closure_subset_ball_of_prevalence_grid
    (μ : MeasureTheory.Measure ℂ) {B : Set ℂ} {r ε α : ℝ} {z : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hsmall : 10 * Real.sqrt ε + ε < r / 32) (hz : dist z 0 < 1 / 2)
    (hB : IsPreconnected B) (hzB : z ∈ B) (P : ℝ → ℂ → Prop)
    (hgood : ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w)
    (hlower : ∀ w ∈ prevalenceGrid ε, ∀ ρ ∈ Icc ε (Real.sqrt ε), P ρ w →
      closedBall w ρ ⊆ ball 0 1 \ {z} →
      μ B ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ))
    (hharnack : ∀ w ∈ prevalenceGrid ε, ∀ ρ ∈ Icc ε (Real.sqrt ε), P ρ w →
      closedBall w ρ ⊆ ball 0 1 \ {z} →
      μ (B ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      B ∩ ball w (ρ / 2) = ∅) :
    closure B ⊆ ball z (r / 2) := by
  obtain ⟨q, hq₁, hq₂, hcover⟩ :=
    exists_origin_avoiding_lattice_circle_cover hr hr1 hε hsmall hz P hgood
  apply closure_subset_ball_of_disjoint_sphere hB hzB (by linarith) hq₂
  apply Set.disjoint_left.2
  intro y hyB hyq
  obtain ⟨w, hw, ρ, hρ, hP, hyball, hdomain⟩ := hcover y hyq
  have hmass : μ (B ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) :=
    (MeasureTheory.measure_mono inter_subset_left).trans (hlower w hw ρ hρ hP hdomain)
  have hempty := hharnack w hw ρ hρ hP hdomain hmass
  exact (eq_empty_iff_forall_notMem.1 hempty) y ⟨hyB, hyball⟩

end HarmonicBalls
