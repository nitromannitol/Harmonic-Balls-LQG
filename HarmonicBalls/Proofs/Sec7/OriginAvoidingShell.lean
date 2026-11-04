import HarmonicBalls.Proofs.Sec7.LatticeApproximation

/-!
# A shell separated from the singularity

For Proposition 7.2, an offset level around the earlier cluster can be chosen
away from the origin, even when the origin is on its boundary.
-/

namespace HarmonicBalls

open Metric Set Section6
open scoped Pointwise

/-- A connected set meeting `A` cannot cross an empty distance level. -/
theorem IsPreconnected.closure_subset_add_ball_of_disjoint_infDist_level
    {A B : Set ℂ} {q R : ℝ} (hB : IsPreconnected B)
    (hAB : (A ∩ B).Nonempty) (hq : 0 < q) (hqR : q < R)
    (hlevel : ∀ x ∈ B, infDist x A ≠ q) :
    closure B ⊆ A + ball 0 R := by
  obtain ⟨a, haA, haB⟩ := hAB
  have hA : A.Nonempty := ⟨a, haA⟩
  have hinner : B ⊆ thickening q A := by
    intro x hx
    by_contra hxinner
    have hxq : q ≤ infDist x A := by
      rw [mem_thickening_iff_infDist_lt hA] at hxinner
      exact le_of_not_gt hxinner
    have haq : infDist a A ≤ q := by rw [infDist_zero_of_mem haA]; exact hq.le
    obtain ⟨y, hyB, hyq⟩ := hB.intermediate_value haB hx
      (continuous_infDist_pt A).continuousOn ⟨haq, hxq⟩
    exact hlevel y hyB hyq
  rw [add_ball_zero]
  exact (closure_mono hinner).trans ((closure_thickening_subset_cthickening q A).trans
    (cthickening_subset_thickening' (lt_trans hq hqR) hqR A))

/-- One of two offset levels is separated from the distance to the origin. -/
theorem exists_origin_separated_infDist_level {s : ℝ} (hs : 0 < s) (d : ℝ) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 60 * s ∧ 20 * s ≤ q ∧ 20 * s ≤ |q - d| := by
  by_cases h : d ≤ 40 * s
  · refine ⟨60 * s, by positivity, le_rfl, by linarith, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨20 * s, by positivity, by linarith, le_rfl, ?_⟩
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The selected distance level is covered by prevalence-grid balls whose
closed Harnack balls avoid the earlier cluster and stay in the unit ball. -/
theorem exists_origin_avoiding_lattice_shell_cover
    {A : Set ℂ} (hA : A.Nonempty) {ε : ℝ} (hε : 0 < ε)
    (hεsqrt : ε ≤ Real.sqrt ε)
    (hunit : thickening (70 * Real.sqrt ε) A ⊆ ball 0 1)
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w) :
    ∃ q : ℝ, 0 < q ∧ q < 70 * Real.sqrt ε ∧
      ∀ x, infDist x A = q → ∃ w ∈ prevalenceGrid ε,
        ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w ∧ x ∈ ball w (ρ / 2) ∧
          closedBall w ρ ⊆ ball 0 1 \ A := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  obtain ⟨q, hqpos, hqmax, hqmin, hsep⟩ :=
    exists_origin_separated_infDist_level hs (infDist (0 : ℂ) A)
  refine ⟨q, hqpos, by linarith, fun x hx => ?_⟩
  have hxunit : dist x 0 < 1 := by
    apply mem_ball.1
    apply hunit
    exact (mem_thickening_iff_infDist_lt hA).2 (by rw [hx]; linarith)
  have hxaway : 20 * Real.sqrt ε ≤ dist x 0 := by
    have h1 := infDist_le_infDist_add_dist (x := x) (y := (0 : ℂ)) (s := A)
    have h2 := infDist_le_infDist_add_dist (x := (0 : ℂ)) (y := x) (s := A)
    rw [hx, dist_comm (0 : ℂ) x] at h2
    rw [hx] at h1
    have habs : |q - infDist (0 : ℂ) A| ≤ dist x 0 := abs_le.2 ⟨by linarith, by linarith⟩
    exact hsep.trans habs
  obtain ⟨w, hw, hxw⟩ := exists_prevalenceGrid_dist_lt hε hxunit (by linarith)
  obtain ⟨ρ, hρ, hP⟩ := hgood w hw
  refine ⟨w, hw, ρ, hρ, hP, ?_, ?_⟩
  · rw [mem_ball]
    linarith [hρ.1]
  · intro y hy
    have hyw : dist y w ≤ ρ := mem_closedBall.1 hy
    have hyx : dist y x < 2 * Real.sqrt ε := by
      have ht := dist_triangle y w x
      rw [dist_comm w x] at ht
      linarith [hρ.2]
    have hyA : infDist y A < 70 * Real.sqrt ε := by
      have ht := infDist_le_infDist_add_dist (x := y) (y := x) (s := A)
      rw [hx] at ht
      linarith
    refine ⟨hunit ((mem_thickening_iff_infDist_lt hA).2 hyA), ?_⟩
    intro hyA'
    have ht := infDist_le_dist_of_mem (x := x) hyA'
    rw [hx, dist_comm x y] at ht
    linarith

end HarmonicBalls
