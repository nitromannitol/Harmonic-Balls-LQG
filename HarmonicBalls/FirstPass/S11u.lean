import HarmonicBalls.FirstPass.S11u.Variance
import HarmonicBalls.FirstPass.Frozen.S11p

/-!
# The circle-average limit derived from the whole-plane GFF

`WholePlaneCircleAverageLimitFrozen` (Frozen/S11p.lean) is proved as the theorem
`wholePlaneCircleAverageLimit_derived`, from `IsWholePlaneGFF` alone. The unit-mass test functions are the normalized
Section 8 annular bumps `unitCircleDensity r (r η) z` (support in `{| |x - z| - r | ≤ η}`, width `δ = r η`), with
`η_j = η₀ 2^{-j}`. The second moment of `hC ψ_j - hcirc(r, z)` is the whole-plane kernel combination, bounded by
`8 η_j / r` (`abs_unitCircleDensity_covariance_combination`), so the series converges almost surely.
Reference: Duplantier-Sheffield, arXiv:0808.1560v2, Section 3.1, Proposition 3.1; Bou-Rabee-Gwynne,
arXiv:2208.11795v3, Section 2.1 eq. (2.1), p. 8.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

universe u

/-- On the support of the annular density, `| |x - z| - r | < η` (from `|ρ² - r²| < δ = r η`). -/
theorem abs_norm_sub_radius_lt_of_unitCircleDensity_ne_zero {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hwidth : δ ≤ r * η) (z x : ℂ) (hx : unitCircleDensity r δ hδ z x ≠ 0) :
    |‖x - z‖ - r| < η := by
  have hcd : circleDensity r δ hδ z x ≠ 0 := (mul_ne_zero_iff.mp hx).2
  have hsup := circleDensity_support r δ hδ z x hcd
  rw [abs_lt] at hsup
  obtain ⟨h1, h2⟩ := hsup
  have hρ : 0 ≤ ‖x - z‖ := norm_nonneg _
  have hη : 0 < η := by
    by_contra hneg
    have hneg' : η ≤ 0 := not_lt.mp hneg
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

/-- The support of the normalized annular density lies in the closed annulus of width `η`. -/
theorem tsupport_unitCircleDensity_subset {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    (z : ℂ) :
    tsupport (unitCircleDensity r δ hδ z) ⊆ {x : ℂ | |‖x - z‖ - r| ≤ η} := by
  apply closure_minimal _ (isClosed_le (by fun_prop : Continuous fun x : ℂ => |‖x - z‖ - r|) continuous_const)
  intro x hx
  exact (abs_norm_sub_radius_lt_of_unitCircleDensity_ne_zero hr hδ hwidth z x hx).le

/-- The closed annulus `{| |x - z| - r | ≤ η}` lies in any thickening of the circle `∂B_r(z)` of width `> η`. -/
theorem annulus_subset_thickening {r η δ₀ : ℝ} (hr : 0 < r) (hηr : η < r / 2) (hηδ : η < δ₀) (z : ℂ) :
    {x : ℂ | |‖x - z‖ - r| ≤ η} ⊆ thickening δ₀ (sphere z r) := by
  intro x hx
  change |‖x - z‖ - r| ≤ η at hx
  have hρ : 0 < ‖x - z‖ := by
    have := (abs_le.mp hx).1
    linarith
  set ρ := ‖x - z‖ with hρdef
  set t : ℝ := r / ρ with htdef
  have ht : 0 < t := div_pos hr hρ
  rw [mem_thickening_iff]
  refine ⟨z + ((t : ℝ) : ℂ) * (x - z), ?_, ?_⟩
  · rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, htdef, ← hρdef]
    field_simp
  · have hxy : x - (z + ((t : ℝ) : ℂ) * (x - z)) = (((1 - t : ℝ)) : ℂ) * (x - z) := by
      push_cast
      ring
    rw [dist_eq_norm, hxy, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hρdef]
    have h1 : |1 - t| * ρ = |ρ - r| := by
      rw [show 1 - t = (ρ - r) / ρ by rw [htdef]; field_simp, abs_div, abs_of_pos hρ,
        div_mul_cancel₀ _ hρ.ne']
    rw [h1]
    linarith

/-- The normalized annular density is a test function on `O` once its annulus lies in `O`. -/
theorem isTestFunction_unitCircleDensity {O : Set ℂ} {r η : ℝ} (z : ℂ) (hr : 0 < r) (hη : 0 < η)
    (hO : {x : ℂ | |‖x - z‖ - r| ≤ η} ⊆ O) :
    IsTestFunction O (unitCircleDensity r (r * η) (mul_pos hr hη) z) := by
  refine ⟨?_, unitCircleDensity_hasCompactSupport hr.le (mul_pos hr hη) z, ?_⟩
  · exact ContDiff.mul contDiff_const (circleDensity_contDiff r (r * η) (mul_pos hr hη) z)
  · exact (tsupport_unitCircleDensity_subset hr (mul_pos hr hη) le_rfl z).trans hO

/-- `log(r + η) - log(r - η) ≤ 4 η / r` for `0 < η ≤ r / 2`. -/
theorem log_add_sub_log_sub_le_four_mul {r η : ℝ} (hr : 0 < r) (hη : 0 < η) (hηr : η ≤ r / 2) :
    Real.log (r + η) - Real.log (r - η) ≤ 4 * η / r := by
  have hpos : 0 < r - η := by linarith
  rw [← Real.log_div (by linarith) hpos.ne']
  have h1 := Real.log_le_sub_one_of_pos (show 0 < (r + η) / (r - η) by positivity)
  have h2 : (r + η) / (r - η) - 1 ≤ 4 * η / r := by
    rw [div_sub_one hpos.ne', div_le_div_iff₀ hpos hr]
    nlinarith [mul_nonneg hη.le (show 0 ≤ r - 2 * η by linarith)]
  linarith

/-- The circle-average limit, derived from the whole-plane GFF (no frozen input). -/
theorem wholePlaneCircleAverageLimit_derived : WholePlaneCircleAverageLimitFrozen.{u} := by
  intro Ω _ P _ hC hcirc hGFF O r z hO hr hsph
  obtain ⟨δ₀, hδ₀, hthick⟩ := (isCompact_sphere z r).exists_thickening_subset_open hO hsph
  set η₀ : ℝ := min (r / 4) (δ₀ / 2) with hη₀def
  have hη₀ : 0 < η₀ := lt_min (by linarith) (by linarith)
  have hη₀r : η₀ ≤ r / 4 := min_le_left _ _
  have hη₀δ : η₀ ≤ δ₀ / 2 := min_le_right _ _
  set η : ℕ → ℝ := fun j => η₀ * (1 / 2) ^ j with hηdef
  have hηpos : ∀ j, 0 < η j := fun j => mul_pos hη₀ (by positivity)
  have hηle : ∀ j, η j ≤ η₀ := fun j =>
    mul_le_of_le_one_right hη₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hηq : ∀ j, η j < r / 2 := fun j => by linarith [hηle j, hη₀r, hr]
  have hηδ : ∀ j, η j < δ₀ := fun j => by linarith [hηle j, hη₀δ]
  have hηr : ∀ j, η j < r := fun j => by linarith [hηq j]
  have hδpos : ∀ j, 0 < r * η j := fun j => mul_pos hr (hηpos j)
  have hann : ∀ j, {x : ℂ | |‖x - z‖ - r| ≤ η j} ⊆ O := fun j =>
    (annulus_subset_thickening hr (hηq j) (hηδ j) z).trans hthick
  have hTF : ∀ j, IsTestFunction O (unitCircleDensity r (r * η j) (hδpos j) z) := fun j =>
    isTestFunction_unitCircleDensity z hr (hηpos j) (hann j)
  have hTFu : ∀ j, IsTestFunction univ (unitCircleDensity r (r * η j) (hδpos j) z) := fun j =>
    isTestFunction_unitCircleDensity z hr (hηpos j) (subset_univ _)
  refine ⟨fun j => unitCircleDensity r (r * η j) (hδpos j) z, fun j =>
    ⟨hTF j, integral_unitCircleDensity hr.le (hδpos j) z⟩, ?_⟩
  have hD : ∀ j, MemLp (fun ω => hC ω (unitCircleDensity r (r * η j) (hδpos j) z) - hcirc ω r z) 2 P := by
    intro j
    have hp : MemLp (fun ω => hC ω (unitCircleDensity r (r * η j) (hδpos j) z)) 2 P :=
      (hGFF.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing _, hTFu j⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
    exact hp.sub hz
  have hbound : ∀ j, ∫ ω, (hC ω (unitCircleDensity r (r * η j) (hδpos j) z) - hcirc ω r z) ^ 2 ∂P ≤
      8 * η₀ / r * (1 / 2) ^ j := by
    intro j
    rw [integral_sq_pairing_sub_circle_eq_variance hGFF hr z _ (hTFu j),
      variance_pairing_sub_circle_eq hGFF hr z _ (hTFu j)]
    have hc := abs_unitCircleDensity_covariance_combination (r := r) (δ := r * η j) (η := η j) hr
      (hδpos j) (hηr j) le_rfl z
    have hl := log_add_sub_log_sub_le_four_mul hr (hηpos j) (hηq j).le
    refine le_trans (le_abs_self _) (le_trans hc ?_)
    have hscale : 2 * (4 * η j / r) = 8 * η₀ / r * (1 / 2) ^ j := by
      have hηj : η j = η₀ * (1 / 2) ^ j := rfl
      rw [hηj]
      ring
    linarith
  have hsum : Summable (fun j : ℕ => 8 * η₀ / r * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  filter_upwards [ae_tendsto_zero_of_summable_integral_sq
    (fun j ω => hC ω (unitCircleDensity r (r * η j) (hδpos j) z) - hcirc ω r z) hD _ hsum hbound] with ω hω
  exact tendsto_sub_nhds_zero_iff.mp hω

end HarmonicBalls
