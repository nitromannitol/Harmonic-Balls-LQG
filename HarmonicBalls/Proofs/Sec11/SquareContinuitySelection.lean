import HarmonicBalls.Proofs.Sec11.SquareFrontierLines
import HarmonicBalls.Proofs.Sec8.RandomMeasureContinuitySets

/-! # Selecting square continuity sets -/

namespace HarmonicBalls
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- Every interval of positive radii contains a centred square with null
frontier for an s-finite measure. -/
theorem exists_centered_square_null_frontier (μ : Measure ℂ) [SFinite μ]
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Ioo (0 : ℝ) R,
      μ (frontier (closedSquare (c - ⟨r, r⟩) (2 * r))) = 0 := by
  let A : Set ℝ := {t | 0 < μ {x : ℂ | x.re = t}}
  let B : Set ℝ := {t | 0 < μ {x : ℂ | x.im = t}}
  have hA : A.Countable := (countable_positive_coordinate_lines μ).1
  have hB : B.Countable := (countable_positive_coordinate_lines μ).2
  let E : Set ℝ := (fun r : ℝ => c.re - r) ⁻¹' A ∪
    (fun r : ℝ => c.re + r) ⁻¹' A ∪
    (fun r : ℝ => c.im - r) ⁻¹' B ∪
    (fun r : ℝ => c.im + r) ⁻¹' B
  have hE : E.Countable := by
    apply Set.Countable.union (Set.Countable.union (Set.Countable.union ?_ ?_) ?_) ?_
    all_goals first | exact hA.preimage (by intro a b h; linarith) |
      exact hB.preimage (by intro a b h; linarith)
  have hae : ∀ᵐ r : ℝ ∂volume, r ∉ E :=
    measure_eq_zero_iff_ae_notMem.mp (hE.measure_zero volume)
  obtain ⟨r, hr, hrE⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (μ := volume) (s := Ioo (0 : ℝ) R)
    (ne_of_gt ((Measure.measure_Ioo_pos volume).2 hR)) (ae_restrict_of_ae hae)
  have hlines : c.re - r ∉ A ∧ c.re + r ∉ A ∧ c.im - r ∉ B ∧ c.im + r ∉ B := by
    simpa only [E, mem_union, mem_preimage, not_or, and_assoc] using hrE
  refine ⟨r, hr, ?_⟩
  have h₁ : μ {x : ℂ | x.re = c.re - r} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hlines.1)
  have h₂ : μ {x : ℂ | x.re = c.re + r} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hlines.2.1)
  have h₃ : μ {x : ℂ | x.im = c.im - r} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hlines.2.2.1)
  have h₄ : μ {x : ℂ | x.im = c.im + r} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hlines.2.2.2)
  have hre : (c - (⟨r, r⟩ : ℂ)).re + 2 * r = c.re + r := by simp; ring
  have him : (c - (⟨r, r⟩ : ℂ)).im + 2 * r = c.im + r := by simp; ring
  apply measure_frontier_closedSquare_eq_zero μ (c - ⟨r, r⟩) (by linarith [hr.1])
  · simpa using h₁
  · simpa only [hre] using h₂
  · simpa using h₃
  · simpa only [him] using h₄

/-- A uniformly bounded random measure admits a deterministic centred
square with almost surely null frontier in any positive radius interval. -/
theorem exists_ae_centered_square_null_frontier_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure ℂ) (hν : AEMeasurable ν P)
    (hbound : ∀ᵐ ω ∂P, ν ω univ ≤ 1) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Ioo (0 : ℝ) R,
      ∀ᵐ ω ∂P, ν ω (frontier (closedSquare (c - ⟨r, r⟩) (2 * r))) = 0 := by
  let : IsFiniteMeasure (P.bind ν) := isFiniteMeasure_bind_of_ae_univ_le_one P ν hν hbound
  obtain ⟨r, hr, hzero⟩ := exists_centered_square_null_frontier (P.bind ν) c hR
  exact ⟨r, hr, ae_measure_eq_zero_of_bind_eq_zero P ν hν
    isClosed_frontier.measurableSet hzero⟩

/-- A centred square of half-side `r` is contained in the ball of radius
`2r` around its centre. -/
theorem centered_closedSquare_subset_closedBall (c : ℂ) {r : ℝ} :
    closedSquare (c - ⟨r, r⟩) (2 * r) ⊆ closedBall c (2 * r) := by
  intro x hx
  have hx' : c.re - r ≤ x.re ∧ x.re ≤ c.re - r + 2 * r ∧
      c.im - r ≤ x.im ∧ x.im ≤ c.im - r + 2 * r := by
    simpa [closedSquare, Complex.mem_reProdIm, mem_Icc, and_assoc] using hx
  have hre : |(x - c).re| ≤ r := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith [hx'.1, hx'.2.1]
  have him : |(x - c).im| ≤ r := by
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith [hx'.2.2.1, hx'.2.2.2]
  rw [mem_closedBall, dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (x - c)
  linarith

/-- A locally finite random measure admits a deterministic centred square
with almost surely null frontier in any positive radius interval. -/
theorem exists_ae_centered_square_null_frontier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Ioo (0 : ℝ) R,
      ∀ᵐ ω ∂P, μ ω (frontier (closedSquare (c - ⟨r, r⟩) (2 * r))) = 0 := by
  let B : Set ℂ := ball c (2 * R + 1)
  let ν : Ω → Measure ℂ := fun ω => normalizedRestriction (μ ω) B
  have hν : AEMeasurable ν P :=
    (measurable_normalizedRestriction_measure B measurableSet_ball).comp_aemeasurable hμ
  have hbound : ∀ᵐ ω ∂P, ν ω univ ≤ 1 := by
    apply Eventually.of_forall
    intro ω
    change (normalizedRestriction (μ ω) B) univ ≤ 1
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    by_cases hz : μ ω B = 0
    · simp [hz]
    by_cases ht : μ ω B = ∞
    · simp [ht]
    simp [ENNReal.inv_mul_cancel hz ht]
  obtain ⟨r, hr, hz⟩ := exists_ae_centered_square_null_frontier_of_bounded P ν hν hbound c hR
  have hsubset : frontier (closedSquare (c - ⟨r, r⟩) (2 * r)) ⊆ B := by
    intro x hx
    have hc : IsClosed (closedSquare (c - ⟨r, r⟩) (2 * r)) :=
      (IsClosed.reProdIm isClosed_Icc isClosed_Icc)
    have hx' := centered_closedSquare_subset_closedBall c (hc.frontier_subset hx)
    change dist x c < 2 * R + 1
    have hd : dist x c ≤ 2 * r := hx'
    linarith [hr.2]
  refine ⟨r, hr, ?_⟩
  filter_upwards [hz, hloc] with ω hzω hlocω
  let : IsLocallyFiniteMeasure (μ ω) := hlocω
  have hfin : μ ω B ≠ ∞ := measure_ball_lt_top.ne
  change normalizedRestriction (μ ω) B (frontier (closedSquare (c - ⟨r, r⟩) (2 * r))) = 0 at hzω
  simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply isClosed_frontier.measurableSet, inter_eq_left.mpr hsubset,
    mul_eq_zero, ENNReal.inv_ne_zero.mpr hfin, false_or] using hzω

/-- Every nonempty open set contains a positive-side square whose frontier
is almost surely null for a locally finite random measure. -/
theorem exists_ae_null_frontier_closedSquare_subset
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
      ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0 := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  obtain ⟨r, hr, hnull⟩ := exists_ae_centered_square_null_frontier P μ hμ hloc c
    (show 0 < R / 2 by positivity)
  refine ⟨c - ⟨r, r⟩, 2 * r, by linarith [hr.1], ?_, hnull⟩
  intro x hx
  apply hRU
  have hd : dist x c ≤ 2 * r := centered_closedSquare_subset_closedBall c hx
  change dist x c < R
  linarith [hr.2]

#print axioms exists_centered_square_null_frontier
#print axioms exists_ae_centered_square_null_frontier_of_bounded
#print axioms exists_ae_centered_square_null_frontier
#print axioms exists_ae_null_frontier_closedSquare_subset
end HarmonicBalls
