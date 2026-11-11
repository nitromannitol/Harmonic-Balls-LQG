import HarmonicBalls.Proofs.Sec6.AnnularCircleDensity
import HarmonicBalls.Proofs.Sec6.AnnulusFrontierAffine
import HarmonicBalls.Proofs.Sec6.GoodAnnulusCenteredExhaustion
import HarmonicBalls.Proofs.Sec8.OpenBallDensity

/-! # Centered circle averages on an annular exhaustion

The imported Section 8 frequency argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- A buffered annular continuity exhaustion admits jointly local centered
circle-average versions at every dyadic scale. Initial stages are empty until
the reference circle fits inside the annulus. -/
theorem IsWholePlaneGFF.exists_centered_lqg_annular_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (z : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus z r R)) = 0)
    (a : ℂ) (ha : a ∈ annulus z r R) :
    ∃ (E : ℕ → Set ℂ) (d : ℕ → Ω → ℂ → ℝ),
      (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
      (⋃ n, E n) = annulus z r R ∧ Bornology.IsBounded (⋃ n, E n) ∧
      (∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
        μ ω (frontier (⋃ n, E n)) = 0) ∧
      (∀ n, @Measurable (Ω × ℂ) ℝ
        ((fieldSigmaAlgebraModConst 0 hC (annulus z r R)).prod inferInstance) _
        (Function.uncurry (d n))) ∧
      ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ E n,
        d n ω w = fieldCircleAverage 0 (hcirc ω) (dyadicScale n) w -
          fieldCircleAverage 0 (hcirc ω) (dyadicScale n) a := by
  classical
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  have hU : IsOpen (annulus z r R) := isOpen_ball.sdiff isClosed_closedBall
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU a ha
  have hlim : Tendsto dyadicScale atTop (𝓝 0) :=
    tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hδ))
  obtain ⟨F, hFo, hFm, hFu, hFb, hFbuffer, hFfront⟩ :=
    IsWholePlaneGFF.exists_buffered_lqg_annular_exhaustion P hgff hμ z hr hrR hfront
      dyadicScale hlim
  let E (n : ℕ) := if N ≤ n then F n else ∅
  have hEm : ∀ n, MeasurableSet (E n) := by
    intro n
    by_cases hn : N ≤ n <;> simp [E, hn, (hFo n).measurableSet]
  have hmono : Monotone E := by
    intro i j hij
    by_cases hi : N ≤ i
    · have hj := hi.trans hij
      simpa only [E, hi, hj, ↓reduceIte] using hFm hij
    · simp [E, hi, empty_subset]
  have hunion : (⋃ n, E n) = ⋃ n, F n := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      by_cases h : N ≤ n
      · exact ⟨n, by simpa [E, h] using hn⟩
      · simp [E, h] at hn
    · rintro ⟨n, hn⟩
      refine ⟨max N n, ?_⟩
      simpa [E, le_max_left] using hFm (le_max_right N n) hn
  have hbounded : Bornology.IsBounded (⋃ n, E n) := by simpa [hunion] using hFb
  have hfront' : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 := by
    filter_upwards [hFfront] with ω hω
    refine ⟨?_, by simpa [hunion] using hω.2⟩
    intro n
    by_cases hn : N ≤ n
    · simpa [E, hn] using hω.1 n
    · simp [E, hn, frontier_empty]
  have hlocal (n : ℕ) : ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((fieldSigmaAlgebraModConst 0 hC (annulus z r R)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ w ∈ E n,
        d ω w = fieldCircleAverage 0 (hcirc ω) (dyadicScale n) w -
          fieldCircleAverage 0 (hcirc ω) (dyadicScale n) a := by
    by_cases hn : N ≤ n
    · have ha' : closedBall a (dyadicScale n) ⊆ annulus z r R :=
        (closedBall_subset_ball (hN n hn)).trans hδU
      obtain ⟨d, hdm, hdeq⟩ := hgff.exists_joint_annular_centered_circle_version
        (α₀ := 0) (dyadicScale_pos n) (annulus z r R) hU a ha'
      refine ⟨d, hdm, ?_⟩
      filter_upwards [hdeq] with ω hω w hw
      apply hω w
      apply hFbuffer n w
      simpa [E, hn] using hw
    · refine ⟨fun _ _ => 0, measurable_const, ?_⟩
      filter_upwards with ω w hw
      simp [E, hn] at hw
  choose d hdm hdeq using hlocal
  exact ⟨E, d, hEm, hmono, hunion.trans hFu, hbounded, hfront', hdm, hdeq⟩

/-- A good-annulus event is local modulo constants for the field defining its
LQG measure, provided the annular boundary is null and the standard measure
and Brownian point-avoidance conditions hold. -/
theorem isFieldMeasurableModConst_goodAnnulus_of_null_frontier
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus z (3 * r) (5 * r))) = 0) :
    IsFieldMeasurableModConst P 0 hC (annulus z (3 * r) (5 * r))
      {ω | IsGoodAnnulus (μ ω) r z a b} := by
  have hanchor : z + ((4 * r : ℝ) : ℂ) ∈ annulus z (3 * r) (5 * r) := by
    have hdist : dist (z + ((4 * r : ℝ) : ℂ)) z = 4 * r := by
      simp [dist_eq_norm, hr.le]
    change dist (z + ((4 * r : ℝ) : ℂ)) z < 5 * r ∧
      ¬ dist (z + ((4 * r : ℝ) : ℂ)) z ≤ 3 * r
    rw [hdist]
    constructor <;> linarith
  obtain ⟨E, d, hEm, hmono, hE, hbounded, hEf, hdm, hdeq⟩ :=
    IsWholePlaneGFF.exists_centered_lqg_annular_exhaustion hgff hμ z (by positivity : 0 ≤ 3 * r)
      (by linarith : 3 * r < 5 * r) hfront _ hanchor
  exact isFieldMeasurableModConst_goodAnnulus_of_centered_exhaustion hgff hμ _
    ((fieldSigmaAlgebraModConst_le 0 hC _).trans (hgff.fieldSigmaAlgebra_le 0 _))
    hr z ha b hatom hfinite hpositive hpolar E hEm hmono hbounded hE hEf _ d hdm hdeq

/-- The affine GFF and coordinate-change laws imply good-annulus
locality once nonatomicity, finite positive annular mass and Brownian point
avoidance are available. -/
theorem isFieldMeasurableModConst_goodAnnulus_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IsFieldMeasurableModConst P 0 hC (annulus z (3 * r) (5 * r))
      {ω | IsGoodAnnulus (μ ω) r z a b} := by
  apply isFieldMeasurableModConst_goodAnnulus_of_null_frontier hgff hμ hr z ha b
    hatom hfinite hpositive hpolar
  exact ae_lqg_annulus_frontier_eq_zero_of_affine hgff hμ hAff hCC hγ hγ2 z
    (by positivity) (by positivity)

end HarmonicBalls.Section6
