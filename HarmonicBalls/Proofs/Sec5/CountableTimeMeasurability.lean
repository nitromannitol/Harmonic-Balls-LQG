import HarmonicBalls.Proofs.Sec5.ClusterMeasurability
import HarmonicBalls.Proofs.Sec5.ScalingMeasure

/-! # Countable time tests for cluster families -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped Pointwise

universe u

/-- The least supersolution decreases as the mass parameter increases,
off the pole. This comparison uses only the obstacle and its nonnegativity. -/
theorem leastSupersolution_antitone_time {μ : Measure ℂ} {r s t : ℝ} {z x : ℂ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    leastSupersolution μ r z t x ≤ leastSupersolution μ r z s x := by
  have hsub : supersolutions μ r z s ⊆ supersolutions μ r z t := by
    intro w hw
    refine ⟨hw.1, hw.2.1, fun y hy hyz => ?_⟩
    have hG := greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := r)) z y
    have h := hw.2.2 y hy hyz
    nlinarith
  apply csInf_le_csInf (bddBelow_supersolutions (μ := μ) (t := t) hx hxz)
    ((supersolutions_nonempty μ r z hs).image _)
  exact image_mono hsub

/-- Every point of a positive-time cluster already belongs to some cluster at
an earlier positive rational time. No regularity of the measure is needed. -/
theorem mem_cluster_exists_earlier_rat {μ : Measure ℂ} {r t : ℝ} {z x : ℂ}
    (ht : 0 < t) (hx : x ∈ cluster μ r z t) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < t ∧ x ∈ cluster μ r z q := by
  rcases (mem_cluster_iff.mp hx) with ⟨hxb, hcase⟩
  by_cases hxz : x = z
  · obtain ⟨q, hq0, hqt⟩ := exists_rat_btwn ht
    exact ⟨q, hq0, hqt, mem_cluster_iff.mpr ⟨hxb, Or.inl hxz⟩⟩
  · have hu := hcase.resolve_left hxz
    let G := greenFunction (ball (0 : ℂ) r) z x
    let v := leastSupersolution μ r z t x
    have hlt : -t * G < v := by
      dsimp [G, v, odometer] at *
      linarith
    have hopen : IsOpen {s : ℝ | -s * G < v} :=
      isOpen_lt (continuous_neg.mul continuous_const) continuous_const
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen t hlt
    obtain ⟨q, hqlo, hqt⟩ := exists_rat_btwn (max_lt ht (sub_lt_self t hε))
    have hq0 : 0 < (q : ℝ) := (le_max_left _ _).trans_lt hqlo
    have hqnear : (q : ℝ) ∈ ball t ε := by
      rw [mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      have hqlo' : t - ε < (q : ℝ) := (le_max_right _ _).trans_lt hqlo
      constructor <;> linarith
    have hqv : -(q : ℝ) * G < v := hεsub hqnear
    have hcomp := leastSupersolution_antitone_time (μ := μ) (r := r) (z := z) (x := x)
      hq0.le hqt.le (ball_subset_closedBall hxb) hxz
    refine ⟨q, hq0, hqt, ?_⟩
    apply mem_cluster_iff.mpr
    refine ⟨hxb, Or.inr ?_⟩
    dsimp [G, v, odometer] at *
    linarith

/-- A positive-time family reconstructed from its rational-time clusters. -/
def rationalTimeClusterFamily (ν : Measure ℂ)
    (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) : Set ℂ :=
  {x | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < p.2 ∧ x ∈ cluster ν 1 p.1 q}

/-- The rational-time decoder is measurable if each rational-time point
test is measurable as a function of the measure. -/
theorem measurable_rationalTimeClusterFamily
    (htest : ∀ z ∈ ball (0 : ℂ) 1, ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (x : ℂ),
      Measurable (fun ν : Measure ℂ => x ∈ cluster ν 1 z q)) :
    Measurable rationalTimeClusterFamily := by
  apply Measurable.of_eval
  intro p
  apply Measurable.of_eval
  intro x
  change Measurable (fun ν : Measure ℂ => ∃ q : ℚ,
    0 < (q : ℝ) ∧ (q : ℝ) < p.2 ∧ x ∈ cluster ν 1 p.1 q)
  apply Measurable.exists
  intro q
  by_cases hq : 0 < (q : ℝ)
  · exact measurable_const.and (measurable_const.and (htest p.1 p.1.property q hq x))
  · simp only [hq, false_and]
    exact measurable_const

/-- Monotonicity identifies the rational decoder with the full cluster
family, simultaneously in centres and times. -/
theorem rationalTimeClusterFamily_eq (ν : Measure ℂ)
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → ∀ z ∈ ball (0 : ℂ) 1,
      cluster ν 1 z s ⊆ cluster ν 1 z t) :
    rationalTimeClusterFamily ν = fun p => cluster ν 1 p.1 p.2 := by
  funext p
  ext x
  constructor
  · rintro ⟨q, hq0, hqt, hx⟩
    exact hmono q p.2 hq0 hqt.le p.1 p.1.property hx
  · intro hx
    exact mem_cluster_exists_earlier_rat p.2.property hx

/-- Joint scale invariance follows from rational-time point tests, the
numbered monotonicity result, and the two staged field inputs. -/
theorem jointClusterScaleInvariance_of_rational_tests
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h33 : ClusterMonotoneStmt.{u})
    (htest : ∀ z ∈ ball (0 : ℂ) 1, ∀ (q : ℚ), 0 < (q : ℝ) → ∀ (x : ℂ),
      Measurable (fun ν : Measure ℂ => x ∈ cluster ν 1 z q))
    {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) => cluster (μ ω) 1 p.1 p.2)
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) =>
        k⁻¹ • cluster (μ ω) k (k • (p.1 : ℂ))
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) P P := by
  let C := fun (ω : Ω) (φ : ℂ → ℝ) => (k ^ 2)⁻¹ * hC ω (fun y => φ (y / (k : ℂ))) -
    hcirc ω k 0 * ∫ x, φ x
  let circ := fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0
  let ν := fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)
  have hGFFscaled : IsWholePlaneGFF P C circ := by
    have hh := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
    simpa only [C, circ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hk, Complex.real_smul, add_zero, sub_zero] using hh
  have hν : IsLQGMeasureOfField P γ α₀ circ ν :=
    isLQGMeasureOfField_normalizedPullback hCC h hγ hγ2 hα hμ hk
  have hfirst : (fun ω => rationalTimeClusterFamily (μ ω)) =ᵐ[P]
      (fun ω p => cluster (μ ω) 1 p.1 p.2) := by
    filter_upwards [h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hω
    exact rationalTimeClusterFamily_eq (μ ω) (fun s t hs hst z hz =>
      hω s t 1 hs hst zero_lt_one z hz)
  have hsecond : (fun ω => rationalTimeClusterFamily (ν ω)) =ᵐ[P]
      (fun ω p => k⁻¹ • cluster (μ ω) k (k • (p.1 : ℂ))
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) := by
    filter_upwards [h33 γ α₀ hγ hγ2 hα Ω P C circ ν hGFFscaled hν,
      clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ k hk] with ω hω hscale
    rw [rationalTimeClusterFamily_eq (ν ω) (fun s t hs hst z hz =>
      hω s t 1 hs hst zero_lt_one z hz)]
    funext p
    exact hscale p.1 p.1.property p.2 p.2.property
  have hd := (h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk).comp
    (measurable_rationalTimeClusterFamily htest)
  exact (IdentDistrib.of_ae_eq hd.aemeasurable_fst hfirst).symm.trans
    (hd.trans (IdentDistrib.of_ae_eq hd.aemeasurable_snd hsecond))

end HarmonicBalls
