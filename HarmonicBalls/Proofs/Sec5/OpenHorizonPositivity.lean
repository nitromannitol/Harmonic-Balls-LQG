import HarmonicBalls.Proofs.Sec5.OpenFirstContact
import HarmonicBalls.Proofs.Sec5.CenteredDiscLocality
import HarmonicBalls.Steps.Sec5.ClusterBounds
import HarmonicBalls.Proofs.Sec5.ClusterGeometricScaling
import HarmonicBalls.Proofs.Sec5.ContactScaledContinuity

/-! # Positive open-domain containment horizons near the origin -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology Pointwise

universe u

/-- The small-time cluster bound confines any regularized family to every
neighborhood of each centre in the half-disc, simultaneously for all centres
and all open neighborhoods. -/
theorem ae_regularizedFamily_small_open_neighborhoods
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ U : Set ℂ,
      IsOpen U → z ∈ U → ∃ t : ℝ, 0 < t ∧ closure (Λ ω z t) ⊆ U := by
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
        closure (cluster (μ ω) 1 z t) ⊆ ball z (((2 : ℝ)⁻¹ ^ n / 2) / 2) := by
    intro n
    have hr : ((2 : ℝ)⁻¹ ^ n / 2) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hp : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    have h := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ _ hr
    filter_upwards [h.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨(2 : ℝ)⁻¹ ^ m, by positivity, hm⟩
  filter_upwards [ae_all_iff.mpr hevent,
    ae_regularizedClusterFamily_centeredDisc_compatibility hI2 hγ hγ2 hα hGFF hμ Λ hΛ]
    with ω hsmall hcompat
  intro z hz U hU hzU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨T, hT, hbound⟩ := hsmall n
  let t : ℝ := T / 2
  have ht : 0 < t := half_pos hT
  have hcl := hbound t ⟨ht, (half_lt_self hT).le⟩ z hz
  have hinside : closure (cluster (μ ω) 1 z t) ⊆ ball (0 : ℂ) 1 := by
    intro x hx
    have hxz := hcl hx
    have htri := dist_triangle x z (0 : ℂ)
    have hp : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    simp only [dist_zero_right] at htri
    simp only [mem_ball, dist_zero_right] at hxz hz ⊢
    linarith
  have hsame := hcompat 1 one_pos z (ball_subset_ball (by norm_num) hz) t ht (Or.inr hinside)
  refine ⟨t, ht, ?_⟩
  rw [hsame]
  apply hcl.trans
  apply (ball_subset_ball ?_).trans hεU
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  linarith

/-- The field-local open-domain horizon is positive for every half-disc
centre in the domain. The locality input is proposed and awaits source review. -/
theorem exists_fieldLocal_open_horizons_positive_on_halfDisc
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      ∀ᵐ ω ∂P, ∀ z : U, (z : ℂ) ∈ ball (0 : ℂ) (1 / 2) →
        0 < H ω z ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (H ω z < ⊤ →
          (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty) := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_horizons_with_conditional_boundary_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, ae_regularizedFamily_small_open_neighborhoods
    hI2 h71 hγ hγ2 hα hGFF hμ hΛ] with ω hchar hsmall
  intro z hz
  obtain ⟨t, ht, hsub⟩ := hsmall z hz U hU z.property
  have hpos : 0 < H ω z := lt_trans (ENNReal.ofReal_pos.mpr ht) ((hchar z).1 t ht |>.mpr hsub)
  exact ⟨hpos, (hchar z).1, (hchar z).2 hpos⟩

/-- After scaling the unit-disc estimate, every centre has arbitrarily small
regularized clusters. The affine and coordinate-change inputs are proposed
and await source review. -/
theorem ae_regularizedFamily_small_open_neighborhoods_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∀ U : Set ℂ, IsOpen U → z ∈ U →
      ∃ t : ℝ, 0 < t ∧ closure (Λ ω z t) ⊆ U := by
  have hevent : ∀ n j : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
        closure (cluster (normalizedPullbackMeasure γ α₀ ((n : ℝ) + 1) (hcirc ω) (μ ω))
          1 z t) ⊆ ball z (((2 : ℝ)⁻¹ ^ j / 2) / 2) := by
    intro n j
    let k : ℝ := (n : ℝ) + 1
    have hk : 0 < k := by dsimp [k]; positivity
    let hC' := affinePairing hC hcirc (k : ℂ) 0
    let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
      hcirc ω (k * r) (k • z) - hcirc ω k 0
    have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
      have hcirc_eq : hcirc' = affineCircle hcirc (k : ℂ) 0 := by
        funext ω r z
        simp [hcirc', affineCircle, Complex.real_smul, abs_of_pos hk]
      rw [hcirc_eq]
      exact hAff hGFF (k : ℂ) (by exact_mod_cast hk.ne') 0
    have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
        (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) :=
      isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ hk
    have hr : ((2 : ℝ)⁻¹ ^ j / 2) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hp : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    have h := h71 γ α₀ hγ hγ2 hα Ω P hC' hcirc' _ hGFF' hμ' _ hr
    filter_upwards [h.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨(2 : ℝ)⁻¹ ^ m, by positivity, hm⟩
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hevent n)),
    ae_regularizedClusterFamily_centeredDisc_compatibility hI2 hγ hγ2 hα hGFF hμ Λ hΛ]
    with ω hsmall hcompat
  intro z U hU hzU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖z‖)
  let k : ℝ := (n : ℝ) + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hz : z ∈ ball (0 : ℂ) (k / 2) := by
    simp only [mem_ball, dist_zero_right]
    dsimp [k]
    linarith
  have hz' : k⁻¹ • z ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
    apply (inv_mul_lt_iff₀ hk).2
    linarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hε hk)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨T, hT, hbound⟩ := hsmall n j
  let c : ℝ := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0))
  have hc : 0 < c := Real.exp_pos _
  let t : ℝ := c * (T / 2)
  have ht : 0 < t := mul_pos hc (half_pos hT)
  have htdiv : t / c = T / 2 := by dsimp [t]; field_simp
  have hcl := hbound (T / 2) ⟨half_pos hT, (half_lt_self hT).le⟩ (k⁻¹ • z) hz'
  have hsmul : k • (k⁻¹ • z) = z := by rw [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  have hscale := cluster_normalizedPullback_smul (γ := γ) (α₀ := α₀) (R := 1)
    (hcirc := hcirc ω) (μ := μ ω) (z := k⁻¹ • z) hk ht.le
  change k • cluster (normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) 1 (k⁻¹ • z)
    (t / c) = cluster (μ ω) (k * 1) (k • (k⁻¹ • z)) t at hscale
  rw [htdiv, mul_one, hsmul] at hscale
  have hball : k • ball (k⁻¹ • z) (((2 : ℝ)⁻¹ ^ j / 2) / 2) =
      ball z (k * (((2 : ℝ)⁻¹ ^ j / 2) / 2)) := by
    change (fun x : ℂ => k • x) '' _ = _
    simpa only [hsmul, Real.norm_eq_abs, abs_of_pos hk] using
      (Metric.smul_image_ball hk.ne' (k⁻¹ • z) (((2 : ℝ)⁻¹ ^ j / 2) / 2))
  have hcl' : closure (cluster (μ ω) k z t) ⊆
      ball z (k * (((2 : ℝ)⁻¹ ^ j / 2) / 2)) := by
    rw [← hscale, closure_smul₀' hk.ne', ← hball]
    exact smul_set_mono hcl
  have hinside : closure (cluster (μ ω) k z t) ⊆ ball (0 : ℂ) k := by
    intro x hx
    have hxz := hcl' hx
    have htri := dist_triangle x z (0 : ℂ)
    have hp : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp' : k * (2 : ℝ)⁻¹ ^ j ≤ k := by nlinarith
    simp only [dist_zero_right] at htri
    simp only [mem_ball, dist_zero_right] at hxz hz ⊢
    nlinarith
  have hsame := hcompat k hk z (ball_subset_ball (by linarith : k / 2 ≤ k) hz) t ht (Or.inr hinside)
  refine ⟨t, ht, ?_⟩
  rw [hsame]
  apply hcl'.trans
  apply (ball_subset_ball ?_).trans hεU
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ j := by positivity
  have hj' : k * (2 : ℝ)⁻¹ ^ j < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hk).mp hj
  nlinarith

/-- Every open-domain containment horizon is positive; if finite, it is a
boundary-contact time. The field locality, affine invariance, and coordinate
change inputs are proposed and await source review. -/
theorem exists_fieldLocal_open_horizons_positive
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      ∀ᵐ ω ∂P, ∀ z : U, 0 < H ω z ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (H ω z < ⊤ →
          (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty) := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_horizons_with_conditional_boundary_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, ae_regularizedFamily_small_open_neighborhoods_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ hΛ] with ω hchar hsmall
  intro z
  obtain ⟨t, ht, hsub⟩ := hsmall z U hU z.property
  have hpos : 0 < H ω z := lt_trans (ENNReal.ofReal_pos.mpr ht) ((hchar z).1 t ht |>.mpr hsub)
  exact ⟨hpos, (hchar z).1, (hchar z).2 hpos⟩

/-- In a bounded open domain every centre has a positive finite field-local
horizon, bounded by the domain mass, and the family reaches the boundary at
that horizon. Proposed inputs await source review. -/
theorem exists_fieldLocal_bounded_open_horizons_positive
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      ∀ᵐ ω ∂P, ∀ z : U, 0 < H ω z ∧ H ω z ≤ μ ω U ∧ H ω z < ⊤ ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_horizons_with_boundary_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, ae_regularizedFamily_small_open_neighborhoods_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ hΛ] with ω hchar hsmall
  intro z
  obtain ⟨t, ht, hsub⟩ := hsmall z U hU z.property
  have hpos : 0 < H ω z := lt_trans (ENNReal.ofReal_pos.mpr ht) ((hchar z).2.2.1 t ht |>.mpr hsub)
  exact ⟨hpos, (hchar z).1, (hchar z).2.1, (hchar z).2.2.1, (hchar z).2.2.2 hpos⟩

end HarmonicBalls
