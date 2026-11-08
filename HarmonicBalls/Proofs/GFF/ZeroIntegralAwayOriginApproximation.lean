import HarmonicBalls.Defs.GFF
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity
import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2S
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Order.LiminfLimsup

/-! # Mean-zero test functions away from the origin

This file records the deterministic approximation needed for the dilation argument.
The imported covariance-linearity development uses Leonardo Bonanno's work via
the pinned Lattice-Probability dependency.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ContDiff Topology MeasureTheory

namespace HarmonicBalls

/-- The desired common deterministic approximation, with convergence for every
whole-plane GFF and every probability space. -/
def ZeroIntegralAwayOriginApproximation (φ : ℂ → ℝ) : Prop :=
  ∃ ψ : ℕ → ℂ → ℝ,
    (∀ n, IsTestFunction univ (ψ n)) ∧
    (∀ n, (∫ z, ψ n z) = 0) ∧
    (∀ n, (0 : ℂ) ∉ tsupport (ψ n)) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      Tendsto (fun n => ∫ sample, (hC sample (ψ n) - hC sample φ) ^ 2 ∂P)
        atTop (𝓝 0)

/-- A fixed smooth probability density supported away from zero. -/
theorem exists_testFunction_integral_one_away_origin :
    ∃ η : ℂ → ℝ, IsTestFunction univ η ∧ (∫ z, η z) = 1 ∧
      (0 : ℂ) ∉ tsupport η := by
  let b : ContDiffBump (2 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, subset_univ _⟩,
    b.integral_normed, ?_⟩
  rw [b.tsupport_normed_eq]
  simp [b, Metric.mem_closedBall, Complex.dist_eq]

/-- Cutting out the origin and subtracting the mass against an integral-one
test produces another mean-zero test supported away from the origin. -/
theorem cutout_corrected_test {φ η : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hη : IsTestFunction univ η)
    (hηone : (∫ z, η z) = 1) (hηzero : (0 : ℂ) ∉ tsupport η)
    (b : ContDiffBump (0 : ℂ)) :
    let cut : ℂ → ℝ := fun z => φ z * (1 - b z)
    let corrected : ℂ → ℝ := fun z => cut z - (∫ w, cut w) * η z
    IsTestFunction univ corrected ∧ (∫ z, corrected z) = 0 ∧
      (0 : ℂ) ∉ tsupport corrected ∧
      tsupport corrected ⊆ tsupport φ ∪ tsupport η := by
  dsimp only
  let cut : ℂ → ℝ := fun z => φ z * (1 - b z)
  have hcut_smooth : ContDiff ℝ ∞ cut := hφ.1.mul (contDiff_const.sub b.contDiff)
  have hcut_compact : HasCompactSupport cut := hφ.2.1.mul_right
  have hcut_int : Integrable cut := hcut_smooth.continuous.integrable_of_hasCompactSupport hcut_compact
  have hη_int : Integrable η := hη.1.continuous.integrable_of_hasCompactSupport hη.2.1
  have hcut_zero : (0 : ℂ) ∉ tsupport cut := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [b.eventuallyEq_one] with z hz
    simp [cut, hz]
  refine ⟨⟨hcut_smooth.sub (contDiff_const.mul hη.1),
    hcut_compact.sub hη.2.1.mul_left, subset_univ _⟩, ?_, ?_, ?_⟩
  · change (∫ z, cut z - (∫ w, cut w) * η z) = 0
    rw [integral_sub hcut_int (hη_int.const_mul _), integral_const_mul, hηone, mul_one, sub_self]
  · change (0 : ℂ) ∉ tsupport (fun z => cut z - (∫ w, cut w) * η z)
    intro hz
    rcases tsupport_sub _ _ hz with hz | hz
    · exact hcut_zero hz
    · exact hηzero (tsupport_mul_subset_right hz)
  · change tsupport (fun z => cut z - (∫ w, cut w) * η z) ⊆ _
    exact (tsupport_sub _ _).trans (union_subset_union
      tsupport_mul_subset_left tsupport_mul_subset_right)

/-- The mass removed by shrinking smooth cutoffs tends to zero. -/
theorem tendsto_integral_mul_shrinking_bump {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (b : ℕ → ContDiffBump (0 : ℂ))
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, φ z * b n z) atTop (𝓝 0) := by
  have hφint : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n z => φ z * b n z) (f := fun _ => (0 : ℝ)) (fun z => ‖φ z‖)
    (fun n => (hφ.1.continuous.mul (b n).continuous).aestronglyMeasurable)
    hφint.norm
    (fun n => Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (b n).nonneg]
      exact mul_le_of_le_one_right (abs_nonneg _) (b n).le_one)
    (by
      filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
      have hd : 0 < dist z 0 := dist_pos.mpr hz
      have he := hb.eventually (Iio_mem_nhds hd)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      simp [(b n).zero_of_le_dist (le_of_lt hn)])
  simpa using ht

/-- A sequence of smooth cutoffs shrinking to the origin. -/
def originShrinkingBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_right _ (by positivity)
    norm_num

/-- The outer radii of the standard cutoffs vanish. -/
theorem tendsto_originShrinkingBump_rOut :
    Tendsto (fun n => (originShrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa [originShrinkingBump, div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
      Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * 0)))

/-- The restoring coefficient for a mean-zero test tends to zero. -/
theorem tendsto_integral_cutout {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (hφzero : (∫ z, φ z) = 0) (b : ℕ → ContDiffBump (0 : ℂ))
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, φ z * (1 - b n z)) atTop (𝓝 0) := by
  have hi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hsub (n : ℕ) : (∫ z, φ z * (1 - b n z)) = -(∫ z, φ z * b n z) := by
    have heq : (fun z => φ z * (1 - b n z)) = fun z => φ z - φ z * b n z := by
      funext z
      ring
    have hmul : Integrable (fun z => φ z * b n z) :=
      (hφ.1.continuous.mul (b n).continuous).integrable_of_hasCompactSupport hφ.2.1.mul_right
    rw [heq, integral_sub hi hmul, hφzero, zero_sub]
  simp_rw [hsub]
  simpa using (tendsto_integral_mul_shrinking_bump hφ b hb).neg

/-- Mean-zero tests have a common-compactly-supported approximation away
from zero, converging pointwise away from zero and in planar L². -/
theorem exists_zeroIntegral_awayOrigin_pointwise {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : (∫ z, φ z) = 0) :
    ∃ ψ : ℕ → ℂ → ℝ, ∃ K : Set ℂ, IsCompact K ∧
      (∀ n, IsTestFunction univ (ψ n)) ∧
      (∀ n, (∫ z, ψ n z) = 0) ∧
      (∀ n, (0 : ℂ) ∉ tsupport (ψ n)) ∧
      (∀ n, tsupport (ψ n) ⊆ K) ∧
      (∀ z ≠ 0, Tendsto (fun n => ψ n z) atTop (𝓝 (φ z))) ∧
      Tendsto (fun n => ∫ z, (ψ n z - φ z) ^ 2) atTop (𝓝 0) := by
  obtain ⟨η, hη, hηone, hηzero⟩ := exists_testFunction_integral_one_away_origin
  let b := originShrinkingBump
  let cut : ℕ → ℂ → ℝ := fun n z => φ z * (1 - b n z)
  let ψ : ℕ → ℂ → ℝ := fun n z => cut n z - (∫ w, cut n w) * η z
  have htests := fun n => cutout_corrected_test hφ hη hηone hηzero (b n)
  have hmass : Tendsto (fun n => ∫ w, cut n w) atTop (𝓝 0) :=
    tendsto_integral_cutout hφ hφzero b tendsto_originShrinkingBump_rOut
  have hpoint (z : ℂ) (hz : z ≠ 0) : Tendsto (fun n => ψ n z) atTop (𝓝 (φ z)) := by
    have hd : 0 < dist z 0 := dist_pos.mpr hz
    have he := tendsto_originShrinkingBump_rOut.eventually (Iio_mem_nhds hd)
    have hcut : Tendsto (fun n => cut n z) atTop (𝓝 (φ z)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      simp [cut, b, (originShrinkingBump n).zero_of_le_dist (le_of_lt hn)]
    simpa [ψ] using hcut.sub (hmass.mul tendsto_const_nhds)
  refine ⟨ψ, tsupport φ ∪ tsupport η, hφ.2.1.union hη.2.1,
    fun n => (htests n).1, fun n => (htests n).2.1,
    fun n => (htests n).2.2.1, fun n => (htests n).2.2.2, ?_, ?_⟩
  · exact hpoint
  · have hmnorm : Tendsto (fun n => ‖∫ w, cut n w‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, norm_zero] using
        (continuous_norm.tendsto (0 : ℝ)).comp hmass
    obtain ⟨C, hC⟩ := hmnorm.bddAbove_range
    have hCbound (n : ℕ) : ‖∫ w, cut n w‖ ≤ C := hC ⟨n, rfl⟩
    let bound : ℂ → ℝ := fun z => (‖φ z‖ + C * ‖η z‖) ^ 2
    have hbound : Integrable bound := by
      have hc : HasCompactSupport (fun z => ‖φ z‖ + C * ‖η z‖) :=
        hφ.2.1.norm.add hη.2.1.norm.mul_left
      have hcs : HasCompactSupport bound := by
        have heq : bound = (fun z : ℂ => ‖φ z‖ + C * ‖η z‖) *
            (fun z : ℂ => ‖φ z‖ + C * ‖η z‖) := by
          funext z
          simp [bound, pow_two]
        rw [heq]
        exact hc.mul_right
      exact ((hφ.1.continuous.norm.add (continuous_const.mul hη.1.continuous.norm)).pow 2
        ).integrable_of_hasCompactSupport hcs
    have hdom (n : ℕ) (z : ℂ) : ‖(ψ n z - φ z) ^ 2‖ ≤ bound z := by
      have hφb : ‖φ z * b n z‖ ≤ ‖φ z‖ := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (b n).nonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) (b n).le_one
      have hηb : ‖(∫ w, cut n w) * η z‖ ≤ C * ‖η z‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hCbound n) (norm_nonneg _)
      have hid : ψ n z - φ z = -(φ z * b n z) - (∫ w, cut n w) * η z := by
        dsimp [ψ, cut]
        ring
      have hn : ‖ψ n z - φ z‖ ≤ ‖φ z‖ + C * ‖η z‖ := by
        rw [hid]
        exact (norm_sub_le _ _).trans (by simpa using add_le_add hφb hηb)
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hlim := tendsto_integral_of_dominated_convergence
      (F := fun n z => (ψ n z - φ z) ^ 2) (f := fun _ => (0 : ℝ)) bound
      (fun n => (((htests n).1.1.continuous.sub hφ.1.continuous).pow 2).aestronglyMeasurable)
      hbound (fun n => Filter.Eventually.of_forall (hdom n))
      (by
        filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
        simpa using ((hpoint z hz).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => φ z) atTop (𝓝 (φ z)))).pow 2)
    simpa using hlim

/-- The actual squared difference of two GFF pairings equals the covariance
energy of their difference, without selecting a samplewise linear version. -/
theorem IsWholePlaneGFF.integral_pairing_sub_sq_eq_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ) :
    (∫ sample, (hC sample ψ - hC sample φ) ^ 2 ∂P) =
      wholePlaneGFFCov (.pairing (fun z => ψ z - φ z))
        (.pairing (fun z => ψ z - φ z)) := by
  let δ : ℂ → ℝ := fun z => ψ z - φ z
  have hδ : IsTestFunction univ δ := by
    simpa [δ, sub_eq_add_neg] using hψ.const_mul_add_const_mul hφ 1 (-1)
  have hlin : ∀ᵐ sample ∂P, hC sample δ = hC sample ψ - hC sample φ := by
    filter_upwards [h.ae_pairing_linear_combination hψ hφ 1 (-1)] with sample hs
    simpa [δ, sub_eq_add_neg] using hs
  have hmean : (∫ sample, hC sample δ ∂P) = 0 := h.integral_eq_zero (.pairing δ) hδ
  have hmeas : AEMeasurable (fun sample => hC sample δ) P :=
    (h.measurable_pairing δ hδ).aemeasurable
  have hc := h.covariance_eq (.pairing δ) (.pairing δ) hδ hδ
  calc
    (∫ sample, (hC sample ψ - hC sample φ) ^ 2 ∂P) =
        ∫ sample, (hC sample δ) ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [hlin] with sample hs
          rw [hs]
    _ = variance (fun sample => hC sample δ) P := by
      rw [variance_eq_integral hmeas, hmean]
      simp
    _ = wholePlaneGFFCov (.pairing δ) (.pairing δ) := by
      rw [← covariance_self hmeas]
      exact hc

/-- On mean-zero tests supported in a fixed ball, the squared pairing
difference is bounded by a constant times the planar squared norm. -/
theorem IsWholePlaneGFF.integral_pairing_sub_sq_le_schur
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hφzero : (∫ z, φ z) = 0) (hψzero : (∫ z, ψ z) = 0)
    {R : ℝ} (hR : 0 ≤ R) (hRsupport : ∀ z, R < ‖z‖ → ψ z - φ z = 0) :
    (∫ sample, (hC sample ψ - hC sample φ) ^ 2 ∂P) ≤
      2 * (2 * R * (Real.pi * (2 * R) ^ 2) + LQGMetric.logBallConst) *
        ∫ z, (ψ z - φ z) ^ 2 := by
  let δ : ℂ → ℝ := fun z => ψ z - φ z
  have hδ : IsTestFunction univ δ := by
    simpa [δ, sub_eq_add_neg] using hψ.const_mul_add_const_mul hφ 1 (-1)
  have hδzero : (∫ z, δ z) = 0 := by
    dsimp [δ]
    rw [integral_sub (hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1)
      (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1), hψzero, hφzero, sub_self]
  let test : LQGMetric.TestC0 := ⟨⟨δ, hδ.1, hδ.2.1, hδ.2.2⟩, hδzero⟩
  rw [h.integral_pairing_sub_sq_eq_covariance hφ hψ]
  change wholePlaneGFFCov (.pairing test.1) (.pairing test.1) ≤ _
  rw [Section6.wholePlaneGFFCov_pairing_eq_logCov test test]
  exact LQGMetric.MarkovGermVer.logCov_self_le_schur hR hδ.1.continuous hRsupport

/-- Every mean-zero test has a deterministic away-origin approximation in
the actual second moment of every normalized whole-plane GFF. -/
theorem zeroIntegralAwayOriginApproximation {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : (∫ z, φ z) = 0) :
    ZeroIntegralAwayOriginApproximation φ := by
  obtain ⟨ψ, K, hK, hψ, hψzero, hψaway, hψK, hpoint, hL2⟩ :=
    exists_zeroIntegral_awayOrigin_pointwise hφ hφzero
  obtain ⟨R, hR⟩ := (hK.union hφ.2.1).isBounded.subset_closedBall (0 : ℂ)
  let S := max R 0
  have hS : 0 ≤ S := le_max_right _ _
  have hsupp (n : ℕ) (z : ℂ) (hz : S < ‖z‖) : ψ n z - φ z = 0 := by
    have hout : z ∉ K ∪ tsupport φ := by
      intro hzmem
      have hzR := hR hzmem
      simp only [mem_closedBall, dist_zero_right] at hzR
      exact (not_le_of_gt hz) (hzR.trans (le_max_left _ _))
    have hψout : z ∉ tsupport (ψ n) := fun hzmem => hout (Or.inl (hψK n hzmem))
    have hφout : z ∉ tsupport φ := fun hzmem => hout (Or.inr hzmem)
    rw [image_eq_zero_of_notMem_tsupport hψout, image_eq_zero_of_notMem_tsupport hφout,
      sub_self]
  refine ⟨ψ, hψ, hψzero, hψaway, ?_⟩
  intro Ω inst P instP hC hcirc h
  have hbound : Tendsto (fun n =>
      (2 * (2 * S * (Real.pi * (2 * S) ^ 2) + LQGMetric.logBallConst)) *
        ∫ z, (ψ n z - φ z) ^ 2) atTop (𝓝 0) := by
    simpa using hL2.const_mul
      (2 * (2 * S * (Real.pi * (2 * S) ^ 2) + LQGMetric.logBallConst))
  exact squeeze_zero (fun n => integral_nonneg fun sample => sq_nonneg _)
    (fun n => h.integral_pairing_sub_sq_le_schur hφ (hψ n) hφzero (hψzero n) hS
      (hsupp n)) hbound

#print axioms exists_testFunction_integral_one_away_origin
#print axioms cutout_corrected_test
#print axioms tendsto_integral_mul_shrinking_bump
#print axioms tendsto_originShrinkingBump_rOut
#print axioms tendsto_integral_cutout
#print axioms exists_zeroIntegral_awayOrigin_pointwise
#print axioms IsWholePlaneGFF.integral_pairing_sub_sq_eq_covariance
#print axioms IsWholePlaneGFF.integral_pairing_sub_sq_le_schur
#print axioms zeroIntegralAwayOriginApproximation

end HarmonicBalls
