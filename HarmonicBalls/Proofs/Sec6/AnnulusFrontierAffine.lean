import HarmonicBalls.Proofs.Sec6.AffineMeasureLaw
import HarmonicBalls.Proofs.Sec8.RandomMeasureContinuitySets
import HarmonicBalls.Proofs.Sec6.BufferedExhaustion

/-! # Null frontiers of deterministic annuli

The conclusions use the staged whole-plane affine invariance and LQG
coordinate-change inputs explicitly.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

/-- The affine pushforward maps sphere masses to sphere masses. -/
theorem map_affine_sphere (m : Measure ℂ) {a : ℂ} (ha : a ≠ 0)
    (b w : ℂ) (r : ℝ) :
    (m.map fun x => (x - b) / a) (sphere w r) =
      m (sphere (a * w + b) (‖a‖ * r)) := by
  rw [Measure.map_apply (by fun_prop) isClosed_sphere.measurableSet]
  congr 1
  ext x
  simp only [mem_preimage, mem_sphere, dist_eq_norm]
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [show (x - b) / a - w = (x - (a * w + b)) / a by field_simp; ring, norm_div,
    div_eq_iff hna.ne', mul_comm r ‖a‖]

/-- Every deterministic positive-radius circle is LQG-null almost surely,
using whole-plane affine invariance and the LQG coordinate-change law. -/
theorem ae_lqg_sphere_eq_zero_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, μ ω (sphere z r) = 0 := by
  let := hgff.isProbabilityMeasure
  obtain ⟨ρ, hρ, hnull⟩ := hgff.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => 0) (fun _ => 1) (fun _ => 2) (by intro n; norm_num)
  let q : ℝ := ρ 0
  have hq : 0 < q := by dsimp [q]; linarith [(hρ 0).1]
  have hz : ∀ᵐ ω ∂P, μ ω (sphere 0 q) = 0 := by
    filter_upwards [hnull] with ω hω
    simpa only [frontier_ball (0 : ℂ) hq.ne', q] using hω 0
  let a : ℂ := ((r / q : ℝ) : ℂ)
  have haR : 0 < r / q := div_pos hr hq
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast haR.ne'
  have hnorm : ‖a‖ * q = r := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos haR]
    exact div_mul_cancel₀ r hq.ne'
  have hd := identDistrib_affineMeasure hgff hμ hAff hCC hγ hγ2 ha z
  have hmeas : MeasurableSet {ν : Measure ℂ | ν (sphere 0 q) = 0} :=
    measurableSet_eq_fun (Measure.measurable_coe isClosed_sphere.measurableSet) measurable_const
  have hv := hd.ae_snd hmeas hz
  filter_upwards [hv] with ω hω
  have hs : affineMeasure γ hcirc μ a z ω (sphere 0 q) =
      ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ‖a‖ z + lqgQ γ * Real.log ‖a‖)))) *
        μ ω (sphere z r) := by
    rw [affineMeasure, Measure.smul_apply, smul_eq_mul, map_affine_sphere _ ha]
    simp only [mul_zero, zero_add, hnorm]
  rw [hs] at hω
  exact (mul_eq_zero.mp hω).resolve_left (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

/-- The boundary of a deterministic annulus has zero LQG mass almost surely. -/
theorem ae_lqg_annulus_frontier_eq_zero_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    ∀ᵐ ω ∂P, μ ω (frontier (annulus z r R)) = 0 := by
  filter_upwards [ae_lqg_sphere_eq_zero_of_affine hgff hμ hAff hCC hγ hγ2 z hr,
    ae_lqg_sphere_eq_zero_of_affine hgff hμ hAff hCC hγ hγ2 z hR] with ω hrω hRω
  apply measure_mono_null _ (measure_union_null hRω hrω)
  have hsub := (frontier_inter_subset (ball z R) (closedBall z r)ᶜ).trans
    (union_subset_union inter_subset_left inter_subset_right)
  exact hsub.trans (union_subset_union frontier_ball_subset_sphere (by
    simpa only [frontier_compl] using (frontier_closedBall_subset_sphere (x := z) (ε := r))))

/-- The staged affine laws supply the frontier condition for a buffered
continuity-set exhaustion of a deterministic annulus. -/
theorem IsWholePlaneGFF.exists_buffered_lqg_annular_exhaustion_of_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ F : ℕ → Set ℂ, (∀ n, IsOpen (F n)) ∧ Monotone F ∧
      (⋃ n, F n) = annulus z r R ∧ Bornology.IsBounded (⋃ n, F n) ∧
      (∀ n x, x ∈ F n → closedBall x (ε n) ⊆ annulus z r R) ∧
      ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (F n)) = 0) ∧
        μ ω (frontier (⋃ n, F n)) = 0 := by
  let := hgff.isProbabilityMeasure
  apply IsWholePlaneGFF.exists_buffered_lqg_annular_exhaustion P hgff hμ z hr.le hrR
  · exact ae_lqg_annulus_frontier_eq_zero_of_affine hgff hμ hAff hCC hγ hγ2 z hr
      (lt_trans hr hrR)
  · exact hε

end HarmonicBalls.Section6
