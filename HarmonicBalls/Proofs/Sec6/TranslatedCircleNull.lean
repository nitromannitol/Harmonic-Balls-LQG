import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance
import HarmonicBalls.Proofs.Sec6.AnnulusFrontierAffine

/-! # Deterministic circles are null under translation invariance

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
A finite average and Fubini's theorem give one null circle of a prescribed
radius; translation invariance transfers this to every deterministic centre.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

/-- For a finite measure, almost every centre has a null circle of any fixed radius. -/
theorem ae_sphere_measure_eq_zero (m : Measure ℂ) [IsFiniteMeasure m] (r : ℝ) :
    ∀ᵐ z ∂volume, m (sphere z r) = 0 := by
  have hmeas : MeasurableSet {p : ℂ × ℂ | p.2 ∉ sphere p.1 r} := by
    apply MeasurableSet.compl
    exact measurableSet_eq_fun (continuous_snd.dist continuous_fst).measurable measurable_const
  have hx : ∀ᵐ x ∂m, ∀ᵐ z ∂volume, x ∉ sphere z r := by
    apply Eventually.of_forall
    intro x
    have hz : ∀ᵐ z ∂volume, z ∉ sphere x r := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using Measure.addHaar_sphere volume x r
    filter_upwards [hz] with z hz
    simpa only [mem_sphere, dist_comm] using hz
  have hz : ∀ᵐ z ∂volume, ∀ᵐ x ∂m, x ∉ sphere z r :=
    (Measure.ae_ae_comm hmeas).2 hx
  filter_upwards [hz] with z hz
  rw [ae_iff] at hz
  simpa only [not_not, ofPred_mem_eq] using hz

/-- A locally finite measurable random measure has a prescribed-radius circle
with a deterministic centre in the unit ball that is almost surely null. -/
theorem exists_ae_null_sphere_of_local_finiteness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    {r : ℝ} :
    ∃ z ∈ ball (0 : ℂ) 1, ∀ᵐ ω ∂P, μ ω (sphere z r) = 0 := by
  let B : Set ℂ := ball 0 (r + 2)
  let ν : Ω → Measure ℂ := fun ω => normalizedRestriction (μ ω) B
  have hν : AEMeasurable ν P :=
    (measurable_normalizedRestriction_measure B isOpen_ball.measurableSet).comp_aemeasurable hμ
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
  let : IsFiniteMeasure (P.bind ν) := isFiniteMeasure_bind_of_ae_univ_le_one P ν hν hbound
  obtain ⟨z, hz, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume (0 : ℂ) zero_lt_one).ne'
    ((ae_sphere_measure_eq_zero (P.bind ν) r).filter_mono (ae_mono Measure.restrict_le_self))
  refine ⟨z, hz, ?_⟩
  have hsubset : sphere z r ⊆ B := by
    intro x hx
    have hx' : dist x z = r := hx
    have hz' : dist z 0 < 1 := hz
    have ht := dist_triangle x z 0
    change dist x 0 < r + 2
    linarith
  have hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞ := by
    filter_upwards [hlocal] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    exact measure_ball_lt_top.ne
  have hnull := ae_measure_eq_zero_of_bind_eq_zero P ν hν isClosed_sphere.measurableSet hm
  filter_upwards [hnull, hfin] with ω hnull hfin
  change normalizedRestriction (μ ω) B (sphere z r) = 0 at hnull
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply isClosed_sphere.measurableSet, inter_eq_left.mpr hsubset,
    mul_eq_zero, ENNReal.inv_ne_zero.mpr hfin, false_or] at hnull
  exact hnull

/-- Every prescribed circle is LQG-null, using only affine
invariance of the field and translation covariance of the dyadic limit. -/
theorem ae_lqg_sphere_eq_zero_of_translation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (z : ℂ) (r : ℝ) :
    ∀ᵐ ω ∂P, μ ω (sphere z r) = 0 := by
  let := hgff.isProbabilityMeasure
  obtain ⟨w, _, hw⟩ := exists_ae_null_sphere_of_local_finiteness P μ
    (hgff.aemeasurable_lqgMeasure hμ) (hμ.mono fun _ h => h.isLocallyFiniteMeasure) (r := r)
  have hd := identDistrib_translateMeasure hgff hμ hAff (z - w)
  have hmeas : MeasurableSet {ν : Measure ℂ | ν (sphere w r) = 0} :=
    measurableSet_eq_fun (Measure.measurable_coe isClosed_sphere.measurableSet) measurable_const
  have hv := hd.ae_snd hmeas hw
  filter_upwards [hv] with ω hω
  have hs : affineMeasure γ hcirc μ 1 (z - w) ω (sphere w r) =
      ENNReal.ofReal (Real.exp (γ * (-(hcirc ω 1 (z - w))))) * μ ω (sphere z r) := by
    rw [affineMeasure, Measure.smul_apply, smul_eq_mul, map_affine_sphere _ one_ne_zero]
    simp
  rw [hs] at hω
  exact (mul_eq_zero.mp hω).resolve_left (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

/-- The boundary of a deterministic annulus is null without a measure
coordinate-change hypothesis. -/
theorem ae_lqg_annulus_frontier_eq_zero_of_translation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (z : ℂ) (r R : ℝ) :
    ∀ᵐ ω ∂P, μ ω (frontier (annulus z r R)) = 0 := by
  filter_upwards [ae_lqg_sphere_eq_zero_of_translation hgff hμ hAff z r,
    ae_lqg_sphere_eq_zero_of_translation hgff hμ hAff z R] with ω hrω hRω
  apply measure_mono_null _ (measure_union_null hRω hrω)
  have hsub := (frontier_inter_subset (ball z R) (closedBall z r)ᶜ).trans
    (union_subset_union inter_subset_left inter_subset_right)
  exact hsub.trans (union_subset_union frontier_ball_subset_sphere (by
    simpa only [frontier_compl] using (frontier_closedBall_subset_sphere (x := z) (ε := r))))

end HarmonicBalls.Section6
