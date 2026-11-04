import HarmonicBalls.Steps.Sec11.UnitAnnulusMass
import HarmonicBalls.Proofs.Sec9.BoundaryScaleField
import HarmonicBalls.Proofs.Sec3.OpenLaplacian

/-!
# Annulus mass estimates at all integer radii

The same universal constant works simultaneously at every positive integer
radius. The affine field invariance and coordinate-change inputs are staged
in `HarmonicBalls.Proposed.LQG` and remain pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Section6

universe u

/-- Lemma 6.8 transfers simultaneously to all positive integer disks, with
centers and annuli expressed in unit-disk coordinates. -/
theorem integer_annulus_mass_bound_of_scaledField
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∃ C : ℝ, 0 < C ∧
      ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ p ∈ ball (0 : ℂ) 1,
        ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        annulus z ((1 / 2) * r) (4 * r) ⊆ ball 0 1 \ {p} →
        μ ω (annulus ((n : ℝ) • z) ((n : ℝ) * r) ((n : ℝ) * (2 * r)) ∩
          cluster (μ ω) n ((n : ℝ) • p) t) ≤
        ENNReal.ofReal C * ⨆ x ∈ annulus ((n : ℝ) • z)
          ((n : ℝ) * ((1 / 2) * r)) ((n : ℝ) * (4 * r)),
            ENNReal.ofReal (odometer (μ ω) n ((n : ℝ) • p) t x) := by
  obtain ⟨C, hCpos, hunit⟩ := unit_annulus_mass_bound_of_lemma68 h68
  refine ⟨C, hCpos, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  rw [ae_all_iff]
  intro n
  by_cases hn : 0 < n
  · have hk : 0 < (n : ℝ) := by exact_mod_cast hn
    let hC' := affinePairing hC hcirc (n : ℂ) 0
    let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
      hcirc ω ((n : ℝ) * r) ((n : ℝ) • z) - hcirc ω n 0
    have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
      have hcirc_eq : hcirc' = affineCircle hcirc (n : ℂ) 0 := by
        funext ω r z
        simp [hcirc', affineCircle, Complex.real_smul]
      rw [hcirc_eq]
      exact hAff Ω P hC hcirc hGFF (n : ℂ) (by exact_mod_cast hn.ne') 0
    have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
        (fun ω => normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω)) := by
      exact isLQGMeasureOfField_normalizedPullback (hCC Ω P γ α₀ hC hcirc)
        hGFF hγ hγ2 hα hμ hk
    have hu := hunit γ α₀ hγ hγ2 hα Ω P hC' hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω)) hGFF' hμ'
    have ho := clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC' hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω)) hGFF' hμ'
    filter_upwards [hu, ho] with ω hu ho _
    intro p hp t ht r hr z hA
    let c := (Real.exp (γ * (lqgQ γ * Real.log n +
      fieldCircleAverage α₀ (hcirc ω) n 0)))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.exp_pos _)
    have hnorm : normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω) =
        ENNReal.ofReal c • Measure.map (fun x : ℂ => (n : ℝ)⁻¹ • x) (μ ω) := by
      simp [normalizedPullbackMeasure, c, ENNReal.ofReal_inv_of_pos, Real.exp_pos]
    have hcluster : MeasurableSet (cluster
        (ENNReal.ofReal c • Measure.map (fun x : ℂ => (n : ℝ)⁻¹ • x) (μ ω)) 1 p (c * t)) := by
      rw [← hnorm]
      exact (ho (c * t) 1 (mul_pos hc ht) zero_lt_one p hp).1.measurableSet
    have hb := hu p hp (c * t) (mul_pos hc ht) r hr z hA
    rw [hnorm] at hb
    exact annulus_mass_bound_of_scaled_unit_bound hk hc ht.le hcluster hA hb
  · exact Filter.Eventually.of_forall fun _ h => (hn h).elim

/-- Dilation into the unit disk preserves annulus containment and avoidance
of the pole. -/
theorem inverse_smul_annulus_subset_unit {k a b : ℝ} {z p : ℂ}
    (hk : 0 < k) (hA : annulus z a b ⊆ ball 0 k \ {p}) :
    annulus (k⁻¹ • z) (k⁻¹ * a) (k⁻¹ * b) ⊆ ball 0 1 \ {k⁻¹ • p} := by
  intro x hx
  have hxA : k • x ∈ annulus z a b := by
    have h := (smul_mem_annulus_iff hk (k⁻¹ • z) x (k⁻¹ * a) (k⁻¹ * b)).2 hx
    simpa [smul_smul, hk.ne', mul_assoc] using h
  have hx' := hA hxA
  constructor
  · have hxball := hx'.1
    rw [mem_ball_zero_iff] at hxball ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk] at hxball
    exact (mul_lt_mul_iff_left₀ hk).mp (by simpa [mul_comm] using hxball)
  · intro heq
    apply hx'.2
    have := congrArg (fun y : ℂ => k • y) heq
    simpa [smul_smul, hk.ne'] using this

/-- The simultaneous integer-radius estimate in the original coordinates. -/
theorem integer_annulus_mass_bound_of_scaledField_original
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h68 : AnnulusMassBoundByOdometerStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∃ C : ℝ, 0 < C ∧
      ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ p ∈ ball (0 : ℂ) n,
        ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        annulus z ((1 / 2) * r) (4 * r) ⊆ ball 0 n \ {p} →
        μ ω (annulus z r (2 * r) ∩ cluster (μ ω) n p t) ≤
        ENNReal.ofReal C * ⨆ x ∈ annulus z ((1 / 2) * r) (4 * r),
            ENNReal.ofReal (odometer (μ ω) n p t x) := by
  obtain ⟨C, hCpos, hbound⟩ := integer_annulus_mass_bound_of_scaledField hI2 h68 hAff hCC
  refine ⟨C, hCpos, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro n hn p hp t ht r hr z hA
  have hk : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp' : (n : ℝ)⁻¹ • p ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hp ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
    rw [← div_eq_inv_mul]
    exact (div_lt_one hk).2 hp
  have hA' : annulus ((n : ℝ)⁻¹ • z) ((1 / 2) * ((n : ℝ)⁻¹ * r))
      (4 * ((n : ℝ)⁻¹ * r)) ⊆ ball 0 1 \ {(n : ℝ)⁻¹ • p} := by
    have h := inverse_smul_annulus_subset_unit hk hA
    simpa only [mul_left_comm ((n : ℝ)⁻¹) (1 / 2 : ℝ),
      mul_left_comm ((n : ℝ)⁻¹) (4 : ℝ)] using h
  have hh := hω n hn ((n : ℝ)⁻¹ • p) hp' t ht ((n : ℝ)⁻¹ * r)
    (mul_pos (inv_pos.mpr hk) hr) ((n : ℝ)⁻¹ • z) hA'
  have hmul (a : ℝ) : (n : ℝ) * (a * ((n : ℝ)⁻¹ * r)) = a * r := by
    calc
      _ = a * ((n : ℝ) * ((n : ℝ)⁻¹ * r)) := by ring
      _ = a * r := by simp [hk.ne']
  have hbase : (n : ℝ) * ((n : ℝ)⁻¹ * r) = r := by simp [hk.ne']
  simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul, hmul, hbase] using hh

end HarmonicBalls
