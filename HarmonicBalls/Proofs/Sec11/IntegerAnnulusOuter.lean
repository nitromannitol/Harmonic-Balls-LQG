import HarmonicBalls.Steps.Sec11.OuterAnnulusDilation
import HarmonicBalls.Proofs.Sec11.IntegerAnnulusMass

/-!
# Outer odometer estimates at all integer radii

The affine invariance and coordinate-change inputs are staged in
`HarmonicBalls.Proposed.LQG` and remain pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Section6

universe u

/-- Lemma 6.10 transfers simultaneously to all positive integer disks,
with annuli and centers expressed in unit-disk coordinates. -/
theorem integer_annulus_odometer_bound_of_scaledField
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
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
        annulus z (3 * r) (6 * r) ⊆ ball 0 1 \ {p} →
        ((cluster (μ ω) n ((n : ℝ) • p) t)ᶜ ∩
          annulus ((n : ℝ) • z) ((n : ℝ) * (4 * r)) ((n : ℝ) * (5 * r))).Nonempty →
        (⨆ x ∈ annulus ((n : ℝ) • z) ((n : ℝ) * (4 * r)) ((n : ℝ) * (5 * r)),
            ENNReal.ofReal (odometer (μ ω) n ((n : ℝ) • p) t x)) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup (μ ω) ((n : ℝ) • z)
          ((n : ℝ) * (3 * r)) ((n : ℝ) * (6 * r)) := by
  obtain ⟨C, hCpos, hunit⟩ := h610 3 4 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
    filter_upwards [hu] with ω hu _
    intro p hp t ht r hr z hA hbad
    let c := (Real.exp (γ * (lqgQ γ * Real.log n +
      fieldCircleAverage α₀ (hcirc ω) n 0)))⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.exp_pos _)
    have hnorm : normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω) =
        ENNReal.ofReal c • Measure.map (fun x : ℂ => (n : ℝ)⁻¹ • x) (μ ω) := by
      simp [normalizedPullbackMeasure, c, ENNReal.ofReal_inv_of_pos, Real.exp_pos]
    have hinner : annulus z (4 * r) (5 * r) ⊆ annulus z (3 * r) (6 * r) := by
      intro x hx
      simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hx ⊢
      constructor <;> linarith [hx.1, hx.2]
    have hbad' : ((cluster (normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω))
        1 p (c * t))ᶜ ∩ annulus z (4 * r) (5 * r)).Nonempty := by
      obtain ⟨x, hxcluster, hxann⟩ := hbad
      refine ⟨(n : ℝ)⁻¹ • x, ?_, ?_⟩
      · rw [hnorm, cluster_comp_real_smul hk hc ht.le]
        simpa only [mem_compl_iff, mem_preimage, mul_one, smul_smul,
          mul_inv_cancel₀ hk.ne', one_smul] using hxcluster
      · apply (smul_mem_annulus_iff hk z ((n : ℝ)⁻¹ • x) (4 * r) (5 * r)).1
        simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hxann
    have hb := hu p hp (c * t) (mul_pos hc ht) r hr z hA hbad'
    rw [hnorm] at hb
    exact annulus_odometer_bound_of_scaled_unit_bound hk hc ht.le (hinner.trans hA) hb
  · exact Filter.Eventually.of_forall fun _ h => (hn h).elim

/-- The simultaneous integer-radius outer estimate in the original coordinates. -/
theorem integer_annulus_odometer_bound_of_scaledField_original
    (h610 : OdometerBoundByAnnulusMassStmt.{u})
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
        annulus z (3 * r) (6 * r) ⊆ ball 0 n \ {p} →
        ((cluster (μ ω) n p t)ᶜ ∩ annulus z (4 * r) (5 * r)).Nonempty →
        (⨆ x ∈ annulus z (4 * r) (5 * r),
            ENNReal.ofReal (odometer (μ ω) n p t x)) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r) := by
  obtain ⟨C, hCpos, hbound⟩ := integer_annulus_odometer_bound_of_scaledField h610 hAff hCC
  refine ⟨C, hCpos, ?_⟩
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro n hn p hp t ht r hr z hA hbad
  have hk : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp' : (n : ℝ)⁻¹ • p ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hp ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
    rw [← div_eq_inv_mul]
    exact (div_lt_one hk).2 hp
  have hA' : annulus ((n : ℝ)⁻¹ • z) (3 * ((n : ℝ)⁻¹ * r))
      (6 * ((n : ℝ)⁻¹ * r)) ⊆ ball 0 1 \ {(n : ℝ)⁻¹ • p} := by
    have h := inverse_smul_annulus_subset_unit hk hA
    simpa only [mul_left_comm ((n : ℝ)⁻¹) (3 : ℝ),
      mul_left_comm ((n : ℝ)⁻¹) (6 : ℝ)] using h
  have hmul (a : ℝ) : (n : ℝ) * (a * ((n : ℝ)⁻¹ * r)) = a * r := by
    calc
      _ = a * ((n : ℝ) * ((n : ℝ)⁻¹ * r)) := by ring
      _ = a * r := by simp [hk.ne']
  have hbad' : ((cluster (μ ω) n ((n : ℝ) • ((n : ℝ)⁻¹ • p)) t)ᶜ ∩
      annulus ((n : ℝ) • ((n : ℝ)⁻¹ • z))
        ((n : ℝ) * (4 * ((n : ℝ)⁻¹ * r)))
        ((n : ℝ) * (5 * ((n : ℝ)⁻¹ * r)))).Nonempty := by
    simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul, hmul] using hbad
  have hh := hω n hn ((n : ℝ)⁻¹ • p) hp' t ht ((n : ℝ)⁻¹ * r)
    (mul_pos (inv_pos.mpr hk) hr) ((n : ℝ)⁻¹ • z) hA' hbad'
  simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul, hmul] using hh

end HarmonicBalls
