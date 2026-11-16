import HarmonicBalls.Proofs.Potential.LQGFineScaleGrid
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.LQG.NormalizedCircleAllScales

/-! # Compact circle-average upper bounds

Dyadic circle averages of a whole-plane field admit simultaneous spatial bounds.
-/

noncomputable section
open MeasureTheory Filter Set Metric LatticeProb.LQG

namespace HarmonicBalls

/-- The circle averages of a rescaled field satisfy a dyadic upper bound on a
fixed disk, with the random recentering retained. -/
theorem IsWholePlaneGFF.ae_affine_dyadic_circle_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ k z, z ∈ ball (0 : ℂ) (1 / 4 : ℝ) →
      hcirc ω (a * LatticeProb.LQG.dyadicScale k) ((a : ℂ) * z) - hcirc ω a 0 ≤
        C + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  let H : Ω → ℝ → ℂ → ℝ := fun ω => affineRecentredCircle (hcirc ω) a 0
  have h := LatticeProb.LQG.AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hlp
    (a : ℂ) (Complex.ofReal_ne_zero.2 ha.ne') 0
  have heq : (fun ω r w => hcirc ω (‖(a : ℂ)‖ * r) ((a : ℂ) * w + 0) -
      hcirc ω ‖(a : ℂ)‖ 0) = H := by
    funext ω r w
    simp [H, affineRecentredCircle, Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [heq] at h
  let hCnew : Ω → (ℂ → ℝ) → ℝ := fun ω φ =>
    (‖(a : ℂ)‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - 0) / (a : ℂ))) -
      hcirc ω ‖(a : ℂ)‖ 0 * ∫ x, φ x
  have hHB : IsWholePlaneGFF P hCnew H := (LPBridge.isWholePlaneGFF_iff P hCnew H).mpr h
  obtain ⟨K, hKc, _, _, hK⟩ := hHB.exists_continuous_circle_version
  have hcoord : ∀ r, 0 < r → ∀ z, (fun ω => K r z ω) =ᵐ[P]
      fun ω => LQGMetric.circleAvg (reconstructedGFF hCnew ω) r z := by
    intro r hr z
    filter_upwards [hK r hr z, hHB.ae_circleAvg_reconstructedGFF hr z] with ω hk ha
    exact hk.trans ha
  have hbound := LatticeProb.LQG.ae_exists_all_dyadic_circle_le_of_normalized_gff
    hHB.reconstructedGFF_normalized (c := fun ω r z => K r z ω) hKc hcoord hδ
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num) (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
  let F : Ω → C(CircleParameter, ℝ) := fun ω =>
    ⟨fun p => K p.1 p.2 ω, continuousOn_univ.mp ((hKc ω).comp
      (continuous_subtype_val.prodMap continuous_id).continuousOn
      (by intro p hp; exact ⟨p.1.2, mem_univ _⟩))⟩
  have hraw : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = H ω p.1 p.2 :=
    hHB.ae_circle_map_eq_raw (fun p => hK p.1 p.1.2 p.2)
  filter_upwards [hbound, hraw] with ω hω hωraw
  obtain ⟨C, hC, hCbound⟩ := hω
  refine ⟨C, hC, fun k z hz => ?_⟩
  have hk := hCbound k z hz
  have hkpos : 0 < LatticeProb.LQG.dyadicScale k := by
    unfold LatticeProb.LQG.dyadicScale
    positivity
  change F ω (⟨_, hkpos⟩, z) ≤ _ at hk
  rw [hωraw (⟨_, hkpos⟩, z)] at hk
  simpa [H, affineRecentredCircle] using hk



/-- A dyadic dilation transfers the spatial circle bound to original coordinates. -/
theorem IsWholePlaneGFF.ae_dyadic_circle_le_on_disk
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {δ R : ℝ} (hδ : 0 < δ)
    (N : ℕ) (hR : R < (LatticeProb.LQG.dyadicScale N)⁻¹ / 4) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ k z, ‖z‖ ≤ R →
      hcirc ω (LatticeProb.LQG.dyadicScale k) z ≤
        C + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ := by
  let d := LatticeProb.LQG.dyadicScale N
  have hd : 0 < d := by unfold d LatticeProb.LQG.dyadicScale; positivity
  have hbound := hh.ae_affine_dyadic_circle_le (inv_pos.mpr hd) hδ
  filter_upwards [hbound] with ω hω
  obtain ⟨C, hC, hCbound⟩ := hω
  refine ⟨max 0 (C + hcirc ω d⁻¹ 0 + (2 + δ) * (N : ℝ) * Real.log 2),
    le_max_left _ _, ?_⟩
  intro k z hz
  have hz' : (d : ℂ) * z ∈ ball (0 : ℂ) (1 / 4 : ℝ) := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.le]
    have : d * R < 1 / 4 := by
      have ht := mul_lt_mul_of_pos_left hR hd
      change d * R < d * (d⁻¹ / 4) at ht
      have he : d * (d⁻¹ / 4) = 1 / 4 := by field_simp
      rwa [he] at ht
    exact (mul_le_mul_of_nonneg_left hz hd.le).trans_lt this
  have hk := hCbound (k + N) ((d : ℂ) * z) hz'
  have hscale : d⁻¹ * LatticeProb.LQG.dyadicScale (k + N) =
      LatticeProb.LQG.dyadicScale k := by
    rw [LatticeProb.LQG.dyadicScale_add]
    change d⁻¹ * (LatticeProb.LQG.dyadicScale k * d) = _
    field_simp
  have hcenter : ((d⁻¹ : ℝ) : ℂ) * ((d : ℂ) * z) = z := by
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hd.ne', Complex.ofReal_one, one_mul]
  rw [hscale, hcenter] at hk
  have hlog : Real.log (LatticeProb.LQG.dyadicScale (k + N))⁻¹ =
      Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ + (N : ℝ) * Real.log 2 := by
    simp only [LatticeProb.LQG.dyadicScale, pow_add, mul_inv_rev, inv_pow, inv_inv]
    rw [Real.log_mul (by positivity : (2 : ℝ) ^ N ≠ 0)
      (by positivity : (2 : ℝ) ^ k ≠ 0), Real.log_pow, Real.log_pow]
    ring
  rw [hlog] at hk
  have := le_max_right (0 : ℝ) (C + hcirc ω d⁻¹ 0 + (2 + δ) * (N : ℝ) * Real.log 2)
  nlinarith



/-- For every bounded set of centers, dyadic circle averages satisfy the
upper bound simultaneously on one event. -/
theorem IsWholePlaneGFF.ae_compact_dyadic_circle_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k z, ‖z‖ ≤ R →
      hcirc ω (LatticeProb.LQG.dyadicScale k) z ≤
        C + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ := by
  have he : ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k z,
      ‖z‖ ≤ (LatticeProb.LQG.dyadicScale N)⁻¹ / 8 →
      hcirc ω (LatticeProb.LQG.dyadicScale k) z ≤
        C + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ := by
    apply ae_all_iff.mpr
    intro N
    apply hh.ae_dyadic_circle_le_on_disk hδ N
    have hd : 0 < (LatticeProb.LQG.dyadicScale N)⁻¹ := by
      apply inv_pos.mpr
      unfold LatticeProb.LQG.dyadicScale
      positivity
    linarith
  filter_upwards [he] with ω hω R
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually_gt_atTop (8 * R)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht
  have hR : R ≤ (LatticeProb.LQG.dyadicScale N)⁻¹ / 8 := by
    have hp := hN N le_rfl
    simp only [LatticeProb.LQG.dyadicScale, inv_pow, inv_inv]
    linarith
  obtain ⟨C, hC, hbound⟩ := hω N
  exact ⟨C, hC, fun k z hz => hbound k z (hz.trans hR)⟩



/-- The affine recentering error has a uniform dyadic power bound on
bounded sets of centers. -/
theorem IsWholePlaneGFF.ae_compact_affine_circle_error_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ k z, ‖z‖ ≤ R →
      LQGDyadicScaling.dyadicFactor γ (k + 2) (hcirc ω (LatticeProb.LQG.dyadicScale (k + 2)) z) *
        ENNReal.ofReal (Real.exp (γ * affineRecentredCircle (hcirc ω)
          (LatticeProb.LQG.dyadicScale (k + 2)) z 4 0)) ≤
      ENNReal.ofReal (C * LatticeProb.LQG.dyadicScale (k + 2) ^
        (2 + γ ^ 2 / 2 - γ * (2 + δ))) := by
  filter_upwards [hh.ae_compact_dyadic_circle_le hδ] with ω hω R
  obtain ⟨B, hB, hbound⟩ := hω R
  refine ⟨Real.exp (γ * B), Real.exp_pos _, ?_⟩
  intro k z hz
  rw [dyadicFactor_mul_affine_circle_exp]
  have hd : 0 < LatticeProb.LQG.dyadicScale (k + 2) := by unfold LatticeProb.LQG.dyadicScale; positivity
  have hscale : LatticeProb.LQG.dyadicScale (k + 2) * 4 = LatticeProb.LQG.dyadicScale k := by
    rw [LatticeProb.LQG.dyadicScale_add_two]
    ring
  have hlog : Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ ≤
      Real.log (LatticeProb.LQG.dyadicScale (k + 2))⁻¹ := by
    simp only [LatticeProb.LQG.dyadicScale, LatticeProb.LQG.dyadicScale, inv_pow, inv_inv, Real.log_pow,
      Nat.cast_add, Nat.cast_ofNat]
    have hp : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith
  have hhbound := hbound k z hz
  have hcircle : hcirc ω (LatticeProb.LQG.dyadicScale (k + 2) * 4) z ≤
      B + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale (k + 2))⁻¹ := by
    rw [hscale]
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 + δ by linarith)
    linarith
  apply ENNReal.ofReal_le_ofReal
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcircle hγ.le)
  calc
    LatticeProb.LQG.dyadicScale (k + 2) ^ (2 + γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (LatticeProb.LQG.dyadicScale (k + 2) * 4) z)
        ≤ LatticeProb.LQG.dyadicScale (k + 2) ^ (2 + γ ^ 2 / 2) *
          Real.exp (γ * (B + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale (k + 2))⁻¹)) := by
            gcongr
    _ = Real.exp (γ * B) * LatticeProb.LQG.dyadicScale (k + 2) ^
          (2 + γ ^ 2 / 2 - γ * (2 + δ)) := by
      rw [Real.rpow_def_of_pos hd, Real.rpow_def_of_pos hd, ← Real.exp_add, ← Real.exp_add,
        Real.log_inv]
      congr 1
      ring



/-- In the subcritical range the affine recentering error has a positive
dyadic power uniformly on bounded sets of centers. -/
theorem IsWholePlaneGFF.ae_compact_affine_circle_error_positive_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ k z, ‖z‖ ≤ R →
      LQGDyadicScaling.dyadicFactor γ (k + 2)
          (hcirc ω (LatticeProb.LQG.dyadicScale (k + 2)) z) *
        ENNReal.ofReal (Real.exp (γ * affineRecentredCircle (hcirc ω)
          (LatticeProb.LQG.dyadicScale (k + 2)) z 4 0)) ≤
      ENNReal.ofReal (C * LatticeProb.LQG.dyadicScale (k + 2) ^ κ) := by
  let δ : ℝ := (2 - γ) ^ 2 / (4 * γ)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hκ : 0 < 2 + γ ^ 2 / 2 - γ * (2 + δ) := by
    dsimp [δ]
    have hs : 0 < (2 - γ) ^ 2 := sq_pos_of_pos (by linarith)
    have he : γ * ((2 - γ) ^ 2 / (4 * γ)) = (2 - γ) ^ 2 / 4 := by
      field_simp
    rw [mul_add, he]
    nlinarith
  filter_upwards [hh.ae_compact_affine_circle_error_le hγ hδ] with ω hω R
  obtain ⟨C, hC, hbound⟩ := hω R
  exact ⟨C, 2 + γ ^ 2 / 2 - γ * (2 + δ), hC, hκ, hbound⟩

end HarmonicBalls
