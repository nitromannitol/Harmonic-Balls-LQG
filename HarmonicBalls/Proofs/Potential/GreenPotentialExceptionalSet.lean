import HarmonicBalls.Proofs.Potential.LogPotentialExceptionalSet
import HarmonicBalls.Proofs.Sec5.GeneralDomainGreenQuadrature

/-!
# Green potentials and the diagonal

The potential-theoretic infrastructure uses work of Leonardo Bonanno.  The real
kernel has value zero at the diagonal; the lower-integral kernel below assigns
infinite value there.  They agree at poles where the source has no atom and the
real kernel is integrable.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- The nonnegative Green kernel with its potential-theoretic diagonal value. -/
noncomputable def greenKernelExtended (O : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  if y = x then ⊤ else ENNReal.ofReal (greenFunction O x y)

/-- At a non-atomic pole, real integrability identifies the lower-integral
potential with the real Green potential. -/
theorem lintegral_greenKernelExtended_eq {O : Set ℂ} (hO : Bornology.IsBounded O)
    {ν : Measure ℂ} {x : ℂ} (hatom : ν {x} = 0)
    (hi : Integrable (greenFunction O x) ν) :
    (∫⁻ y, greenKernelExtended O x y ∂ν) = ENNReal.ofReal (greenPotential O ν x) := by
  have hae : ∀ᵐ y ∂ν, y ≠ x := ae_iff.mpr (by simpa using hatom)
  calc
    (∫⁻ y, greenKernelExtended O x y ∂ν) =
        ∫⁻ y, ENNReal.ofReal (greenFunction O x y) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hae] with y hy
          simp [greenKernelExtended, hy]
    _ = ENNReal.ofReal (greenPotential O ν x) :=
      (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall (greenFunction_nonneg hO x))).symm

/-- The potential-theoretic lower integral is finite at such a pole. -/
theorem lintegral_greenKernelExtended_lt_top {O : Set ℂ} (hO : Bornology.IsBounded O)
    {ν : Measure ℂ} {x : ℂ} (hatom : ν {x} = 0)
    (hi : Integrable (greenFunction O x) ν) :
    (∫⁻ y, greenKernelExtended O x y ∂ν) < ⊤ := by
  rw [lintegral_greenKernelExtended_eq hO hatom hi]
  exact ENNReal.ofReal_lt_top

/-- At points where both sources have no atom and both kernels are integrable,
the difference of the finite lower-integral potentials equals the real one. -/
theorem greenPotential_sub_eq_lintegral_toReal {O : Set ℂ}
    (hO : Bornology.IsBounded O) {ν₁ ν₂ : Measure ℂ} {x : ℂ}
    (h₁ : ν₁ {x} = 0) (h₂ : ν₂ {x} = 0)
    (hi₁ : Integrable (greenFunction O x) ν₁)
    (hi₂ : Integrable (greenFunction O x) ν₂) :
    greenPotential O ν₁ x - greenPotential O ν₂ x =
      (∫⁻ y, greenKernelExtended O x y ∂ν₁).toReal -
        (∫⁻ y, greenKernelExtended O x y ∂ν₂).toReal := by
  rw [lintegral_greenKernelExtended_eq hO h₁ hi₁,
    lintegral_greenKernelExtended_eq hO h₂ hi₂,
    ENNReal.toReal_ofReal (greenPotential_nonneg hO ν₁ x),
    ENNReal.toReal_ofReal (greenPotential_nonneg hO ν₂ x)]

/-- Uniform disc Green-potential bound under upper growth on a bounded
restriction, including poles in the observation set. -/
theorem green_disc_integral_bound_of_upper {μ : Measure ℂ} {R r₀ β : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedBall (0 : ℂ) R,
      Integrable (greenFunction (ball 0 R) x) (μ.restrict (ball 0 R)) ∧
      (∫ y, greenFunction (ball 0 R) x y ∂μ.restrict (ball 0 R)) ≤ C := by
  let α := greenPotentialHolderExponent β
  let K := greenPotentialRieszBound β r₀ (μ (ball (0 : ℂ) R)).toReal
  have hK : 0 ≤ K := greenPotentialRieszBound_nonneg hβ hr₀ ENNReal.toReal_nonneg
  have hbound : ∀ x ∈ closedBall (0 : ℂ) R,
      ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-α)) ∂μ.restrict (ball 0 R) ≤ ENNReal.ofReal K := by
    intro x hx
    have hi := riesz_integrable_restrict_ball_of_upper hR hr₀ hβ hup hfin hx
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1
      (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal hi.2
  have h := greenPotential_ball_integrable_and_sub_le (M := 1) hR (greenPotentialHolderExponent_pos hβ)
    (greenPotentialHolderExponent_le_one β) hK hbound
    (fun x _ => restrict_ball_singleton_eq_zero_of_upper hR hr₀ hβ hup hfin x)
    (f := fun _ => (1 : ℝ)) aestronglyMeasurable_const (by norm_num)
    (Filter.Eventually.of_forall (by simp))
  let C := 2 * (Real.pi * α)⁻¹ * K * (2 * R) ^ α
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hx₀ : (R : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hzero : ∀ y, greenFunction (ball (0 : ℂ) R) (R : ℂ) y = 0 :=
    greenFunction_of_notMem_left (by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hR.le]
      exact lt_irrefl R)
  have hd : ‖x - (R : ℂ)‖ ≤ 2 * R := by
    have hx' : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    calc ‖x - (R : ℂ)‖ ≤ ‖x‖ + ‖(R : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 * R := by rw [Complex.norm_real, Real.norm_of_nonneg hR.le]; linarith
  have hp := Real.rpow_le_rpow (norm_nonneg (x - (R : ℂ))) hd
    (greenPotentialHolderExponent_pos hβ).le
  have hb := h.2 x hx (R : ℂ) hx₀
  simp only [mul_one, hzero, integral_zero, sub_zero] at hb
  refine ⟨by simpa only [mul_one] using h.1 x hx, ?_⟩
  apply (le_abs_self _).trans (hb.trans ?_)
  dsimp [C]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr
      (mul_nonneg Real.pi_pos.le (greenPotentialHolderExponent_pos hβ).le))) hK)

/-- Product integrability of the disc Green kernel for a finite source in
the closed disc and an observation measure with upper growth. -/
theorem green_disc_integrable_product_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) :
    Integrable (fun p : ℂ × ℂ => greenFunction (ball 0 R) p.1 p.2)
      ((ν.restrict (closedBall 0 R)).prod (μ.restrict (ball 0 R))) := by
  have : IsFiniteMeasure (μ.restrict (ball 0 R)) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨C, hC, hbound⟩ := green_disc_integral_bound_of_upper hR hr₀ hβ hup hfin
  let f : ℂ × ℂ → ℝ := fun p => greenFunction (ball 0 R) p.1 p.2
  have hf : Measurable f := measurable_greenFunction_ball_uncurry R
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact (hbound x hx).1
  · apply Integrable.mono' (integrable_const C) (hf.norm.aestronglyMeasurable.integral_prod_right')
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have heq : (fun y => ‖f (x, y)‖) = fun y => greenFunction (ball 0 R) x y := by
      funext y
      simp only [f, Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg isBounded_ball x y)]
    rw [heq, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (greenFunction_nonneg isBounded_ball x))]
    exact (hbound x hx).2

/-- For a finite source concentrated in the closed disc, almost every observation
point has an integrable real Green kernel and a finite extended potential. -/
theorem ae_green_disc_potential_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤)
    (hν : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R) :
    ∀ᵐ x ∂μ.restrict (ball 0 R),
      Integrable (greenFunction (ball 0 R) x) ν ∧ ν {x} = 0 ∧
      (∫⁻ y, greenKernelExtended (ball 0 R) x y ∂ν) < ⊤ ∧
      (∫⁻ y, greenKernelExtended (ball 0 R) x y ∂ν) =
        ENNReal.ofReal (greenPotential (ball 0 R) ν x) := by
  have : IsFiniteMeasure (μ.restrict (ball 0 R)) := isFiniteMeasure_restrict.2 hfin
  have hp := (green_disc_integrable_product_of_upper (ν := ν) hR hr₀ hβ hup hfin).swap
  rw [Measure.restrict_eq_self_of_ae_mem hν] at hp
  filter_upwards [hp.prod_right_ae,
      ae_measure_singleton_eq_zero_of_upper (ν := ν) hR hr₀ hβ hup hfin] with x hi hatom
  have hi' : Integrable (greenFunction (ball 0 R) x) ν := by
    convert hi using 1
    funext y
    exact greenFunction_ball_comm R x y
  exact ⟨hi', hatom, lintegral_greenKernelExtended_lt_top isBounded_ball hatom hi',
    lintegral_greenKernelExtended_eq isBounded_ball hatom hi'⟩

/-- Domain monotonicity transfers the exceptional-set result from an enclosing
disc to any open subdomain. The source may charge the observation set. -/
theorem ae_greenPotential_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {O : Set ℂ} {R r₀ β : ℝ} (hO : IsOpen O)
    (hsub : O ⊆ ball (0 : ℂ) R) (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤)
    (hν : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R) :
    ∀ᵐ x ∂μ.restrict (ball 0 R),
      Integrable (greenFunction O x) ν ∧ ν {x} = 0 ∧
      (∫⁻ y, greenKernelExtended O x y ∂ν) < ⊤ ∧
      (∫⁻ y, greenKernelExtended O x y ∂ν) = ENNReal.ofReal (greenPotential O ν x) := by
  have hOb : Bornology.IsBounded O := isBounded_ball.subset hsub
  filter_upwards [ae_green_disc_potential_of_upper (ν := ν) hR hr₀ hβ hup hfin hν] with x hx
  have hi := Section6.integrable_greenFunction_of_subset hO hsub isBounded_ball ν x hx.1
  exact ⟨hi, hx.2.1, lintegral_greenKernelExtended_lt_top hOb hx.2.1 hi,
    lintegral_greenKernelExtended_eq hOb hx.2.1 hi⟩

/-- Local upper growth removes the exceptional set for a compactly
concentrated finite source on a bounded open domain. -/
theorem ae_greenPotential_of_local_upper_growth {μ ν : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {O K : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (s : ℝ) :
    ∀ᵐ x ∂μ.restrict (ball 0 s),
      Integrable (greenFunction O x) ν ∧ ν {x} = 0 ∧
      (∫⁻ y, greenKernelExtended O x y ∂ν) < ⊤ ∧
      (∫⁻ y, greenKernelExtended O x y ∂ν) = ENNReal.ofReal (greenPotential O ν x) := by
  obtain ⟨a, ha⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨b, hb⟩ := hOb.subset_closedBall (0 : ℂ)
  let R := max (max (max s a) b) 1 + 1
  have hmax : max (max s a) b ≤ max (max (max s a) b) 1 := le_max_left _ _
  have hsR : s ≤ R := by
    dsimp [R]
    have := (le_max_left s a).trans (le_max_left (max s a) b) |>.trans hmax
    linarith
  have haR : a ≤ R := by
    dsimp [R]
    have := (le_max_right s a).trans (le_max_left (max s a) b) |>.trans hmax
    linarith
  have hbR : b < R := by
    dsimp [R]
    have := (le_max_right (max s a) b).trans hmax
    linarith
  have hR : 0 < R := by
    dsimp [R]
    have := le_max_right (max (max s a) b) (1 : ℝ)
    linarith
  have hsub : O ⊆ ball (0 : ℂ) R := fun x hx =>
    (closedBall_subset_ball hbR) (hb hx)
  have hνR : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R := by
    have hνK : ∀ᵐ y ∂ν, y ∈ K := ae_iff.mpr hν
    filter_upwards [hνK] with y hy
    exact closedBall_subset_closedBall haR (ha hy)
  obtain ⟨r₀, β, hr₀, hβ, hg⟩ := hup R hR
  exact Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono
    (ball_subset_ball hsR) le_rfl))
    (ae_greenPotential_of_upper hO hsub hR hr₀ hβ hg
      (measure_ball_lt_top (μ := μ)).ne hνR)

/-- The difference of two compactly concentrated finite Green potentials agrees
almost everywhere with the difference of their finite lower integrals. -/
theorem ae_greenPotential_sub_of_local_upper_growth {μ ν₁ ν₂ : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {O K₁ K₂ : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hν₁ : ν₁ K₁ᶜ = 0) (hν₂ : ν₂ K₂ᶜ = 0) (s : ℝ) :
    ∀ᵐ x ∂μ.restrict (ball 0 s),
      (∫⁻ y, greenKernelExtended O x y ∂ν₁) < ⊤ ∧
      (∫⁻ y, greenKernelExtended O x y ∂ν₂) < ⊤ ∧
      greenPotential O ν₁ x - greenPotential O ν₂ x =
        (∫⁻ y, greenKernelExtended O x y ∂ν₁).toReal -
          (∫⁻ y, greenKernelExtended O x y ∂ν₂).toReal := by
  filter_upwards [ae_greenPotential_of_local_upper_growth hup hO hOb hK₁ hν₁ s,
    ae_greenPotential_of_local_upper_growth hup hO hOb hK₂ hν₂ s] with x h₁ h₂
  exact ⟨h₁.2.2.1, h₂.2.2.1,
    greenPotential_sub_eq_lintegral_toReal hOb h₁.2.1 h₂.2.1 h₁.1 h₂.1⟩

#print axioms ae_greenPotential_sub_of_local_upper_growth
#print axioms ae_greenPotential_of_local_upper_growth
#print axioms ae_greenPotential_of_upper
#print axioms ae_green_disc_potential_of_upper
#print axioms green_disc_integrable_product_of_upper
#print axioms green_disc_integral_bound_of_upper
#print axioms greenPotential_sub_eq_lintegral_toReal
#print axioms lintegral_greenKernelExtended_eq
#print axioms lintegral_greenKernelExtended_lt_top

end HarmonicBalls
