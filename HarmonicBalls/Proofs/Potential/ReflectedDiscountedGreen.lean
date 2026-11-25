import HarmonicBalls.Proofs.Potential.ReflectedCenteredGreenKernel
import HarmonicBalls.Proofs.Potential.ReflectedClockResolventSymmetry

/-!
# The discounted Green kernels and their limit

For `β ≥ 0` put `g̃_β(x, y) = ∫_0^∞ e^{-β s} (k_s(x, y) - 1) ds` (`discountedGreenKernel`), so that
`g̃_0 = g` is the centered Green kernel. Off the diagonal of `K₀`:

* the Green kernel `g_β = ∫_0^∞ e^{-β s} k_s ds` of the square is `g̃_β + 1/β` for `β > 0`
  (`toReal_squareGreenKernel`);
* `|g̃_β| ≤ C₁ |x - y|^{-2θ} + C₂` uniformly in `β ≥ 0` (`exists_abs_discountedGreenKernel_le`), and
  `g̃_β → g` as `β → 0` (`tendsto_discountedGreenKernel`), by dominated convergence with the
  majorant of `|k_s - 1|`.

For a probability measure `ν` with upper power bounds and bounded measurable `f`, the potentials
`∫ g̃_β(z, y) f(y) ν(dy)` (`discountedGreenPotential`) are bounded on `K₀` uniformly in `β` and
converge to `∫ g(z, y) f(y) ν(dy)` (`centeredGreenPotential`) for every `z ∈ K₀`
(`tendsto_discountedGreenPotential`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The discounted centered Green kernel `g̃_β(x, y) = ∫_0^∞ e^{-β s} (k_s(x, y) - 1) ds`. -/
noncomputable def discountedGreenKernel (β : ℝ) (x y : ℂ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-(β * s)) * (neumannKernel s x y - 1)

theorem measurable_discountedGreenKernel_uncurry (β : ℝ) :
    Measurable fun p : ℂ × ℂ => discountedGreenKernel β p.1 p.2 := by
  have hf : StronglyMeasurable fun q : (ℂ × ℂ) × ℝ =>
      Real.exp (-(β * q.2)) * (neumannKernel q.2 q.1.1 q.1.2 - 1) :=
    ((Real.continuous_exp.measurable.comp ((measurable_snd.const_mul β).neg)).mul
      ((measurable_neumannKernel_uncurry.comp (measurable_snd.prodMk
        (measurable_fst.fst.prodMk measurable_fst.snd))).sub measurable_const)).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem exp_neg_mul_le_one {β s : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) : Real.exp (-(β * s)) ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith)

/-- **Uniform bounds for the discounted kernels** off the diagonal. -/
theorem exists_abs_discountedGreenKernel_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ y ∈ closedSquare (0 : ℂ) 1,
      x ≠ y → ∀ β : ℝ, 0 ≤ β →
        IntegrableOn (fun s => Real.exp (-(β * s)) * (neumannKernel s x y - 1)) (Ioi 0) ∧
        |discountedGreenKernel β x y| ≤ C₁ * ‖x - y‖ ^ (-(2 * θ)) + C₂ ∧
        |centeredGreenKernel x y| ≤ C₁ * ‖x - y‖ ^ (-(2 * θ)) + C₂ := by
  obtain ⟨a, b, ham, hbm, hai, hbi, ha0, hb0, hab⟩ := exists_neumannKernel_majorant hθ0 hθ1
  refine ⟨∫ s in Ioi (0 : ℝ), a s, ∫ s in Ioi (0 : ℝ), b s, setIntegral_nonneg measurableSet_Ioi
    fun s _ => ha0 s, setIntegral_nonneg measurableSet_Ioi fun s _ => hb0 s,
    fun x hx y hy hxy β hβ => ?_⟩
  have hmaj : IntegrableOn (fun s => a s * ‖x - y‖ ^ (-(2 * θ)) + b s) (Ioi 0) :=
    (hai.mul_const _).add hbi
  have hval : ∫ s in Ioi (0 : ℝ), (a s * ‖x - y‖ ^ (-(2 * θ)) + b s) =
      (∫ s in Ioi (0 : ℝ), a s) * ‖x - y‖ ^ (-(2 * θ)) + ∫ s in Ioi (0 : ℝ), b s := by
    rw [integral_add (hai.mul_const _) hbi, integral_mul_const]
  have hle : ∀ β' : ℝ, 0 ≤ β' → ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ‖Real.exp (-(β' * s)) * (neumannKernel s x y - 1)‖ ≤
        a s * ‖x - y‖ ^ (-(2 * θ)) + b s := by
    intro β' hβ'
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (exp_neg_mul_le_one hβ' (le_of_lt hs))).trans
      (hab x hx y hy hxy s hs)
  have hmeas : ∀ β' : ℝ, AEStronglyMeasurable (fun s => Real.exp (-(β' * s)) *
      (neumannKernel s x y - 1)) (volume.restrict (Ioi (0 : ℝ))) := fun β' =>
    ((Real.continuous_exp.measurable.comp ((measurable_id.const_mul β').neg)).mul
      ((measurable_neumannKernel_time x y).sub measurable_const)).aestronglyMeasurable
  refine ⟨hmaj.mono' (hmeas β) (hle β hβ), ?_, ?_⟩
  · have h := norm_integral_le_of_norm_le hmaj (hle β hβ)
    rwa [hval, Real.norm_eq_abs] at h
  · have h := norm_integral_le_of_norm_le hmaj (hle 0 le_rfl)
    simp only [zero_mul, neg_zero, Real.exp_zero, one_mul] at h
    rwa [hval, Real.norm_eq_abs] at h

/-- **`g̃_β → g` as `β → 0`** off the diagonal, along `β_n = 1/(n+1)`. -/
theorem tendsto_discountedGreenKernel {x y : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1)
    (hy : y ∈ closedSquare (0 : ℂ) 1) (hxy : x ≠ y) :
    Tendsto (fun n : ℕ => discountedGreenKernel (1 / (n + 1)) x y) atTop
      (𝓝 (centeredGreenKernel x y)) := by
  obtain ⟨a, b, ham, hbm, hai, hbi, ha0, hb0, hab⟩ := exists_neumannKernel_majorant one_pos le_rfl
  have hmaj : IntegrableOn (fun s => a s * ‖x - y‖ ^ (-(2 * (1 : ℝ))) + b s) (Ioi 0) :=
    (hai.mul_const _).add hbi
  refine tendsto_integral_of_dominated_convergence (fun s => a s * ‖x - y‖ ^ (-(2 * (1 : ℝ))) + b s)
    (fun n => ((Real.continuous_exp.measurable.comp ((measurable_id.const_mul _).neg)).mul
      ((measurable_neumannKernel_time x y).sub measurable_const)).aestronglyMeasurable) hmaj
    (fun n => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (exp_neg_mul_le_one (by positivity)
      (le_of_lt hs))).trans (hab x hx y hy hxy s hs)
  · refine Eventually.of_forall fun s => ?_
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => Real.exp (-((1 : ℝ) / (n + 1) * s))) atTop (𝓝 1) := by
      have h4 : Tendsto (fun n : ℕ => -((1 : ℝ) / (n + 1) * s)) atTop (𝓝 0) := by
        simpa using (h1.mul_const s).neg
      have h3 := (Real.continuous_exp.tendsto 0).comp h4
      rw [Real.exp_zero] at h3
      exact h3
    simpa using h2.mul_const (neumannKernel s x y - 1)

/-- **The Green kernel of the square** is `g̃_β + 1/β ≥ 0` off the diagonal, for `β > 0`. -/
theorem squareGreenKernel_eq_ofReal {β : ℝ} (hβ : 0 < β) {x y : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) (hy : y ∈ closedSquare (0 : ℂ) 1) (hxy : x ≠ y) :
    0 ≤ discountedGreenKernel β x y + 1 / β ∧
      squareGreenKernel β x y = ENNReal.ofReal (discountedGreenKernel β x y + 1 / β) := by
  obtain ⟨C₁, C₂, -, -, h⟩ := exists_abs_discountedGreenKernel_le one_pos le_rfl
  have hi := (h x hx y hy hxy β hβ.le).1
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-(β * s))) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 hβ
    simpa only [neg_mul] using this
  have hk : IntegrableOn (fun s => Real.exp (-(β * s)) * neumannKernel s x y) (Ioi 0) :=
    (hi.add hexp).congr_fun (fun s _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  have hval : ∫ s in Ioi (0 : ℝ), Real.exp (-(β * s)) = 1 / β := by
    have := integral_exp_mul_Ioi (a := -β) (by linarith) 0
    simp only [mul_zero, Real.exp_zero, neg_mul] at this
    rw [this]
    field_simp
  have hsplit : ∫ s in Ioi (0 : ℝ), Real.exp (-(β * s)) * neumannKernel s x y =
      discountedGreenKernel β x y + 1 / β := by
    rw [discountedGreenKernel, ← hval, ← integral_add hi hexp]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    ring
  have hnn : 0 ≤ ∫ s in Ioi (0 : ℝ), Real.exp (-(β * s)) * neumannKernel s x y :=
    integral_nonneg fun s => mul_nonneg (Real.exp_pos _).le (neumannKernel_nonneg _ _ _)
  refine ⟨hsplit ▸ hnn, ?_⟩
  unfold squareGreenKernel
  rw [← hsplit]
  have hlin : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(β * s))) *
      squareNeumannKernel s.toNNReal x y = ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(β * s)) * neumannKernel s x y) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_neumannKernel hs hx hy]
  rw [hlin, ← ofReal_integral_eq_lintegral_ofReal hk
    (Eventually.of_forall fun s => mul_nonneg (Real.exp_pos _).le (neumannKernel_nonneg _ _ _))]

theorem toReal_squareGreenKernel {β : ℝ} (hβ : 0 < β) {x y : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1)
    (hy : y ∈ closedSquare (0 : ℂ) 1) (hxy : x ≠ y) :
    (squareGreenKernel β x y).toReal = discountedGreenKernel β x y + 1 / β := by
  obtain ⟨h0, h⟩ := squareGreenKernel_eq_ofReal hβ hx hy hxy
  rw [h, ENNReal.toReal_ofReal h0]

/-! ### The potentials -/

section Potentials

variable {ν : Measure ℂ}

/-- The discounted potential `∫ g̃_β(z, y) f(y) ν(dy)`. -/
noncomputable def discountedGreenPotential (ν : Measure ℂ) (β : ℝ) (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ y, discountedGreenKernel β z y * f y ∂ν

/-- The centered Green potential `∫ g(z, y) f(y) ν(dy)`. -/
noncomputable def centeredGreenPotential (ν : Measure ℂ) (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ y, centeredGreenKernel z y * f y ∂ν

variable [IsProbabilityMeasure ν]

theorem measurable_discountedGreenPotential (β : ℝ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable (discountedGreenPotential ν β f) := by
  have hm : StronglyMeasurable fun q : ℂ × ℂ => discountedGreenKernel β q.1 q.2 * f q.2 :=
    ((measurable_discountedGreenKernel_uncurry β).mul (hf.comp measurable_snd)).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := ν)).measurable

theorem measurable_centeredGreenPotential {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable (centeredGreenPotential ν f) := by
  have hm : StronglyMeasurable fun q : ℂ × ℂ => centeredGreenKernel q.1 q.2 * f q.2 :=
    (measurable_centeredGreenKernel_uncurry.mul (hf.comp measurable_snd)).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := ν)).measurable

/-- **Uniform bounds and convergence of the potentials**: for bounded measurable `f`, the discounted
potentials are bounded on `K₀` uniformly in `β ≥ 0`, so is the centered potential, the integrands
are integrable, and `∫ g̃_{β_n}(z, ·) f dν → ∫ g(z, ·) f dν` on `K₀`. -/
theorem IsUpperRegularSpeed.exists_potential_bound (hν : IsUpperRegularSpeed ν) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {f : ℂ → ℝ} {M : ℝ}, Measurable f → (∀ y, |f y| ≤ M) →
      ∀ z ∈ closedSquare (0 : ℂ) 1,
        (∀ β : ℝ, 0 ≤ β → Integrable (fun y => discountedGreenKernel β z y * f y) ν ∧
          |discountedGreenPotential ν β f z| ≤ M * B) ∧
        Integrable (fun y => centeredGreenKernel z y * f y) ν ∧
        |centeredGreenPotential ν f z| ≤ M * B ∧
        Tendsto (fun n : ℕ => discountedGreenPotential ν (1 / (n + 1)) f z) atTop
          (𝓝 (centeredGreenPotential ν f z)) := by
  obtain ⟨β₀, hβ₀, hR⟩ := hν.exists_riesz_le
  obtain ⟨θ, hθ0, hθ1, hθβ⟩ := exists_theta hβ₀
  obtain ⟨R, hR0, hRx⟩ := hR (2 * θ) (by positivity) (by linarith)
  obtain ⟨C₁, C₂, hC₁, hC₂, hC⟩ := exists_abs_discountedGreenKernel_le hθ0 hθ1
  refine ⟨C₁ * R + C₂, by positivity, fun {f M} hf hM z hz => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hw : Integrable (fun y => ‖z - y‖ ^ (-(2 * θ))) ν := integrable_rpow_neg_of_lintegral (hRx z hz)
  have hwR : ∫ y, ‖z - y‖ ^ (-(2 * θ)) ∂ν ≤ R := integral_rpow_neg_le_of_lintegral hR0 (hRx z hz)
  have hmaj : Integrable (fun y => M * (C₁ * ‖z - y‖ ^ (-(2 * θ)) + C₂)) ν :=
    ((hw.const_mul C₁).add (integrable_const C₂)).const_mul M
  have hmajv : ∫ y, M * (C₁ * ‖z - y‖ ^ (-(2 * θ)) + C₂) ∂ν ≤ M * (C₁ * R + C₂) := by
    rw [integral_const_mul, integral_add (hw.const_mul C₁) (integrable_const C₂), integral_const_mul,
      integral_const, smul_eq_mul, probReal_univ, one_mul]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hM0
  have hbd : ∀ (k : ℂ → ℂ → ℝ), (∀ y ∈ closedSquare (0 : ℂ) 1, z ≠ y →
      |k z y| ≤ C₁ * ‖z - y‖ ^ (-(2 * θ)) + C₂) →
      ∀ᵐ y ∂ν, ‖k z y * f y‖ ≤ M * (C₁ * ‖z - y‖ ^ (-(2 * θ)) + C₂) := by
    intro k hk
    filter_upwards [hν.ae_mem, hν.ae_ne hz] with y hy hyz
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul (hM y) (hk y hy (Ne.symm hyz)) (abs_nonneg _) hM0
  have hdisc : ∀ β : ℝ, 0 ≤ β → ∀ᵐ y ∂ν, ‖discountedGreenKernel β z y * f y‖ ≤
      M * (C₁ * ‖z - y‖ ^ (-(2 * θ)) + C₂) := fun β hβ =>
    hbd _ fun y hy hzy => (hC z hz y hy hzy β hβ).2.1
  have hcent : ∀ᵐ y ∂ν, ‖centeredGreenKernel z y * f y‖ ≤
      M * (C₁ * ‖z - y‖ ^ (-(2 * θ)) + C₂) :=
    hbd _ fun y hy hzy => (hC z hz y hy hzy 0 le_rfl).2.2
  have hdm : ∀ β : ℝ, AEStronglyMeasurable (fun y => discountedGreenKernel β z y * f y) ν :=
    fun β => (((measurable_discountedGreenKernel_uncurry β).comp
      (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
  have hcm : AEStronglyMeasurable (fun y => centeredGreenKernel z y * f y) ν :=
    ((measurable_centeredGreenKernel z).mul hf).aestronglyMeasurable
  refine ⟨fun β hβ => ⟨hmaj.mono' (hdm β) (hdisc β hβ), ?_⟩, hmaj.mono' hcm hcent, ?_, ?_⟩
  · have h := norm_integral_le_of_norm_le hmaj (hdisc β hβ)
    rw [Real.norm_eq_abs] at h
    exact h.trans hmajv
  · have h := norm_integral_le_of_norm_le hmaj hcent
    rw [Real.norm_eq_abs] at h
    exact h.trans hmajv
  · refine tendsto_integral_of_dominated_convergence _ (fun n => hdm _) hmaj
      (fun n => hdisc _ (by positivity)) ?_
    filter_upwards [hν.ae_mem, hν.ae_ne hz] with y hy hyz
    exact (tendsto_discountedGreenKernel hz hy (Ne.symm hyz)).mul_const _

end Potentials

end HarmonicBalls
