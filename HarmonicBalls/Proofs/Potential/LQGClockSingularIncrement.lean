import HarmonicBalls.Proofs.Potential.LQGClockSingularPairExponents
import LatticeProb.LQG.GMCL1Rate

/-! # Singularly weighted clock increments

A pathwise Gaussian increment bound holds uniformly for singularly dominated weights.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

private theorem exp_bound_algebra {u p d a q B C M I A : ℝ}
    (hB : 0 ≤ B)
    (hI : I ≤ C * Real.exp (u*d)) (hA : A ≤ M) :
    Real.exp (u*a) * ((B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) +
      Real.exp (u*((d-p)/2))) / 2 + 2*A*Real.exp (-u*q)) ≤
    (B*C+1)/2 * Real.exp (u*(a+(d-p)/2)) + 2*M*Real.exp (u*(a-q)) := by
  have h : B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) ≤
      B * Real.exp (-u*p) * (C * Real.exp (u*d)) / Real.exp (u*((d-p)/2)) := by
    gcongr
  have ha : 2*A*Real.exp (-u*q) ≤ 2*M*Real.exp (-u*q) := by gcongr
  calc
    _ ≤ Real.exp (u*a) * ((B * Real.exp (-u*p) * (C * Real.exp (u*d)) /
        Real.exp (u*((d-p)/2)) + Real.exp (u*((d-p)/2))) / 2 +
        2*M*Real.exp (-u*q)) := by gcongr
    _ = _ := by
      have h1 : Real.exp (u*a) * Real.exp (-u*p) * Real.exp (u*d) /
          Real.exp (u*((d-p)/2)) = Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      have h2 : Real.exp (u*a) * Real.exp (u*((d-p)/2)) =
          Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : Real.exp (u*a) * Real.exp (-u*q) = Real.exp (u*(a-q)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination (B*C/2)*h1 + (1/2)*h2 + (2*M)*h3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

private theorem field_increment_le_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε γ θ d C M : ℝ}
    (hε : 0 < ε) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1)
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2 * γ)
    (hA : (∫ z, |g z| ∂ν) ≤ M)
    (hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) ≤ C * Real.exp (Real.log ε * d)) :
    ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω (ε / 2) z - hcirc ω 1 0)) -
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0))) ∂ν| ∂P ≤
      ((Real.exp (γ ^ 2 * Real.log 2) - 1) * C + 1) / 2 *
        Real.exp (Real.log ε * ((d - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2)) +
      2 * M * Real.exp (Real.log ε * ((θ - γ) ^ 2 / 2)) := by
  let p : ℝ := 2 * γ ^ 2 - (2 * γ - θ) ^ 2 / 2
  let q : ℝ := γ ^ 2 / 2 - (θ - γ) ^ 2 / 2
  let u : ℝ := Real.log ε
  have hB : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hraw := hh.integral_abs_integral_increment_le hε (R := 1) zero_lt_one ν hgm hg hgR hγθ hθ
    (t := Real.exp (u * ((d - p) / 2))) (Real.exp_pos _)
  have hlog : Real.log (1 / ε) = -u := by simp [u]
  conv at hraw =>
    rhs
    rw [hlog, Real.rpow_def_of_pos hε]
  have halg := exp_bound_algebra (u := u) (p := p) (d := d) (a := γ ^ 2 / 2)
    (q := q) (B := Real.exp (γ ^ 2 * Real.log 2) - 1) hB hI hA
  refine hraw.trans ?_
  convert halg using 1; dsimp [p, q, u]; ring_nf

/-- Singularly dominated weights have a common pathwise field-increment bound. -/
theorem planarBrownianMotion_ae_singular_field_increment_le
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x z : ℂ) {q γ : ℝ}
    (hq0 : 0 < q) (hq2 : q < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-q) / (2+q)) :
    ∃ β θ : ℝ, 0 < β ∧ β < 2 ∧ γ < θ ∧ θ < 2*γ ∧
      0 < β*(2-q)/(2+q) - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x), ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
        ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
        (∀ w, ENNReal.ofReal |g w| ≤ ENNReal.ofReal M *
          (ENNReal.ofReal ‖w-z‖) ^ (-q)) →
        (∀ w, g w ≠ 0 → ‖w‖ ≤ 1/2) →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        let μ := Measure.map (fun t => b t) ν
        (∫ ω, |∫ w, g w * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*M^2*C+1)/2 *
          Real.exp (Real.log ε * ((β*(2-q)/(2+q)-γ^2+(2*γ-θ)^2/2)/2)) +
        2*(M*A)*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨β, θ, hβ0, hβ2, hγθ, hθ, hdecay, hb⟩ :=
    planarBrownianMotion_ae_singular_pair_clock_exponents x z hq0 hq2 hγ hsub
  refine ⟨β, θ, hβ0, hβ2, hγθ, hθ, hdecay, ?_⟩
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [hb, planarBrownianMotion_ae_unit_singular_occupation_lt_top x z hq0 hq2]
    with b hb hsing
  obtain ⟨C, hC, hb⟩ := hb
  let A : ℝ≥0∞ := ∫⁻ t, (ENNReal.ofReal ‖b t-z‖)^(-q) ∂ν
  refine ⟨C * 2^(β*(2-q)/(2+q)), A.toReal, by positivity, ENNReal.toReal_nonneg, ?_⟩
  intro g hg M hM hgM hgs ε hε hεhalf
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hlin : (∫⁻ w, ENNReal.ofReal |g w| ∂μ) ≤ ENNReal.ofReal M * A := by
    rw [show μ = Measure.map (fun t => b t) ν from rfl,
      lintegral_map hg.abs.ennreal_ofReal b.continuous.measurable]
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal M * (ENNReal.ofReal ‖b t-z‖)^(-q) ∂ν :=
        lintegral_mono (fun t => hgM (b t))
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hgi : Integrable g μ := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (b := ENNReal.ofReal M * A) ?_
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsing)
    simpa only [Real.enorm_eq_ofReal_abs] using hlin
  have hA : (∫ w, |g w| ∂μ) ≤ M*A.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsing.ne) hlin
    rw [← ofReal_integral_eq_lintegral_ofReal hgi.abs
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
      ENNReal.toReal_ofReal (integral_nonneg (fun _ => abs_nonneg _)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] at h
    exact h
  have hp := (hb g hg M hM hgM (2*ε) (by positivity)).2
  have hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (M^2*(C*2^(β*(2-q)/(2+q))))*Real.exp (Real.log ε*(β*(2-q)/(2+q))) := by
    have hp' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
        (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
        M^2*(C*(2*ε)^(β*(2-q)/(2+q))) := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hp
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hp'
    convert hp' using 1; ring
  have h := field_increment_le_rate hh hε μ hg hgi (fun w hw => by linarith [hgs w hw])
    hγθ.le hθ.le hA hI
  convert h using 1; ring

end HarmonicBalls
