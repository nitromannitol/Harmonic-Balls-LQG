import HarmonicBalls.Proofs.Potential.BrownianSingularWeightedMeasure

/-! # Singular occupation exponents for clock increments

A weighted Brownian pair estimate can be matched to a positive truncation exponent
in a restricted range of insertion and field parameters.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A singular pair exponent and truncation level can be chosen with positive decay. -/
theorem exists_singular_clock_truncation_exponents {q γ : ℝ}
    (hq0 : 0 < q) (hq2 : q < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-q) / (2+q)) :
    ∃ β θ : ℝ, 0 < β ∧ β < 2 ∧ γ < θ ∧ θ < 2*γ ∧
      0 < β*(2-q)/(2+q) - γ^2 + (2*γ-θ)^2/2 := by
  let a : ℝ := (2-q)/(2+q)
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hsub' : γ^2/2 < 2*a := by
    convert hsub using 1; dsimp [a]; ring
  have hb : γ^2/(2*a) < 2 := by
    rw [div_lt_iff₀ (by positivity : 0 < 2*a)]
    nlinarith
  obtain ⟨β, hβl, hβu⟩ := exists_between hb
  have hβ0 : 0 < β := by
    have : 0 ≤ γ^2/(2*a) := by positivity
    linarith
  have hd : γ^2/2 < β*a := by
    have hh := (div_lt_iff₀ (show 0 < 2*a by positivity)).mp hβl
    nlinarith
  let e : ℝ := β*a - γ^2/2
  have he : 0 < e := by dsimp [e]; linarith
  have hv : γ < min (2*γ) (γ + e/(γ+1)) := by
    apply lt_min
    · linarith
    · have : 0 < e/(γ+1) := div_pos he (by linarith)
      linarith
  obtain ⟨θ, hθl, hθu⟩ := exists_between hv
  have hθ2 : θ < 2*γ := hθu.trans_le (min_le_left _ _)
  have hθe : θ-γ < e/(γ+1) := by
    have := hθu.trans_le (min_le_right (2*γ) (γ + e/(γ+1)))
    linarith
  have hmul : (θ-γ)*(γ+1) < e := (lt_div_iff₀ (by linarith : 0 < γ+1)).mp hθe
  have hsq : 0 ≤ (θ-γ)^2 := sq_nonneg _
  have hθg : 0 < θ-γ := by linarith
  refine ⟨β, θ, hβ0, hβu, hθl, hθ2, ?_⟩
  have hid : β*(2-q)/(2+q) = β*a := by dsimp [a]; ring
  rw [hid]
  dsimp [e] at hmul
  nlinarith

/-- Singularly dominated occupation weights admit a pair exponent compatible with
positive Gaussian truncation decay. The constant may depend on the Brownian path. -/
theorem planarBrownianMotion_ae_singular_pair_clock_exponents (x z : ℂ) {q γ : ℝ}
    (hq0 : 0 < q) (hq2 : q < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-q) / (2+q)) :
    ∃ β θ : ℝ, 0 < β ∧ β < 2 ∧ γ < θ ∧ θ < 2*γ ∧
      0 < β*(2-q)/(2+q) - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧
        ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
        (∀ w, ENNReal.ofReal |g w| ≤ ENNReal.ofReal M *
          (ENNReal.ofReal ‖w-z‖) ^ (-q)) → ∀ r : ℝ, 0 < r →
        let μ := Measure.map (fun t => b t) ν
        Integrable (fun p : ℂ × ℂ =>
          if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
        (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0
          ∂(μ.prod μ)) ≤ M^2*(C*r^(β*(2-q)/(2+q))) := by
  obtain ⟨β, θ, hβ0, hβ2, hγθ, hθ, hdecay⟩ :=
    exists_singular_clock_truncation_exponents hq0 hq2 hγ hsub
  refine ⟨β, θ, hβ0, hβ2, hγθ, hθ, hdecay, ?_⟩
  filter_upwards [planarBrownianMotion_ae_unit_singular_weighted_occupation_measure_le
    x z hq0 hq2 hβ0 hβ2] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, ?_⟩
  intro g hg M hM hgM r hr
  exact ⟨(hb g hg M hM hgM r hr).1, (hb g hg M hM hgM r hr).2.2⟩

end HarmonicBalls
