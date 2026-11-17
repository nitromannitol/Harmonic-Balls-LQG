import HarmonicBalls.Proofs.Potential.LQGClockExistenceProved
import LatticeProb.LQG.GMCL1Rate

/-! # Field increment bounds at an arbitrary normalization radius

A weighted pair estimate yields a geometric bound on circle-average increments
for measures supported in an arbitrary bounded region.
-/

open MeasureTheory Real Set
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- A weighted pair bound controls the expected field increment at any positive
normalization radius. -/
theorem field_increment_le_rate_of_radius
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε R γ θ d C M : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R)
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2 * γ)
    (hA : (∫ z, |g z| ∂ν) ≤ M)
    (hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) ≤ C * Real.exp (Real.log ε * d)) :
    ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω (ε / 2) z - hcirc ω R 0)) -
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν| ∂P ≤
      ((Real.exp (γ ^ 2 * Real.log 2) - 1) *
        Real.exp (Real.log R * (2 * γ ^ 2 - (2 * γ - θ) ^ 2 / 2)) * C + 1) / 2 *
        Real.exp (Real.log ε * ((d - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2)) +
      2 * M * Real.exp (Real.log R * (γ ^ 2 / 2 - (θ - γ) ^ 2 / 2)) *
        Real.exp (Real.log ε * ((θ - γ) ^ 2 / 2)) := by
  let p : ℝ := 2 * γ ^ 2 - (2 * γ - θ) ^ 2 / 2
  let q : ℝ := γ ^ 2 / 2 - (θ - γ) ^ 2 / 2
  let a : ℝ := γ ^ 2 / 2
  let u : ℝ := Real.log ε
  let v : ℝ := Real.log R
  let B : ℝ := Real.exp (γ ^ 2 * Real.log 2) - 1
  let I : ℝ := ∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
    (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)
  let A : ℝ := ∫ z, |g z| ∂ν
  have hB : 0 ≤ B := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hraw := hh.integral_abs_integral_increment_le hε hR ν hgm hg hgR hγθ hθ
    (t := Real.exp (u * ((d - p) / 2))) (Real.exp_pos _)
  have hlog : Real.log (R / ε) = v - u := Real.log_div hR.ne' hε.ne'
  conv at hraw =>
    rhs
    rw [hlog, Real.rpow_def_of_pos hε]
  change _ ≤ Real.exp (u*a) * ((B * Real.exp ((v-u)*p) * I /
    Real.exp (u*((d-p)/2)) + Real.exp (u*((d-p)/2))) / 2 +
    2*A*Real.exp ((v-u)*q)) at hraw
  have hI' : I ≤ C * Real.exp (u*d) := hI
  have hA' : A ≤ M := hA
  have hi : B * Real.exp ((v-u)*p) * I / Real.exp (u*((d-p)/2)) ≤
      B * Real.exp ((v-u)*p) * (C * Real.exp (u*d)) / Real.exp (u*((d-p)/2)) := by
    gcongr
  have ha : 2*A*Real.exp ((v-u)*q) ≤ 2*M*Real.exp ((v-u)*q) := by gcongr
  refine hraw.trans ?_
  calc
    _ ≤ Real.exp (u*a) * ((B * Real.exp ((v-u)*p) * (C * Real.exp (u*d)) /
        Real.exp (u*((d-p)/2)) + Real.exp (u*((d-p)/2))) / 2 +
        2*M*Real.exp ((v-u)*q)) := by gcongr
    _ = _ := by
      have h1 : Real.exp (u*a) * Real.exp ((v-u)*p) * Real.exp (u*d) /
          Real.exp (u*((d-p)/2)) = Real.exp (v*p) * Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
        congr 1
        ring
      have h2 : Real.exp (u*a) * Real.exp (u*((d-p)/2)) = Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : Real.exp (u*a) * Real.exp ((v-u)*q) = Real.exp (v*q) * Real.exp (u*(a-q)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      dsimp [p, q, a, u, v, B] at h1 h2 h3 ⊢
      ring_nf at h1 h2 h3 ⊢
      linear_combination (B*C/2)*h1 + (1/2)*h2 + (2*M)*h3

end HarmonicBalls
