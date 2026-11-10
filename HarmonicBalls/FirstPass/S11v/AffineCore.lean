import HarmonicBalls.Defs.GFF

/-!
# Change of variables for the complex affine maps `F z = a z + b` (fp-S11v, P6, operator note 01:44 UTC)

Deterministic core of `WholePlaneGFFAffineInvariance` (`Proposed/LQG.lean`): the smearing functionals of the
observables of the whole-plane GFF transform under `F z = a z + b` (`a ≠ 0`, `s = |a|`) as in
`notes/fp-gaps/CHATGPT-n1-hAff-hhom.md` §1:
* pairings: `|a|⁻² ∫ φ(F⁻¹ x) f(x) dx = ∫ φ(u) f(F u) du` (`integral_affine_complex`, Haar change of variables
  for the complex-linear map `u ↦ a u`, which is a real dilation by `|a|` composed with a rotation);
* circle averages: `avg_{∂B(F z, s r)} f = avg_{∂B(z, r)} (f ∘ F)` (`circleAverage_affine_comp`, a reparametrisation
  `θ ↦ θ + arg a` of the period `2π`).
No hypothesis is used: both identities hold for every `f`, with the Bochner integrals of Lean.
-/

namespace HarmonicBalls

open MeasureTheory Complex

/-- Affine change of variables on `ℂ`: `∫ g (a u + b) du = |a|⁻² ∫ g` for `a ≠ 0`. -/
theorem integral_affine_complex {a : ℂ} (ha : a ≠ 0) (b : ℂ) (g : ℂ → ℝ) :
    ∫ u, g (a * u + b) = (‖a‖ ^ 2)⁻¹ * ∫ x, g x := by
  have hae : a = (‖a‖ : ℂ) * ((Circle.exp (arg a) : Circle) : ℂ) := by
    rw [Circle.coe_exp]
    exact (Complex.norm_mul_exp_arg_mul_I a).symm
  set e : Circle := Circle.exp (arg a) with he
  have hr : 0 < ‖a‖ := norm_pos_iff.2 ha
  generalize hR : ‖a‖ = r at hae hr ⊢
  -- the map `u ↦ a u + b` is `u ↦ r • (rotation e u) + b` (rotation: a unit complex multiplication)
  have hG : (fun u : ℂ => g (a * u + b)) = fun u => g (r • rotation e u + b) := by
    funext u
    rw [rotation_apply, Complex.real_smul, hae]
    congr 1
    ring
  have hmp : ∫ u, g (r • rotation e u + b) = ∫ v, g (r • v + b) :=
    (rotation e).measurePreserving.integral_comp (rotation e).toHomeomorph.measurableEmbedding
      (fun v => g (r • v + b))
  have hscale := Measure.integral_comp_smul volume (fun y : ℂ => g (y + b)) r
  have hfin : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [hfin, abs_of_pos (inv_pos.2 (pow_pos hr 2))] at hscale
  simp only [smul_eq_mul, integral_add_right_eq_self g b] at hscale
  rw [hG, hmp]
  exact hscale

/-- Reparametrisation of a circle average under `z ↦ a z + b`:
`avg_{∂B(a z + b, |a| ρ)} f = avg_{∂B(z, ρ)} (f ∘ F)`. -/
theorem circleAverage_affine_comp {a : ℂ} (b : ℂ) (f : ℂ → ℝ) (z : ℂ) (ρ : ℝ) :
    Real.circleAverage f (a * z + b) (‖a‖ * ρ) = Real.circleAverage (fun x => f (a * x + b)) z ρ := by
  have hae : (‖a‖ : ℂ) * exp (arg a * I) = a := Complex.norm_mul_exp_arg_mul_I a
  have key : ∀ θ : ℝ, a * circleMap z ρ θ + b = circleMap (a * z + b) (‖a‖ * ρ) (θ + arg a) := by
    intro θ
    simp only [circleMap]
    push_cast
    rw [add_mul, Complex.exp_add]
    linear_combination (-((ρ : ℂ) * exp (θ * I))) * hae
  have hper : Function.Periodic (fun θ : ℝ => f (circleMap (a * z + b) (‖a‖ * ρ) θ)) (2 * Real.pi) :=
    (periodic_circleMap (a * z + b) (‖a‖ * ρ)).comp f
  have h2 : ∫ x in (0 : ℝ)..2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) (x + arg a)) =
      ∫ x in arg a..arg a + 2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) x) := by
    rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => f (circleMap (a * z + b) (‖a‖ * ρ) x)) (arg a),
      zero_add, add_comm (2 * Real.pi) (arg a)]
  have h3 : ∫ x in arg a..arg a + 2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) x) =
      ∫ x in (0 : ℝ)..2 * Real.pi, f (circleMap (a * z + b) (‖a‖ * ρ) x) := by
    have := hper.intervalIntegral_add_eq (arg a) 0
    simpa only [zero_add, add_zero] using this
  have hRHS : ∀ θ : ℝ, (fun x => f (a * x + b)) (circleMap z ρ θ) =
      f (circleMap (a * z + b) (‖a‖ * ρ) (θ + arg a)) := fun θ => by
    simp only
    rw [key θ]
  unfold Real.circleAverage
  congr 1
  simp only [hRHS]
  exact (h2.trans h3).symm

/-- Pairings: `|a|⁻² ⟨φ ∘ F⁻¹, f⟩ = ⟨φ, f ∘ F⟩` for every `f` (no integrability needed). -/
theorem smear_affine_pairing {a : ℂ} (ha : a ≠ 0) (b : ℂ) (φ f : ℂ → ℝ) :
    (‖a‖ ^ 2)⁻¹ * (GFFObservable.pairing (fun y => φ ((y - b) / a))).smear f =
      (GFFObservable.pairing φ).smear (fun x => f (a * x + b)) := by
  have h : ∫ u, φ u * f (a * u + b) = (‖a‖ ^ 2)⁻¹ * ∫ x, φ ((x - b) / a) * f x := by
    have := integral_affine_complex ha b (fun x => φ ((x - b) / a) * f x)
    simpa only [add_sub_cancel_right, mul_div_cancel_left₀ _ ha] using this
  simp only [GFFObservable.smear]
  rw [h]

/-- Circles: `⟨circle(|a| r, a z + b), f⟩ - ⟨circle(|a|, b), f⟩ = ⟨circle(r, z), f ∘ F⟩ - ⟨circle(1, 0), f ∘ F⟩`
(the centring of `hcirc` at `(|a|, b)` is the centring at the unit circle after pull-back). -/
theorem smear_affine_circle_sub {a : ℂ} (b z : ℂ) (r : ℝ) (f : ℂ → ℝ) :
    (GFFObservable.circle (‖a‖ * r) (a * z + b)).smear f - (GFFObservable.circle ‖a‖ b).smear f =
      (GFFObservable.circle r z).smear (fun x => f (a * x + b)) -
        (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
  have h0 : (GFFObservable.circle ‖a‖ b).smear f = (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
    have := circleAverage_affine_comp (a := a) b f 0 1
    simp only [mul_one, mul_zero, zero_add] at this
    exact this
  have h1 : (GFFObservable.circle (‖a‖ * r) (a * z + b)).smear f =
      (GFFObservable.circle r z).smear (fun x => f (a * x + b)) :=
    circleAverage_affine_comp (a := a) b f z r
  rw [h0, h1]

end HarmonicBalls
