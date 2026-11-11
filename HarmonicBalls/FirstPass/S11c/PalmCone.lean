import HarmonicBalls.Draft.Section11
import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation

/-!
# Local Palm comparison for cone-mass events under a continuous density

Let `μ' = exp(γ v) · μ` with `a ≤ v ≤ b` on the ball `B_{6r}(z)` and `γ ≥ 0`. Then the cone-mass event
`coneMassEvent μ Q M r z` implies `coneMassEvent μ' Q (M e^{γ(a-b)}) r z`. Only the two bounds on the ball enter: the
annular Green potential is at most `e^{γb}` times the unweighted one, and the cone mass is at least `e^{γa}` times the
unweighted one. Pure measure theory; the identity `μ_{f+v} = e^{γv} μ_f` locally is an input of the proof of Lemma 11.7.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Lower bound: a density at least `lo` on the ball `B_ρ(z)` gives mass at least `lo` times the mass of any subset of
the ball. -/
lemma mul_measure_le_withDensity_of_ball (μ : Measure ℂ) [SFinite μ] {d : ℂ → ℝ≥0∞} (hd : Measurable d)
    {z : ℂ} {ρ : ℝ} {lo : ℝ≥0∞} (hlo : ∀ y ∈ ball z ρ, lo ≤ d y) {s : Set ℂ} (hs : s ⊆ ball z ρ) :
    lo * μ s ≤ μ.withDensity d s :=
  calc lo * μ s = ∫⁻ _ in s, lo ∂μ := (setLIntegral_const s lo).symm
    _ ≤ ∫⁻ y in s, d y ∂μ := setLIntegral_mono hd (fun y hy => hlo y (hs hy))
    _ = μ.withDensity d s := (withDensity_apply' d s).symm

/-- Upper bound: a density at most `hi` on the ball `B_{6r}(z)` bounds the annular Green potential at scales `(3r, 6r)`
by `hi` times the unweighted one. -/
lemma annulusGreenPotentialSup_withDensity_le (μ : Measure ℂ) {d : ℂ → ℝ≥0∞} (hd : Measurable d) (z : ℂ) (r : ℝ)
    {hi : ℝ≥0∞} (hhi : ∀ y ∈ ball z (6 * r), d y ≤ hi) :
    annulusGreenPotentialSup (μ.withDensity d) z (3 * r) (6 * r) ≤
      hi * annulusGreenPotentialSup μ z (3 * r) (6 * r) := by
  unfold annulusGreenPotentialSup
  refine iSup₂_le fun x hx => ?_
  have hA : MeasurableSet (annulus z (3 * r) (6 * r)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hsub : annulus z (3 * r) (6 * r) ⊆ ball z (6 * r) := fun y hy => by
    unfold annulus at hy
    exact hy.1
  have hf : Measurable (fun y : ℂ => if y = x then ∞ else
      ENNReal.ofReal (greenFunction (ball z (6 * r)) x y)) :=
    Measurable.ite (measurableSet_singleton x) measurable_const
      ((measurable_greenFunction isOpen_ball x).ennreal_ofReal)
  calc ∫⁻ y in annulus z (3 * r) (6 * r), (if y = x then ∞ else
        ENNReal.ofReal (greenFunction (ball z (6 * r)) x y)) ∂(μ.withDensity d)
      = ∫⁻ y in annulus z (3 * r) (6 * r), d y * (if y = x then ∞ else
        ENNReal.ofReal (greenFunction (ball z (6 * r)) x y)) ∂μ :=
        setLIntegral_withDensity_eq_setLIntegral_mul μ hd hf hA
    _ ≤ ∫⁻ y in annulus z (3 * r) (6 * r), hi * (if y = x then ∞ else
        ENNReal.ofReal (greenFunction (ball z (6 * r)) x y)) ∂μ := by
        refine setLIntegral_mono (measurable_const.mul hf) fun y hy => ?_
        have h1 := hhi y (hsub hy)
        gcongr
    _ = hi * ∫⁻ y in annulus z (3 * r) (6 * r), (if y = x then ∞ else
        ENNReal.ofReal (greenFunction (ball z (6 * r)) x y)) ∂μ :=
        lintegral_const_mul hi hf
    _ ≤ hi * ⨆ x' ∈ annulus z (3 * r) (6 * r), ∫⁻ y in annulus z (3 * r) (6 * r),
        (if y = x' then ∞ else ENNReal.ofReal (greenFunction (ball z (6 * r)) x' y)) ∂μ := by
        gcongr
        exact le_iSup₂ (f := fun x' (_ : x' ∈ annulus z (3 * r) (6 * r)) =>
          ∫⁻ y in annulus z (3 * r) (6 * r),
            (if y = x' then ∞ else ENNReal.ofReal (greenFunction (ball z (6 * r)) x' y)) ∂μ) x hx

/-- The local Palm comparison for cone-mass events (Step 4 of the proof of Lemma 11.7). On the ball `B_{6r}(z)`, with
`a ≤ v ≤ b` and `γ ≥ 0`, the density `exp(γ v)` turns the cone-mass event at constant `M` into the one at constant
`M exp(γ(a-b))`. -/
theorem coneMassEvent_withDensity_exp {μ : Measure ℂ} [SFinite μ] {Q : Set ℂ} {γ M r a b : ℝ} {z : ℂ}
    (hγ : 0 ≤ γ) (hM : 0 ≤ M) (hr : 0 < r) {v : ℂ → ℝ} (hv : Measurable v)
    (hlo : ∀ y ∈ ball z (6 * r), a ≤ v y) (hhi : ∀ y ∈ ball z (6 * r), v y ≤ b)
    (h : coneMassEvent μ Q M r z) :
    coneMassEvent (μ.withDensity fun y => ENNReal.ofReal (Real.exp (γ * v y))) Q
      (M * Real.exp (γ * (a - b))) r z := by
  have hd : Measurable fun y => ENNReal.ofReal (Real.exp (γ * v y)) := by fun_prop
  have hlo' : ∀ y ∈ ball z (6 * r), ENNReal.ofReal (Real.exp (γ * a)) ≤
      ENNReal.ofReal (Real.exp (γ * v y)) :=
    fun y hy => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hlo y hy) hγ))
  have hhi' : ∀ y ∈ ball z (6 * r), ENNReal.ofReal (Real.exp (γ * v y)) ≤
      ENNReal.ofReal (Real.exp (γ * b)) :=
    fun y hy => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hhi y hy) hγ))
  have hann : annulus z r (2 * r) ⊆ ball z (6 * r) := fun y hy => by
    unfold annulus at hy
    exact ball_subset_ball (by linarith) hy.1
  have hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ ball z (6 * r) := fun y hy => hann hy.1
  have hmass := mul_measure_le_withDensity_of_ball μ hd hlo' hcone
  have hgreen := annulusGreenPotentialSup_withDensity_le μ hd z r hhi'
  have hkey : ENNReal.ofReal (M * Real.exp (γ * (a - b))) * ENNReal.ofReal (Real.exp (γ * b))
      = ENNReal.ofReal (Real.exp (γ * a)) * ENNReal.ofReal M := by
    have hX : 0 ≤ M * Real.exp (γ * (a - b)) := mul_nonneg hM (Real.exp_pos _).le
    have e : Real.exp (γ * (a - b)) * Real.exp (γ * b) = Real.exp (γ * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    calc M * Real.exp (γ * (a - b)) * Real.exp (γ * b)
        = M * (Real.exp (γ * (a - b)) * Real.exp (γ * b)) := by ring
      _ = Real.exp (γ * a) * M := by rw [e]; ring
  unfold coneMassEvent at h ⊢
  calc ENNReal.ofReal (M * Real.exp (γ * (a - b))) * annulusGreenPotentialSup
        (μ.withDensity fun y => ENNReal.ofReal (Real.exp (γ * v y))) z (3 * r) (6 * r)
      ≤ ENNReal.ofReal (M * Real.exp (γ * (a - b))) *
          (ENNReal.ofReal (Real.exp (γ * b)) * annulusGreenPotentialSup μ z (3 * r) (6 * r)) := by
        gcongr
    _ = (ENNReal.ofReal (M * Real.exp (γ * (a - b))) * ENNReal.ofReal (Real.exp (γ * b))) *
          annulusGreenPotentialSup μ z (3 * r) (6 * r) := (mul_assoc _ _ _).symm
    _ = (ENNReal.ofReal (Real.exp (γ * a)) * ENNReal.ofReal M) *
          annulusGreenPotentialSup μ z (3 * r) (6 * r) := by rw [hkey]
    _ = ENNReal.ofReal (Real.exp (γ * a)) *
          (ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r)) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (Real.exp (γ * a)) * μ (annulus z r (2 * r) ∩ coneAt Q z) := by
        gcongr
    _ ≤ (μ.withDensity fun y => ENNReal.ofReal (Real.exp (γ * v y))) (annulus z r (2 * r) ∩ coneAt Q z) :=
        hmass

end HarmonicBalls
