import HarmonicBalls.FirstPass.S11r.VIdentity

/-!
# The rooted disk identity with an explicit scalar

Step 2 of the local agreement route for the rooted identity (20). For a disk `V = ball c r` with `0 ∉ closedBall c r`,
a root `z` with `r < R < dist z c` and `closedBall c R ⊆ ball 0 1`, and the decoder `(ρ, M)` of `V`,
`vIdentity_rooted_weylScaling` (S11r/VIdentity.lean) gives almost surely some scalar `b > 0` with
`M (obs_V f_z) = b · D_{f_z}` on `V × V`. Here the scalar is explicit and does not depend on the cutoff:
`b = exp(-ξ ((h, ρ) - γ ∫ log|w - z| ρ(w) dw))`, where `(h, ρ) = (h^ℂ, ρ) - α ∫ ρ log|·|` is the pairing of the field
`h = h^ℂ - α log|·|`. This is the zero-insertion pairing of the shifted field `h^ℂ + g` with any cutoff `g` that equals
`-α log|·| - γ log|· - z|` on `V` (`fieldPairing_addFunPairing_of_eqOn_rootedWeight`).

* `fieldPairing_addFunPairing_of_eqOn_rootedWeight`: the pairing identity for a test function supported in `V`;
* `vIdentity_rooted_weylScaling_explicit`: the rooted identity on `V` with the explicit scalar, for a given cutoff `g`;
* `vIdentity_rooted_weylScaling_explicit_of_margin`: the same, with the cutoff supplied by `exists_rooted_cutoff`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **Pairing of the shifted field.** Let `ρ` be a test function supported in `V`, with `0 ∉ V` and `z ∉ V`, and let
`g = -α log|·| - γ log|· - z|` on `V`. Then the zero-insertion pairing of `h^ℂ + g` with `ρ` is the pairing of the field
`h = h^ℂ - α log|·|` with `ρ`, minus `γ ∫ log|w - z| ρ(w) dw`. -/
theorem fieldPairing_addFunPairing_of_eqOn_rootedWeight {V : Set ℂ} {α γ : ℝ} {z : ℂ} (T : (ℂ → ℝ) → ℝ)
    {g ρ : ℂ → ℝ} (hρ : IsTestFunction V ρ) (hV0 : (0 : ℂ) ∉ V) (hzV : z ∉ V)
    (hg : ∀ x ∈ V, g x = -α * Real.log ‖x‖ - γ * Real.log ‖x - z‖) :
    fieldPairing 0 (addFunPairing T g) ρ = fieldPairing α T ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w := by
  have hzero : ∀ x, x ∉ V → ρ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hρ.2.2 h))
  have hI0 : Integrable (fun x => ρ x * Real.log ‖x‖) := by
    simpa using integrable_test_mul_log_sub hρ hV0
  have hIz : Integrable (fun x => ρ x * Real.log ‖x - z‖) := integrable_test_mul_log_sub hρ hzV
  have hpt : ∀ x, g x * ρ x = -α * (ρ x * Real.log ‖x‖) + (-γ) * (ρ x * Real.log ‖x - z‖) := by
    intro x
    by_cases hx : x ∈ V
    · rw [hg x hx]; ring
    · rw [hzero x hx]; simp
  have hcomm : (fun w => Real.log ‖w - z‖ * ρ w) = fun w => ρ w * Real.log ‖w - z‖ := by
    funext w; ring
  have hint : ∫ x, g x * ρ x =
      -α * (∫ x, ρ x * Real.log ‖x‖) + (-γ) * (∫ x, ρ x * Real.log ‖x - z‖) := by
    simp_rw [hpt]
    rw [integral_add (hI0.const_mul _) (hIz.const_mul _), integral_const_mul, integral_const_mul]
  unfold fieldPairing addFunPairing
  rw [hcomm, hint]
  ring

/-- **Rooted identity (20) on a disk avoiding the root, with the explicit scalar.** Under the hypotheses of
`vIdentity_rooted_weylScaling`, almost surely, for every pair `p ∈ V × V`, the decoder `M` of `V = ball c r` applied to
the rooted Campbell observation equals `exp(-ξ ((h, ρ) - γ ∫ log|w - z| ρ(w) dw))` times the internal metric on `V` of the
Weyl scaling of `𝔇 (hC ω)` by the rooted weight `f_z = -α log|·| - γ log|· - z| + γ log max(1, |·|)`. -/
theorem vIdentity_rooted_weylScaling_explicit {γ ξ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c z : ℂ} {r : ℝ}
    (hr : 0 < r)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (ρ : ℂ → ℝ) (hρT : IsTestFunction (ball c r) ρ)
    (M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ)
    (hMm : Measurable M)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
        ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
          ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
            internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2)
    {R : ℝ} (hrR : r < R) (hpR : R < dist z c)
    (hU : closedBall c R ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r)
    (g : ℂ → ℝ) (hgsm : ContDiff ℝ (⊤ : ℕ∞) g) (hgcomp : HasCompactSupport g)
    (hgcirc : Real.circleAverage g 0 1 = 0)
    (hgz : ∀ x ∈ ball c r, g x = -α * Real.log ‖x‖ - γ * Real.log ‖x - z‖)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
      ENNReal.ofReal (M (campbellReferenceObs γ α (ball c r) (hC ω) z).2 p) =
        ENNReal.ofReal (Real.exp (-ξ * (fieldPairing α (hC ω) ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w))) *
          internalMetric
            (fun u v => (weylScaling (𝔇 (hC ω)) ξ
              (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
            (ball c r) p.1.1 p.1.2 := by
  have hV1 : ∀ x ∈ ball c r, ‖x‖ < 1 := fun x hx => by
    have hxR : x ∈ closedBall c R := by
      rw [mem_ball] at hx
      rw [mem_closedBall]
      linarith [dist_comm x c]
    have := hU hxR
    rwa [mem_ball_zero_iff] at this
  have hV0 : (0 : ℂ) ∉ ball c r := fun h => h0 (ball_subset_closedBall h)
  have hzV : z ∉ ball c r := fun hz => by
    rw [mem_ball] at hz
    linarith [dist_comm z c]
  have hVc : IsConnected (ball c r) := (convex_ball c r).isConnected ⟨c, mem_ball_self hr⟩
  have hfg : ∀ x ∈ ball c r, g =ᶠ[nhds x]
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) := by
    intro x hx
    refine Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) (fun y hy => ?_)
    simp [hgz y hy, max_eq_left (hV1 y hy).le]
  have key := vIdentity_rooted hγ0 hγ2 h𝔇 hPhi hCM ρ hρT M hMm hid hrR hpR hU h0 g hgsm hgcomp hgcirc hgz
    Ω P hC hcirc hGFF
  have hE0 := FirstPassS11aa.ae_isEuclideanLengthMetric_universe h𝔇 hGFF (0 : ℂ → ℝ) continuous_zero
  simp only [addFunPairing_zero_fun] at hE0
  have hEg := FirstPassS11aa.ae_isEuclideanLengthMetric_universe h𝔇 hGFF g hgsm.continuous
  have hW := FirstPassS11aa.ae_weylScaling_universe h𝔇 hGFF
  filter_upwards [key, hE0, hEg, hW] with ω hω hE0ω hEgω hWω
  intro p
  have hmetric : 𝔇 (addFunPairing (hC ω) g) = fun u v => (weylScaling (𝔇 (hC ω)) ξ g u v).toReal := by
    funext u v
    have h2 : 0 ≤ 𝔇 (addFunPairing (hC ω) g) u v := by
      have h1 := hEgω.triangle u v u
      have h3 := hEgω.self_eq_zero u
      have h4 := hEgω.symm u v
      linarith
    rw [← hWω g hgsm.continuous u v, ENNReal.toReal_ofReal h2]
  have hR1 := RootedLocal.internalMetric_weylScaling_eq_of_eventuallyEq (ξ := ξ) hE0ω hgsm.continuous hgcomp
    isOpen_ball hVc hfg (x := p.1.1) (y := p.1.2)
  rw [hω p, hmetric, hR1, fieldPairing_addFunPairing_of_eqOn_rootedWeight (hC ω) hρT hV0 hzV hgz]

/-- **Rooted identity (20) on a disk avoiding the root, explicit scalar, cutoff supplied.** The same conclusion as
`vIdentity_rooted_weylScaling_explicit`, with the cutoff `g` taken from `exists_rooted_cutoff`; only the margin
`r < R < dist z c` with `closedBall c R ⊆ ball 0 1` and `0 ∉ closedBall c r` is assumed. -/
theorem vIdentity_rooted_weylScaling_explicit_of_margin {γ ξ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {c z : ℂ}
    {r : ℝ} (hr : 0 < r)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (ρ : ℂ → ℝ) (hρT : IsTestFunction (ball c r) ρ)
    (M : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) ℝ)
    (hMm : Measurable M)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
        ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
          ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
            internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2)
    {R : ℝ} (hrR : r < R) (hpR : R < dist z c)
    (hU : closedBall c R ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
      ENNReal.ofReal (M (campbellReferenceObs γ α (ball c r) (hC ω) z).2 p) =
        ENNReal.ofReal (Real.exp (-ξ * (fieldPairing α (hC ω) ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w))) *
          internalMetric
            (fun u v => (weylScaling (𝔇 (hC ω)) ξ
              (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
            (ball c r) p.1.1 p.1.2 := by
  obtain ⟨g, hgsm, hgcomp, hgcirc, hgz⟩ := exists_rooted_cutoff α γ hr hrR hpR hU h0
  exact vIdentity_rooted_weylScaling_explicit hγ0 hγ2 hr h𝔇 hPhi hCM ρ hρT M hMm hid hrR hpR hU h0
    g hgsm hgcomp hgcirc hgz Ω P hC hcirc hGFF

end HarmonicBalls
