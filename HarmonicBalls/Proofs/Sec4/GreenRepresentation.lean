import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Steps.Sec4.LeastSupersolutionHolder

/-!
# Green representation on a disc (`GreenRepresentationBallStep`)

`greenRepresentationBallStep_holds`: if `σ ≤ μ` on `B_R` for a measure `μ` with the volume growth condition, `w` is
continuous on `closedBall 0 R`, `w = 0` on `∂B_R` and `Δw = σ` on `B_R`, then `w = -∫_{B_R} G_{B_R}(·,y) σ(dy)` on
`B_R` (Riesz decomposition on a disc, AG01 Thm 4.4.1, used at line 732 of the paper).

Route: `σ|_{B_R} + μ` has the volume growth condition with upper exponent `β⁺/2` (`VolumeGrowth.add_of_le`), so the
Green potential `p` of `σ|_{B_R}` is the difference of two potentials with `Δ = -(σ|_{B_R} + μ)` and `Δ = -μ`
(`GreenPotentialBallLaplacianStep`), continuous on the closed disc (`GreenPotentialBallContinuousStep`) and `0` on
`∂B_R` (Prop 2.3). Then `h = w + p` has `Δh = 0`, so `±h` are superharmonic (`SuperharmonicOfLaplacianLEStep`), and
the maximum principle on the disc (`le_zero_of_isSuperharmonicOn_neg`) gives `h = 0`. Symmetry of `G_{B_R}`
(`greenFunction_ball_comm`) puts the integral in the stated order.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ENNReal

/-- A measure dominated by a measure with the volume growth condition can be added to it, at the price of halving
the upper exponent. -/
theorem VolumeGrowth.add_of_le {μ ν : Measure ℂ} {R βm βp : ℝ} (hV : VolumeGrowth μ R βm βp) (hνμ : ν ≤ μ) :
    VolumeGrowth (ν + μ) R βm (βp / 2) := by
  obtain ⟨hβm, hβp, r₀, hr₀, h⟩ := hV
  have hr₁ : 0 < ((1 : ℝ) / 2) ^ (2 / βp) := by positivity
  refine ⟨hβm, half_pos hβp, min r₀ (((1 : ℝ) / 2) ^ (2 / βp)), lt_min hr₀ hr₁, fun r hr hr' z hz => ?_⟩
  obtain ⟨h1, h2⟩ := h r hr (lt_of_lt_of_le hr' (min_le_left _ _)) z hz
  have hsmall : r ^ (βp / 2) ≤ 1 / 2 := by
    have h3 := Real.rpow_le_rpow hr.le (lt_of_lt_of_le hr' (min_le_right _ _)).le (half_pos hβp).le
    have e : 2 / βp * (βp / 2) = 1 := by field_simp
    rwa [← Real.rpow_mul (by norm_num), e, Real.rpow_one] at h3
  have hkey : 2 * r ^ βp ≤ r ^ (βp / 2) := by
    have e : r ^ βp = r ^ (βp / 2) * r ^ (βp / 2) := by rw [← Real.rpow_add hr]; ring_nf
    have h0 : 0 ≤ r ^ (βp / 2) := Real.rpow_nonneg hr.le _
    rw [e]
    nlinarith
  have hr0 : 0 ≤ r ^ βp := Real.rpow_nonneg hr.le _
  refine ⟨h1.trans (by rw [Measure.add_apply]; exact le_add_self), ?_⟩
  calc (ν + μ) (ball z r) = ν (ball z r) + μ (ball z r) := Measure.add_apply _ _ _
    _ ≤ μ (ball z r) + μ (ball z r) := add_le_add_left (Measure.le_iff'.1 hνμ _) _
    _ ≤ ENNReal.ofReal (r ^ βp) + ENNReal.ofReal (r ^ βp) := add_le_add h2 h2
    _ = ENNReal.ofReal (2 * r ^ βp) := by rw [← ENNReal.ofReal_add hr0 hr0, two_mul]
    _ ≤ ENNReal.ofReal (r ^ (βp / 2)) := ENNReal.ofReal_le_ofReal hkey

/-- **Maximum principle on a disc.** If `f` is continuous on `closedBall 0 R`, `-f` is superharmonic on `B_R` and
`f ≤ 0` on `∂B_R`, then `f ≤ 0` on `B_R`. -/
theorem le_zero_of_isSuperharmonicOn_neg {R : ℝ} {f : ℂ → ℝ} (hfc : ContinuousOn f (closedBall 0 R))
    (hsup : IsSuperharmonicOn (ball 0 R) (-f)) (hb : ∀ x ∈ sphere (0 : ℂ) R, f x ≤ 0) :
    ∀ x ∈ ball (0 : ℂ) R, f x ≤ 0 := by
  set W := ball (0 : ℂ) R ∩ f ⁻¹' Ioi 0 with hW
  have hWo : IsOpen W := (hfc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hclW : closure W ⊆ closedBall 0 R :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  have hWe : W = ∅ := by
    refine eq_empty_of_pos_of_subMean (isBounded_ball.subset inter_subset_left) (hfc.mono hclW)
      (fun x hx => hx.2) (fun x hx => ?_) (fun x hx => ?_)
    · have hxc := hclW (frontier_subset_closure hx)
      rcases (mem_closedBall_zero_iff.1 hxc).lt_or_eq with hlt | heq
      · have hxW : x ∉ W := by
          rw [hWo.frontier_eq] at hx
          exact hx.2
        by_contra hpos
        exact hxW ⟨mem_ball_zero_iff.2 hlt, not_le.1 hpos⟩
      · exact hb x (mem_sphere_zero_iff_norm.2 heq)
    · obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo x hx
      have hsub : closedBall x (r / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hr)).trans hrW
      refine ⟨r / 2, half_pos hr, hsub, ?_⟩
      have h := (hsup.2 x hx.1 (r / 2) (half_pos hr) (hsub.trans inter_subset_left)).2
      rw [circleAverage_neg_fun, Pi.neg_apply] at h
      linarith
  intro x hx
  by_contra hpos
  have hxW : x ∈ W := ⟨hx, not_le.1 hpos⟩
  rw [hWe] at hxW
  exact hxW

/-- **Green representation on a disc** (`GreenRepresentationBallStep`). -/
theorem greenRepresentationBallStep_holds : GreenRepresentationBallStep := by
  intro μ hμ R βm βp hR hV σ w hle hw hw0 hLap
  set B := ball (0 : ℂ) R with hB
  have hBm : MeasurableSet B := measurableSet_ball
  set σ' := σ.restrict B with hσ'
  have hσ'μ : σ' ≤ μ := hle.trans Measure.restrict_le_self
  have hV' : VolumeGrowth (σ' + μ) R βm (βp / 2) := hV.add_of_le hσ'μ
  have hσμ' : σ' ≤ σ' + μ := Measure.le_add_right le_rfl
  have : IsLocallyFiniteMeasure σ' := Measure.isLocallyFiniteMeasure_of_le hσ'μ
  have hsumlf : IsLocallyFiniteMeasure (σ' + μ) := ⟨fun x => by
    obtain ⟨s, hs, hμs⟩ := μ.finiteAt_nhds x
    refine ⟨s, hs, ?_⟩
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨(Measure.le_iff'.1 hσ'μ s).trans_lt hμs, hμs⟩⟩
  have hσ'B : σ'.restrict B = σ' := by rw [hσ', Measure.restrict_restrict hBm, inter_self]
  have hint : ∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => greenFunction B y x) (σ'.restrict B) :=
    fun x hx => (integrable_greenFunction_ball_left hR hV' hx).mono_measure
      (Measure.restrict_mono subset_rfl hσμ')
  have hsplit : ∀ x ∈ closedBall (0 : ℂ) R,
      greenPotentialBall (σ' + μ) R x = greenPotentialBall σ' R x + greenPotentialBall μ R x := by
    intro x hx
    simp only [greenPotentialBall]
    rw [Measure.restrict_add, integral_add_measure (hint x hx) (integrable_greenFunction_ball_left hR hV hx)]
  have hΔsum := greenPotentialBallLaplacianStep_holds (σ' + μ) hsumlf R βm (βp / 2) hR hV'
  have hΔμ := greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV
  have hcsum := greenPotentialBallContinuousStep_holds (σ' + μ) hsumlf R βm (βp / 2) hR hV'
  have hcμ := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  set p := greenPotentialBall σ' R with hp
  have hpeq : EqOn (fun x => greenPotentialBall (σ' + μ) R x - greenPotentialBall μ R x) p (closedBall 0 R) :=
    fun x hx => by
      simp only [hsplit x hx]
      ring
  have hpc : ContinuousOn p (closedBall 0 R) := (hcsum.sub hcμ).congr fun x hx => (hpeq hx).symm
  have hpΔ : HasLaplacian p 0 σ' B := by
    have hd : HasLaplacian (fun x => greenPotentialBall (σ' + μ) R x - greenPotentialBall μ R x) 0 σ' B := by
      refine ⟨hΔsum.1.sub hΔμ.1, fun φ hφ => ?_⟩
      obtain ⟨-, hi1, e1⟩ := hΔsum.2 φ hφ
      obtain ⟨-, hiμ, e2⟩ := hΔμ.2 φ hφ
      refine ⟨integrable_zero_measure, hi1.mono_measure hσμ', ?_⟩
      have hfun : (fun x => (greenPotentialBall (σ' + μ) R x - greenPotentialBall μ R x) * Δ φ x) =
          fun x => greenPotentialBall (σ' + μ) R x * Δ φ x - greenPotentialBall μ R x * Δ φ x := by
        funext x
        ring
      rw [hfun, integral_sub (integrable_mul_laplacian hΔsum.1 hφ) (integrable_mul_laplacian hΔμ.1 hφ), e1, e2,
        integral_add_measure (hi1.mono_measure hσμ') hiμ]
      simp only [integral_zero_measure]
      ring
    exact hd.congr_eqOn hBm (hpeq.mono ball_subset_closedBall)
  -- `h = w + p` is harmonic
  have hhΔ : HasLaplacian (fun x => w x + p x) 0 0 B := by
    refine ⟨hLap.1.add hpΔ.1, fun φ hφ => ⟨integrable_zero_measure, integrable_zero_measure, ?_⟩⟩
    obtain ⟨-, -, e1⟩ := hLap.2 φ hφ
    obtain ⟨-, -, e2⟩ := hpΔ.2 φ hφ
    have hfun : (fun x => (w x + p x) * Δ φ x) = fun x => w x * Δ φ x + p x * Δ φ x := by
      funext x
      ring
    rw [hfun, integral_add (integrable_mul_laplacian hLap.1 hφ) (integrable_mul_laplacian hpΔ.1 hφ), e1, e2]
    have hσσ' : ∫ x, φ x ∂σ' = ∫ x, φ x ∂σ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)
    rw [hσσ']
    simp only [integral_zero_measure]
    ring
  have hhc : ContinuousOn (fun x => w x + p x) (closedBall 0 R) := hw.add hpc
  have hp0 : ∀ x ∈ sphere (0 : ℂ) R, p x = 0 := by
    intro x hx
    show ∫ y in ball (0 : ℂ) R, greenFunction (ball 0 R) y x ∂σ' = 0
    rw [setIntegral_congr_fun hBm (g := fun _ => (0 : ℝ))
      (fun y hy => ((greenFunctionBall R hR y hy).2.2.1 x hx).1)]
    simp
  have hLE1 : LaplacianLE (fun x => w x + p x) 0 B :=
    ⟨hhΔ.1, fun φ hφ _ _ => by
      rw [(hhΔ.2 φ hφ).2.2]
      simp⟩
  have hLE2 : LaplacianLE (fun x => -(w x + p x)) 0 B := by
    refine ⟨hhΔ.1.neg, fun φ hφ _ _ => ?_⟩
    have hfun : (fun x => -(w x + p x) * Δ φ x) = fun x => -((w x + p x) * Δ φ x) := by
      funext x
      ring
    rw [hfun, integral_neg, (hhΔ.2 φ hφ).2.2]
    simp
  have hsup1 := superharmonicOfLaplacianLEStep_holds B _ isOpen_ball (hhc.mono ball_subset_closedBall) hLE1
  have hsup2 := superharmonicOfLaplacianLEStep_holds B _ isOpen_ball
    (hhc.neg.mono ball_subset_closedBall) hLE2
  have hle0 := le_zero_of_isSuperharmonicOn_neg hhc hsup2 fun x hx => by
    simp [hw0 x hx, hp0 x hx]
  have hneg : -(fun x => -(w x + p x)) = fun x => w x + p x := by
    funext x
    simp
  have hge0 := le_zero_of_isSuperharmonicOn_neg (f := fun x => -(w x + p x)) hhc.neg
    (by rw [hneg]; exact hsup1) fun x hx => by simp [hw0 x hx, hp0 x hx]
  intro x hx
  have h1 : w x + p x ≤ 0 := hle0 x hx
  have h2 : -(w x + p x) ≤ 0 := hge0 x hx
  refine ⟨?_, ?_⟩
  · have := hint x (ball_subset_closedBall hx)
    rw [hσ'B] at this
    exact this.congr (Eventually.of_forall fun y => greenFunction_ball_comm R y x)
  · have hpx : p x = ∫ y in B, greenFunction B x y ∂σ := by
      show ∫ y in ball (0 : ℂ) R, greenFunction (ball 0 R) y x ∂σ' = _
      rw [hσ', Measure.restrict_restrict hBm, inter_self]
      exact integral_congr_ae (Eventually.of_forall fun y => greenFunction_ball_comm R y x)
    linarith

end HarmonicBalls
