import HarmonicBalls.Draft.Section2
import HarmonicBalls.Defs.Annuli
import HarmonicBalls.Proposed.LQG

/-!
# Base finiteness of the annular Green potential from HB Proposition 2.5 (fp-S11p, owner n4)

Bridges the Green-potential clause of Proposition 2.5 (`GreenPotentialHolderStmt`, Draft/Section2.lean; cited and used
as a hypothesis, as in `FirstPass/S5S7S8.lean`) to `annulusGreenPotentialSup` for the exponent-`0` base measure `μ₀`
of the singular LQG measure. This discharges the named hypothesis `hBase` of `FirstPass/S11p/FiniteWeighted.lean`
(Bou-Rabee-Gwynne, arXiv:2208.11795v3, Proposition 2.5; the annular potential is `SG_{3,6}`, Section 2).

Inputs: the whole-plane GFF `hGFF`; the exponent-`0` LQG measure `h₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀`; the
non-atomicity `hNa0 : LQGMeasureNonatomic P γ 0 hC hcirc` (Proposed, pending source-check). Non-atomicity is used only
to discard the diagonal `y = x`, where `annulusGreenPotentialSup` takes the value `+∞` while the Lean junk value of
`greenFunction` is not controlled by Proposition 2.5.

Argument. Take `O = B_6(0)` (smooth bounded) and `f = 1_{𝔸_{3,6}}` (bounded, measurable). The Hölder clause makes
`x ↦ ∫_O G_O(x,y) f(y) μ₀(dy)` continuous on the compact set `closure O`, hence bounded there by some `K`. For
`x ∈ 𝔸_{3,6}` this integral is `∫_{𝔸_{3,6}} G_O(x,y) μ₀(dy)`, with integrand `≥ 0` (`greenFunction_nonneg`) and
integrable (Proposition 2.5). Hence the annular supremum is at most `ofReal K`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

open scoped ContDiff in
/-- A disc `B_r(c)` with `r > 0` has a smooth nondegenerate defining function `‖z - c‖² - r²`
(copy of `isSmoothBoundedOpen_disc`, `Proofs/Sec6/FineSupportDisc.lean`, which is not imported here). -/
theorem isSmoothBoundedOpen_ball_S11p (c : ℂ) {r : ℝ} (hr : 0 < r) : IsSmoothBoundedOpen (ball c r) := by
  let ρ : ℂ → ℝ := fun z => ‖z - c‖ ^ 2 - r ^ 2
  refine ⟨isBounded_ball, ρ, ?_, ?_, ?_⟩
  · exact ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  · ext z
    simp only [mem_ball, dist_eq_norm, mem_ofPred_eq, ρ]
    have hn := norm_nonneg (z - c)
    constructor <;> intro h <;> nlinarith [sq_nonneg (‖z - c‖ - r)]
  · intro z hz hzero
    have hn : 0 < ‖z - c‖ ^ 2 := by dsimp [ρ] at hz; nlinarith [sq_pos_of_pos hr]
    have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L (z - c)) hzero
    have hf : HasFDerivAt ρ (2 • (innerSL ℝ (z - c)).comp
        (ContinuousLinearMap.id ℝ ℂ)) z := by
      exact (((hasFDerivAt_id z).sub_const c).norm_sq).sub_const _
    rw [hf.fderiv] at hd
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, inner_self_eq_norm_sq_to_K,
      zero_apply, nsmul_eq_mul] at hd
    exact (mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hn))) hd

/-- **Base finiteness (HB Proposition 2.5, Green clause).** For the exponent-`0` LQG measure `μ₀` of a whole-plane GFF,
almost surely `SG_{3,6}(μ₀) = annulusGreenPotentialSup (μ₀ ω) 0 3 6 ≠ ∞`. Inputs: `GreenPotentialHolderStmt` (cited,
Proposition 2.5), `LQGMeasureNonatomic` (Proposed, pending source-check). -/
theorem ae_annulusGreenPotentialSup_ne_top_base {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ₀ : Ω → Measure ℂ} (h₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hNa0 : LQGMeasureNonatomic P γ 0 hC hcirc) (hholder : GreenPotentialHolderStmt.{u}) :
    ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ₀ ω) 0 3 6 ≠ ⊤ := by
  have hQ0 : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hH := hholder γ 0 hγ0 hγ2 hQ0 Ω P hC hcirc μ₀ hGFF h₀
  have hN := hNa0 hGFF hγ0 hγ2 hQ0 μ₀ h₀
  filter_upwards [hH, hN] with ω hHω hNω
  have hOs : IsSmoothBoundedOpen (ball (0 : ℂ) 6) := isSmoothBoundedOpen_ball_S11p 0 (by norm_num)
  have hAm : MeasurableSet (annulus (0 : ℂ) 3 6) := by
    unfold annulus; exact measurableSet_ball.diff measurableSet_closedBall
  have hAO : annulus (0 : ℂ) 3 6 ⊆ ball (0 : ℂ) 6 := fun z hz => hz.1
  set f : ℂ → ℝ := (annulus (0 : ℂ) 3 6).indicator (fun _ => (1 : ℝ)) with hf
  have hfA : ∀ y ∈ annulus (0 : ℂ) 3 6, f y = 1 := fun y hy => indicator_of_mem hy _
  have hfm : MemLp f ⊤ ((μ₀ ω).restrict (closure (ball (0 : ℂ) 6))) := by
    refine memLp_top_of_bound (measurable_const.indicator hAm).aestronglyMeasurable 1
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ annulus (0 : ℂ) 3 6
    · rw [hfA y hy]; norm_num
    · rw [hf, indicator_of_notMem hy]; norm_num
  obtain ⟨hint, C, r, hr, hHolF⟩ := hHω (ball (0 : ℂ) 6) hOs f hfm
  obtain ⟨K, hK⟩ := (isBounded_ball.isCompact_closure).exists_bound_of_continuousOn
    (hHolF.continuousOn hr)
  -- on the annulus the Hölder integrand is the plain integral over the annulus
  have hF : ∀ x ∈ annulus (0 : ℂ) 3 6,
      (∫ y in ball (0 : ℂ) 6, greenFunction (ball (0 : ℂ) 6) x y * f y ∂(μ₀ ω)) =
        ∫ y in annulus (0 : ℂ) 3 6, greenFunction (ball (0 : ℂ) 6) x y ∂(μ₀ ω) := by
    intro x _
    have hfun : (fun y => greenFunction (ball (0 : ℂ) 6) x y * f y) =
        (annulus (0 : ℂ) 3 6).indicator (fun y => greenFunction (ball (0 : ℂ) 6) x y) := by
      funext y
      by_cases hy : y ∈ annulus (0 : ℂ) 3 6
      · rw [hfA y hy, mul_one, indicator_of_mem hy]
      · rw [hf, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
    rw [hfun, setIntegral_indicator hAm, inter_eq_right.mpr hAO]
  have hIA : ∀ x ∈ closure (ball (0 : ℂ) 6),
      IntegrableOn (fun y => greenFunction (ball (0 : ℂ) 6) x y) (annulus (0 : ℂ) 3 6) (μ₀ ω) := by
    intro x hx
    refine ((hint x hx).mono_set hAO).congr_fun (fun y hy => ?_) hAm
    simp only [hfA y hy, mul_one]
  -- the diagonal `y = x` is `μ₀`-null
  refine ne_top_of_le_ne_top (show ENNReal.ofReal K ≠ ⊤ from ENNReal.ofReal_ne_top) ?_
  unfold annulusGreenPotentialSup
  refine iSup₂_le fun x hx => ?_
  have hxcl : x ∈ closure (ball (0 : ℂ) 6) := subset_closure (hAO hx)
  have hae : ∀ᵐ y ∂(μ₀ ω), y ≠ x := ae_iff.mpr (by simpa using hNω x)
  have hdiag : (∫⁻ y in annulus (0 : ℂ) 3 6,
      (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball (0 : ℂ) 6) x y)) ∂(μ₀ ω)) =
      ∫⁻ y in annulus (0 : ℂ) 3 6, ENNReal.ofReal (greenFunction (ball (0 : ℂ) 6) x y) ∂(μ₀ ω) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hae] with y hy
    simp [hy]
  rw [hdiag, ← ofReal_integral_eq_lintegral_ofReal (hIA x hxcl)
    (ae_restrict_of_ae (Eventually.of_forall fun y => greenFunction_nonneg isBounded_ball x y))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hF x hx]
  exact (Real.le_norm_self _).trans (hK x hxcl)

end HarmonicBalls

#print axioms HarmonicBalls.ae_annulusGreenPotentialSup_ne_top_base
