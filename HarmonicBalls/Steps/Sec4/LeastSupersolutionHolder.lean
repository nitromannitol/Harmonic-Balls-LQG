import HarmonicBalls.Steps.Sec4.Basic
import HarmonicBalls.Steps.Sec4.GreenPotentialBallHolderStep

/-!
# Lemma 4.2 (odometer:cont, line 721): reduction to Sections 2-3, a Green representation step and step G4

`leastSupersolutionHolder_of_steps : LeastSupersolutionHolderStmt` (with [C8], exponent `α = α(γ, α₀)`).

## The printed proof (lines 730-733)

"By Lemma 3.2, `Δ v^z_t = μ_h|_Λ + ν|_{∂Λ}` and `ν` is absolutely continuous with respect to `μ_h` in `B_1`. Thus,
the claim follows by Proposition 2.5."

## Route in Lean

1. **Green representation** (`GreenRepresentationBallStep`, implicit in line 732). `v = v^z_t` is continuous on the
   closed ball (Lemma 3.1), vanishes on `∂B_1` (Lemma 3.4: `u = 0` there, and `G_{B_1}(z,·) = 0` off `B_1`) and
   `Δv = σ := μ_h|_Λ + ν|_{∂Λ}` on `B_1` (Lemma 3.2). Hence `v(x) = -∫_{B_1} G_{B_1}(x,y) σ(dy)` (Riesz
   decomposition on the disc). The paper leaves this step implicit.
2. **Density** (Lemma 3.2). `ν ≤ μ_h` on `B_1` and `Λ ∩ ∂Λ = ∅` give `σ ≤ μ_h` on `B_1`, so
   `σ|_{B_1} = ρ μ_h|_{B_1}` with a Radon-Nikodym density `0 ≤ ρ ≤ 1` (`Measure.rnDeriv_le_one_of_le`). The
   absolute continuity clause of Lemma 3.2 is implied by `ν ≤ μ_h`.
3. **Quantitative Proposition 2.5 (gap G4)** (`GreenPotentialBallHolderStep`). The Hölder seminorm of the Green
   potential of `ρ μ_h` is `≤ C ‖ρ‖_∞ ≤ C` with `C = C(μ_h)` and exponent `min (β⁺, 1) / 2`: the same `C` for all
   `t > 0` and `z ∈ B_1`. The step is proved in Steps/Sec4/GreenPotentialBallHolder.lean from c1's
   `VolumeGrowth.greenPotential_ball_holder`, but cannot be imported here (name clash with Steps/SecA).
4. **The exponent** ([C8]). `β⁺ = volumeGrowthExponentPlus γ α₀ = min {(2-γ)²/2, γ(Q-α₀)} / 2` is fixed before the
   probability space; the a.s. event is that of Input I2 for this `β⁺` (and `β⁻ = volumeGrowthExponentMinus γ α₀`).
   So `α = min (β⁺, 1) / 2` depends on `γ` and `α₀`, as [C8] requires (it cannot depend on `γ` only). The random
   constant is `C + 1 > 0`.

## Hypotheses consumed

Input I2, Lemmas 3.1, 3.2, 3.4 (Draft statements), `GreenRepresentationBallStep`, `GreenPotentialBallHolderStep`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- **Step (Green representation on a disc; Riesz decomposition, AG01 Thm 4.4.1 / Sec. 4.5).** Let `R > 0`, `σ`
a measure with `σ(B_R) < ∞` and `w` continuous on `closedBall 0 R`, zero on `∂B_R`, with `Δw = σ` on `B_R` in the
distributional sense. Then for `x ∈ B_R`, `y ↦ G_{B_R}(x,y)` is `σ`-integrable on `B_R` and
`w(x) = -∫_{B_R} G_{B_R}(x,y) σ(dy)`.

Re-carved (c1, 2026-11-03): `σ` is dominated on `B_R` by a measure `μ` with the volume growth condition, as in its
only use (`holder_of_hasLaplacian_le`, where `σ = Δ v^z_t ≤ μ_h`); then `σ(B_R) < ∞` and the Green potential of `σ`
is continuous with `Δ = -σ` (proved in Proofs/Sec4/GreenRepresentation.lean).

Used implicitly in the proof of Lemma 4.2 (line 732: `v^z_t` is minus the Green potential of its Laplacian).
Route: `p(x) = ∫_{B_R} G_{B_R}(x,y) σ(dy)` satisfies `Δp = -σ` (Prop 2.3 and Fubini); `w` is subharmonic and
continuous, hence `p < ∞` wherever `w > -∞`, i.e. everywhere (Riesz decomposition `w = -p + h` with `h` the least
harmonic majorant of `w`); `h` is the Poisson integral of `w|_{∂B_R} = 0`, so `h = 0`. Atoms of `σ` are excluded by
the finiteness of `w` (the junk value `G_{B_R}(x,x) = 0` is irrelevant). Difficulty: hard (2-3 rounds). -/
def GreenRepresentationBallStep : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ (σ : Measure ℂ) (w : ℂ → ℝ), σ.restrict (ball 0 R) ≤ μ.restrict (ball 0 R) → ContinuousOn w (closedBall 0 R) →
    (∀ x ∈ sphere (0 : ℂ) R, w x = 0) → HasLaplacian w σ 0 (ball 0 R) →
    ∀ x ∈ ball (0 : ℂ) R, IntegrableOn (greenFunction (ball 0 R) x) (ball 0 R) σ ∧
      w x = -∫ y in ball 0 R, greenFunction (ball 0 R) x y ∂σ

/-- **Hölder bound for functions with Laplacian `≤ μ`, deterministic form.** Under the volume growth condition on
`B_R` there is `C ≥ 0` such that every `w` continuous on the closed ball, zero on `∂B_R`, with `Δw = σ` on `B_R`
for a measure `σ ≤ μ` on `B_R`, satisfies `|w(x) - w(y)| ≤ C |x - y|^{min (β⁺,1)/2}` on `B_R`. The constant does
not depend on `w` or `σ`. -/
theorem holder_of_hasLaplacian_le (hRep : GreenRepresentationBallStep) (hHol : GreenPotentialBallHolderStep)
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ℂ → ℝ) (σ : Measure ℂ), ContinuousOn w (closedBall 0 R) →
      (∀ x ∈ sphere (0 : ℂ) R, w x = 0) → HasLaplacian w σ 0 (ball 0 R) →
      σ.restrict (ball 0 R) ≤ μ.restrict (ball 0 R) →
      ∀ x ∈ ball (0 : ℂ) R, ∀ y ∈ ball (0 : ℂ) R, |w x - w y| ≤ C * ‖x - y‖ ^ (min βp 1 / 2) := by
  obtain ⟨C, hC, hH⟩ := hHol μ hμ R βm βp hR hV
  refine ⟨C, hC, fun w σ hw hw0 hLap hle x hx y hy => ?_⟩
  set B := ball (0 : ℂ) R with hB
  have hσB : σ B < ⊤ := by
    have h := Measure.le_iff'.1 hle univ
    rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ] at h
    exact h.trans_lt measure_ball_lt_top
  have : IsFiniteMeasure (σ.restrict B) := isFiniteMeasure_restrict.2 hσB.ne
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set ρ : ℂ → ℝ := fun y => ((σ.restrict B).rnDeriv (μ.restrict B) y).toReal with hρ_def
  have hac : σ.restrict B ≪ μ.restrict B := Measure.absolutelyContinuous_of_le hle
  have hrep : ∀ x', ∫ y in B, greenFunction B x' y ∂σ = ∫ y in B, greenFunction B x' y * ρ y ∂μ := by
    intro x'
    calc ∫ y in B, greenFunction B x' y ∂σ
        = ∫ y, ρ y * greenFunction B x' y ∂(μ.restrict B) := (integral_toReal_rnDeriv_mul hac).symm
      _ = ∫ y in B, greenFunction B x' y * ρ y ∂μ := by
          congr 1
          funext y
          exact mul_comm _ _
  have hρm : AEStronglyMeasurable ρ (μ.restrict B) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.aestronglyMeasurable
  have hρ1 : ∀ᵐ y ∂μ.restrict B, |ρ y| ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hle] with y hy
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hy)
  obtain ⟨-, hD⟩ := hH ρ 1 hρm zero_le_one hρ1
  have h := hD x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
  rw [mul_one] at h
  rw [(hRep μ hμ R βm βp hR hV σ w hle hw hw0 hLap x hx).2, (hRep μ hμ R βm βp hR hV σ w hle hw hw0 hLap y hy).2, hrep x, hrep y,
    neg_sub_neg, abs_sub_comm]
  exact h

/-- **Lemma 4.2 from Sections 2-3** (lines 730-733), with the representation step and the quantitative
Proposition 2.5 (G4); exponent `α = min (β⁺, 1) / 2`, `β⁺ = volumeGrowthExponentPlus γ α₀` ([C8]). -/
theorem leastSupersolutionHolder_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h31 : LeastSupersolutionMemStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (hRep : GreenRepresentationBallStep)
    (hHol : GreenPotentialBallHolderStep) : LeastSupersolutionHolderStmt.{u} := by
  intro γ α₀ hγ hγ2 hα
  obtain ⟨hβp, hβp', hβm⟩ := volumeGrowthExponents_mem hγ hγ2 hα
  refine ⟨min (volumeGrowthExponentPlus γ α₀) 1 / 2, half_pos (lt_min hβp one_pos), ?_⟩
  intro Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents hI2 hγ hγ2 hα hβp hβp' hβm hGFF hμ,
    h31 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h34 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω h1 h2 h4
  obtain ⟨C, hC0, hCH⟩ := holder_of_hasLaplacian_le hRep hHol hω.1 one_pos (hω.2 1 one_pos)
  refine ⟨C + 1, by linarith, fun t ht z hz x hx y hy => ?_⟩
  obtain ⟨hopen, -, ν, -, -, hle, hLap, -⟩ := h2 t 1 ht one_pos z hz
  have h := hCH _ _ (h1 t 1 ht one_pos z hz).2.1
    (fun x hx => leastSupersolution_eq_zero_of_mem_sphere (h4 1 t one_pos ht z hz).2.1 hx) hLap
    (restrict_add_restrict_frontier_le hopen measurableSet_ball hle) x hx y hy
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))

end HarmonicBalls
