import HarmonicBalls.FirstPass.S8c.WeylOffOrigin
import HarmonicBalls.FirstPass.S8c.TailTransfer
import HarmonicBalls.Draft.Section8
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proposed.LQG

/-! # FIRST-PASS result 8.2 (`TypicalPointManyGoodScalesStmt`, Lemma 8.2, lemma:mu_h-doubling-and-harnack)

`firstPass_8_2` proves the Draft statement `TypicalPointManyGoodScalesStmt` from:
* the FROZEN local joint field-measure identification `LocalRootedFieldMeasureDomination` (L1, DMS A.10 local form);
* the FROZEN Weyl relation off the origin `LocalLQGInsertionWeylOffOrigin` (standard; locator pending);
* the Draft full-support statement `LQGMeasureFullSupportStmt` (Draft/Section2);
* the Proposed existence and non-atomicity of LQG measures (`LQGMeasureExistence`, `LQGMeasureNonatomic`,
  Proposed/LQG.lean; explicit literature inputs pending operator source-check);
* the NEW, OPEN phase tail `LocalPhaseTailStep` (G-8-2 section 3, eq. (7)-(8)); it is an input and is NOT proved here.

L2 (the unit good-annulus measurability) is discharged by `GoodEventPointPolarity.lean`; the Weyl comparison off the
origin is derived from the frozen relation; the local transfer is `localRoot_ae_eventually_count_final`
(WeylOffOrigin.lean) and `localReference_ae_mem_of_tail` (TailTransfer.lean).
-/

open MeasureTheory ProbabilityTheory Metric Set Filter

namespace HarmonicBalls

universe u

/-- FIRST-PASS result 8.2 from the frozen local inputs, the Proposed existence and non-atomicity inputs, and the
open phase tail `LocalPhaseTailStep`. -/
theorem firstPass_8_2 (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hTail : LocalPhaseTailStep.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc) :
    TypicalPointManyGoodScalesStmt.{u} := by
  intro γ α₀ hγ0 hγ2 hα βm hβ
  obtain ⟨C₃, hC₃, hT⟩ := hTail γ hγ0 hγ2 βm hβ
  refine ⟨C₃, hC₃, fun ζ hζ b hb => ?_⟩
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1, h2, h3, h4, N₁, hN₁, hrest⟩ := hT ζ hζ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1, h2, h3, h4, N₁, by omega, fun N₀ hN₀ => ?_⟩
  obtain ⟨m, hm, hfin⟩ := hrest N₀ hN₀
  refine ⟨m, hm, fun Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hγQ : γ < lqgQ γ := by
    unfold lqgQ
    have hprod : 0 < (2 - γ) * (2 + γ) := mul_pos (by linarith) (by linarith)
    have hdiv : γ / 2 < 2 / γ := (div_lt_div_iff₀ (by norm_num) hγ0).2 (by nlinarith)
    linarith
  have hQ0 : (0 : ℝ) < lqgQ γ := by linarith
  obtain ⟨ν, hν⟩ := hEx Ω P γ γ hC hcirc hGFF hγ0 hγ2 hγQ
  obtain ⟨lam, hlam⟩ := hEx Ω P γ 0 hC hcirc hGFF hγ0 hγ2 hQ0
  have hTailN := hfin Ω P hC hcirc ν hGFF hν
  have hposν : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → 0 < ν ω (ball 0 r) := by
    filter_upwards [hfull γ γ hγ0 hγ2 hγQ Ω P hC hcirc ν hGFF hν] with ω hω r hr
    exact hω _ isOpen_ball (nonempty_ball.mpr hr)
  have hlocν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  exact localRoot_ae_eventually_count_final hL1 hfull hWeyl P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2
    hα hμ hν hlam (hN Ω P γ α₀ hC hcirc) βm N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha.1
    (fun j hj => localReference_ae_mem_of_tail P ν βm N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hTailN
      hposν hlocν j hj)

#print axioms firstPass_8_2

end HarmonicBalls
