import HarmonicBalls.FirstPass.S8d.TailStep
import HarmonicBalls.FirstPass.S8c.WeylOffOrigin
import HarmonicBalls.FirstPass.S8c.TailTransfer
import HarmonicBalls.Draft.Section8
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proposed.LQG

/-! # FIRST-PASS result 8.2 (fp-S8d-8-2-from-chatgpt-proof, owner n4): `firstPass_8_2`

Result 8.2 of "Harmonic balls in Liouville quantum gravity" (Bou-Rabee–Gwynne, arXiv:2208.11795):
`TypicalPointManyGoodScalesStmt` (Draft/Section8.lean:74). The route is the one of the ChatGPT proof of Lemma 8.2
(notes/fp-gaps/CHATGPT-8-2-proof.md, rated CORRECT by the independent referee): the local count of good scales is reduced
to the phase tail `LocalPhaseTailStep` (FirstPass/S8c/PhaseTail.lean), which is proved in FirstPass/S8d/TailStep.lean on
the profile space `C(CircleParameter, ℝ)` (the circle profile of the field, with the continuous circle dilation as
measure-preserving ergodic map). The reduction from the tail to the statement is the S8c argument, reproduced here
verbatim (`FirstPass/S8c.lean`, which we do not import, to avoid a name clash with its conditional theorem).

Hypotheses are the frozen inputs and the Draft or Proposed statements: `hL1`, `hfull`, `hWeyl`, `hEx`, `hN` (as in S8c),
`hL67` (Draft VeryGoodAnnulusProbabilityStmt), `hAff`, `hCC` (Proposed coordinate-change inputs, universal form),
`hE1` (profile measurability of the LQG measure, E1), `hE3` (product ergodicity of the doubling map, E3, universe 0),
`hB` (Birkhoff, universe 0), `hU` (uniqueness of Radon measures, flagged for operator review). -/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- Result 8.2 (FIRST PASS): for every many-good-scales statement at typical points. -/
theorem firstPass_8_2 (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hL67 : VeryGoodAnnulusProbabilityStmt.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) (hU : RadonIntegralUniqueFrozen) :
    TypicalPointManyGoodScalesStmt.{u} := by
  have hTail : LocalPhaseTailStep.{u} :=
    s8d_localPhaseTailStep hfull hWeyl hEx hL67 hAff hCC hE1 hE3 hB hU
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
