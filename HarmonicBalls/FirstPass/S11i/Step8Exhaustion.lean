import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8PhysicalWindow
import HarmonicBalls.FirstPass.S11i.Step8CorrectedMarked
import HarmonicBalls.FirstPass.S11i.AnnularWeylAbsCont
import HarmonicBalls.FirstPass.S11i.HzoomScale
import HarmonicBalls.FirstPass.S11r.MarkedObs

/-!
# Exhaustion of the punctured unit disc and the unit-ball frequency (Step 8, fp-S11i-11-13f, n3)

* `exists_validBall_of_ne_zero`: a countable family of rational balls `ball (ballCen p) (ballRad p)` covers `ball 0 1 \ {0}`, each
  with `ball (ballCen p) (2 ballRad p) ⊆ ball 0 1` and `0 ∉ ball (ballCen p) (2 ballRad p)` (`ValidBall`).
* `ae_forall_of_cover`: a countable exhaustion of almost-sure statements over the cover, with the atom at `0` removed.
* `ae_marked_local_transfer_on`: the corrected marked transfer (`Step8CorrectedMarked.lean`) on a measurable `U ⊆ ball 0 1`.
  The good set is enlarged by `{p | p.2 ∉ U}`, so the DMS hypothesis `hleb` holds on all of `ball 0 1`. The identity is
  `campbellMarkedObs_dmsShiftedPairing` (n2, `S11r/MarkedObs.lean`, landed); the absolute continuity is
  `insertedMeasure_ac_zeroInsertion_on_unitBall` (z7, `S11i/AnnularWeylAbsCont.lean`, landed).
* `ae_unitScale_of_ball`: one local ball (chain output `href`, measurability `hBad`, fitting `hfit`).
* `unitBallFrequencyStmt_of_cover`: the exhaustion gives `UnitBallFrequencyStmt` from the per-ball statements `hloc`.

Inputs: the frozen Weyl relation `LocalLQGInsertionWeylOffOrigin` (`Frozen/S8c.lean:73`), the nonatomicity hypotheses
`hNon0 : μ0 ω {0} = 0`, `hNonα : μα ω {0} = 0` (hypotheses here), the per-ball chain outputs `href`, `hBad`, `hfit`.
No new input.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8Exhaustion

open MeasureTheory Filter Topology Set Metric
open HarmonicBalls HarmonicBalls.S11c HarmonicBalls.FirstPassS11iStep8Transfer
open HarmonicBalls.FirstPassS11iStep8Corrected HarmonicBalls.FirstPassS11iStep8PhysicalWindow
open HarmonicBalls.FirstPassS11iHzoom FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassS11iAnnularWeylAbsCont

/-- Rational centre of the cover: `ballCen p = p.1 + p.2.1 · i`. -/
noncomputable def ballCen (p : ℚ × ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩

/-- Rational radius of the cover. -/
def ballRad (p : ℚ × ℚ × ℚ) : ℝ := (p.2.2 : ℝ)

/-- A valid cover index: the inner ball `ball (ballCen p) (ballRad p)` has the doubled ball `ball (ballCen p) (2 ballRad p)` inside the
unit disc, and that doubled ball misses `0`. -/
def ValidBall (p : ℚ × ℚ × ℚ) : Prop :=
  0 < ballRad p ∧ 2 * ballRad p < ‖ballCen p‖ ∧ ‖ballCen p‖ + 2 * ballRad p < 1

/-- **Rational cover of the punctured unit disc.** Every point `x` with `0 < ‖x‖ < 1` lies in a valid rational ball. -/
theorem exists_validBall_of_ne_zero {x : ℂ} (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) :
    ∃ p : ℚ × ℚ × ℚ, ValidBall p ∧ x ∈ ball (ballCen p) (ballRad p) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set s : ℝ := min ‖x‖ (1 - ‖x‖) with hs
  have hs0 : 0 < s := lt_min hxpos (by linarith)
  have hsx : s ≤ ‖x‖ := min_le_left _ _
  have hs1 : s ≤ 1 - ‖x‖ := min_le_right _ _
  obtain ⟨r, hr0, hrs⟩ := exists_rat_btwn (show (0 : ℝ) < s / 4 by positivity)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - (r : ℝ) / 2 < x.re + (r : ℝ) / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - (r : ℝ) / 2 < x.im + (r : ℝ) / 2 by linarith)
  have hcre : (ballCen (a, b, r)).re = (a : ℝ) := rfl
  have hcim : (ballCen (a, b, r)).im = (b : ℝ) := rfl
  have hd : ‖x - ballCen (a, b, r)‖ < (r : ℝ) := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (x - ballCen (a, b, r))
    rw [Complex.sub_re, Complex.sub_im, hcre, hcim] at h1
    have h2 : |x.re - a| < (r : ℝ) / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    have h3 : |x.im - b| < (r : ℝ) / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    linarith
  have hn1 : ‖x‖ - ‖ballCen (a, b, r)‖ ≤ ‖x - ballCen (a, b, r)‖ := norm_sub_norm_le x _
  have hn2 : ‖ballCen (a, b, r)‖ - ‖x‖ ≤ ‖ballCen (a, b, r) - x‖ := norm_sub_norm_le _ x
  rw [norm_sub_rev (ballCen (a, b, r)) x] at hn2
  refine ⟨(a, b, r), ⟨hr0, ?_, ?_⟩, ?_⟩
  · show 2 * (r : ℝ) < ‖ballCen (a, b, r)‖
    linarith
  · show ‖ballCen (a, b, r)‖ + 2 * (r : ℝ) < 1
    linarith
  · rw [mem_ball, dist_eq_norm]
    exact hd

/-- **Countable exhaustion.** If for every valid rational ball the almost-sure statement holds at `μ`-a.e. point of the
inner ball, and `μ ω {0} = 0` almost surely, then the statement holds at `μ`-a.e. point of the unit disc. -/
theorem ae_forall_of_cover {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (Φ : Ω → ℂ → Prop) (hNon : ∀ᵐ ω ∂P, μ ω {0} = 0)
    (hloc : ∀ p : ℚ × ℚ × ℚ, ValidBall p → ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (ballCen p) (ballRad p) → Φ ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 → Φ ω z := by
  have h1 : ∀ᵐ ω ∂P, ∀ p : ℚ × ℚ × ℚ, ∀ᵐ z ∂(μ ω), ValidBall p → z ∈ ball (ballCen p) (ballRad p) → Φ ω z := by
    refine ae_all_iff.2 (fun p => ?_)
    by_cases hv : ValidBall p
    · filter_upwards [hloc p hv] with ω hω
      filter_upwards [hω] with z hz
      exact fun _ => hz
    · exact Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun z => fun hv' _ => absurd hv' hv
  have h2 : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ p : ℚ × ℚ × ℚ, ValidBall p → z ∈ ball (ballCen p) (ballRad p) → Φ ω z := by
    filter_upwards [h1] with ω hω
    exact ae_all_iff.2 hω
  have hz0 : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ≠ 0 := by
    filter_upwards [hNon] with ω hω
    exact ae_iff.2 (by simpa using hω)
  filter_upwards [h2, hz0] with ω hω hω0
  filter_upwards [hω, hω0] with z hzq hzne
  intro hzB
  have hx1 : ‖z‖ < 1 := by simpa using hzB
  obtain ⟨p, hv, hzp⟩ := exists_validBall_of_ne_zero hzne hx1
  exact hzq p hv hzp

/-- The good set of the corrected marked transfer on a set `U`: the points off `U` are declared good, so that the DMS
hypothesis holds on all of `ball 0 1`; on `U` the good set is `dmsLocalGood`. -/
def dmsGoodOn (α₀ : ℝ) (D U : Set ℂ)
    (Bad : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ))) :
    Set (((ℂ → ℝ) → ℝ) × ℂ) :=
  {p | p.2 ∉ U} ∪ dmsLocalGood α₀ D Bad

/-- **Corrected marked transfer on `U`.** Same as `ae_marked_local_transfer` (Step8CorrectedMarked.lean), with the DMS
identity `campbellMarkedObs_dmsShiftedPairing` (n2, landed) and the reference statement needed only on `U ⊆ ball 0 1`. -/
theorem ae_marked_local_transfer_on {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    (γ α₀ : ℝ) (D : Set ℂ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (μ0 μα : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (U : Set ℂ) (hUB : U ⊆ ball (0 : ℂ) 1) (hU : MeasurableSet U)
    (Bad : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ))) (hBad : MeasurableSet Bad)
    (href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → ∀ᵐ ω ∂P, campbellReferenceObs γ α₀ D (hC ω) z ∉ Bad)
    (hac : ∀ᵐ ω ∂P, (μα ω).restrict (ball (0 : ℂ) 1) ≪ (μ0 ω).restrict (ball (0 : ℂ) 1)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ U → campbellMarkedObs α₀ D (hC ω) z ∉ Bad := by
  have hsnd : MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      {p : ((ℂ → ℝ) → ℝ) × ℂ | p.2 ∉ U} := by
    let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ
    exact (hU.compl).preimage measurable_snd
  have hS : MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (dmsGoodOn α₀ D U Bad) :=
    hsnd.union (measurableSet_dmsLocalGood α₀ D hBad)
  have hleb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∈ dmsGoodOn α₀ D U Bad := by
    filter_upwards [href] with z hz hzB
    by_cases hzU : z ∈ U
    · filter_upwards [hz hzU] with ω hω
      refine Set.mem_union_right _ ?_
      show campbellMarkedObs α₀ D (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) z ∉ Bad
      rw [campbellMarkedObs_dmsShiftedPairing]
      exact hω
    · exact Filter.Eventually.of_forall fun ω => Set.mem_union_left _ hzU
  have h0 := ae_ae_ball_of_marked_of_ae_volume' P γ hC hcirc μ0 hA10 hGFF hμ0 (dmsGoodOn α₀ D U Bad) hS hleb
  filter_upwards [h0, hac] with ω hω hacω
  have h1 : ∀ᵐ z ∂((μ0 ω).restrict (ball (0 : ℂ) 1)), (hC ω, z) ∈ dmsGoodOn α₀ D U Bad := by
    rw [ae_restrict_iff' measurableSet_ball]
    exact hω
  have h2 : ∀ᵐ z ∂((μα ω).restrict (ball (0 : ℂ) 1)), (hC ω, z) ∈ dmsGoodOn α₀ D U Bad :=
    hacω.ae_le h1
  rw [ae_restrict_iff' measurableSet_ball] at h2
  filter_upwards [h2] with z hz hzU
  rcases (Set.mem_union _ _ _).1 (hz (hUB hzU)) with h | h
  · exact absurd hzU h
  · exact h

/-- **One ball of the exhaustion.** The chain output `href` (reference observations off `Bad` on `U`), the measurability
`hBad` of the local failure set and the fitting identity `hfit` give the physical unit-scale limit `μα`-a.e. on `U`.
Inputs: the frozen Weyl relation (`hWeyl`), nonatomicity of `μ0` and `μα` at `0` (`hNon0`, `hNonα`). -/
theorem ae_unitScale_of_ball {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (μ0 μα : Ω → Measure ℂ) (Dα : Ω → ℂ → ℂ → ℝ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hWeyl : HarmonicBalls.LocalLQGInsertionWeylOffOrigin.{u}) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    {c₂ : ℂ} {r₂ : ℝ} (U : Set ℂ) (hUB : U ⊆ ball (0 : ℂ) 1) (hUD : U ⊆ ball c₂ r₂) (hU : MeasurableSet U)
    (q : ℝ) (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U' V W T Q' Q : Set ℂ) (η M : ℝ)
    (hBad : MeasurableSet (HarmonicBalls.ReferenceNullS11i.refBadWindowSet
      (localCertSeq κ m Ostar U' V W T Q' Q η M) q))
    (href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → ∀ᵐ ω ∂P,
      campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉
        HarmonicBalls.ReferenceNullS11i.refBadWindowSet (localCertSeq κ m Ostar U' V W T Q' Q η M) q)
    (hfit : ∀ᵐ ω ∂P, ∀ z ∈ ball c₂ r₂, ∀ᶠ n : ℕ in atTop,
      (FirstPassS11i.CertificateEvent (κ (fun φ => fieldPairing α₀ (hC ω) φ.1))
          (m (fun φ => fieldPairing α₀ (hC ω) φ.1)) Ostar U' V W T Q' Q η M (certScale n) z ↔
        FirstPassS11i.CertificateEvent (μα ω) (Dα ω) Ostar U' V W T Q' Q η M (certScale n) z)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ U →
      Tendsto (fun N : ℕ => unitScaleWindowFreq (μα ω) (Dα ω) Ostar U' V W T Q' Q η M z N) atTop (𝓝 q) := by
  have hac := insertedMeasure_ac_zeroInsertion_on_unitBall hWeyl P γ α₀ hC hcirc μ0 μα hGFF hγ0 hγ2 hα hμ0 hμα
    hNon0 hNonα
  have hGood := ae_marked_local_transfer_on γ α₀ (ball c₂ r₂) μ0 μα hA10 hGFF hμ0 U hUB hU _ hBad href hac
  exact ae_unitScale_of_local_good α₀ U hUD q κ m Ostar U' V W T Q' Q η M hC μα Dα hfit hGood

/-- **Unit-ball frequency from the per-ball statements.** If the per-ball unit-scale limit holds `μ`-a.e. on each valid
rational ball, and `μ ω {0} = 0` a.s., then `UnitBallFrequencyStmt` holds with `Ostar = pinchOmegaGeom W Q δ`, `η = δ`. -/
theorem unitBallFrequencyStmt_of_cover {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (q δ M : ℝ)
    (U V W T Q' Q : Set ℂ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hNon : ∀ᵐ ω ∂P, μ ω {0} = 0)
    (hloc : ∀ p : ℚ × ℚ × ℚ, ValidBall p → ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (ballCen p) (ballRad p) →
      Tendsto (fun N : ℕ => unitScaleWindowFreq (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M z N)
        atTop (𝓝 q)) :
    UnitBallFrequencyStmt P q U V W T Q' Q δ M μ D := by
  unfold UnitBallFrequencyStmt
  exact ae_forall_of_cover P μ
    (fun ω z => Tendsto (fun N : ℕ => unitScaleWindowFreq (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M z N)
      atTop (𝓝 q)) hNon hloc

end HarmonicBalls.FirstPassS11iStep8Exhaustion

#print axioms HarmonicBalls.FirstPassS11iStep8Exhaustion.ae_forall_of_cover
#print axioms HarmonicBalls.FirstPassS11iStep8Exhaustion.ae_marked_local_transfer_on
#print axioms HarmonicBalls.FirstPassS11iStep8Exhaustion.ae_unitScale_of_ball
#print axioms HarmonicBalls.FirstPassS11iStep8Exhaustion.unitBallFrequencyStmt_of_cover
