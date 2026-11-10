import HarmonicBalls.FirstPass.S11i.ReferenceNull
import HarmonicBalls.FirstPass.S11i.RootedLocalLimit
import HarmonicBalls.FirstPass.S11w

/-!
# Steps 6 and 7 of the Lean route for equation (34) (fp-S11ai-11-13-steps-6-7, owner n1)

Source: `notes/fp-gaps/CHATGPT-n3-Q1-eq34.md` §5. Step 6 is the reference-nullity (L) of the failure set; Step 7 is its
transfer to zero quantum bad mass (M), through the Campbell glue. Consumers: n3 (`Assembly13.lean`, Step 8 and up).

Notation. `D = ball c₂ r₂` is the observation domain, `B = ball c₁ r₁` the root domain, `A` the set of roots of Step 4.
`c n` is the cutoff certificate indicator of Step 4 (eq. (J)) at a marked observation `(z, ℓ)`; `q` is the limit of Step 2.

The failure set `S` of Step 5 (eq. (K), owned by n4) enters as a named hypothesis: a measurable set `S` (`hS`) with the
characterisation `hSfail : x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (window averages of c at x) (𝓝 q)`.

Named inputs, none proved here:
* `hId` (Step 6, rooted decoder identification): for a.e. root `z ∈ A` there are `b > 0` and a smooth, compactly supported
  `u` with zero unit-circle average such that almost surely the reference window averages of `c` at `z` agree eventually
  with the window frequency (Step 11.5) of the rooted field `addFunPairing (translatedPairing hC hcirc z ω) u`.
* the frozen inputs `CameronMartinGFFMutualAbsCont` (`hCM`), `BirkhoffPointwiseErgodic` (`hB`) of Step 11.5, and
  `LocalCampbellMarkedRestrictionFrozen` (`hCamp`) with the LQG existence family `hE` of the Campbell glue.
-/

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

universe u

/-- **Step 6, reference-nullity (eq. (L)) from the a.e.-root window limit.** If for a.e. root `z ∈ A` the reference window
averages of `c` at the rooted observation `f_z` converge to `q` almost surely, then for a.e. root `z ∈ B` the failure set is
`P`-null at `f_z`: `∫ 1_S(z, obs_D f_z) dP = 0`. No joint measurability is needed for this a.e. form. -/
theorem ae_reference_nullity_of_window_limit
    {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (A : Set ℂ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ) (q : ℝ)
    (S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)))
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop (𝓝 q))
    (hLim : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ᵐ ω ∂P,
      Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z))
        atTop (𝓝 q)) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0 := by
  filter_upwards [hLim] with z hz
  by_cases hA : z ∈ A
  · have hf : ∀ᵐ ω ∂P, campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉ S := by
      filter_upwards [hz hA] with ω hω
      intro hmem
      rw [hSfail] at hmem
      exact hmem.2 hω
    exact ReferenceNullS11i.lintegral_indicator_eq_zero_of_ae_notMem S _ hf
  · have hf : ∀ ω, campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z ∉ S := fun ω hmem => by
      rw [hSfail] at hmem
      exact hA hmem.1
    exact ReferenceNullS11i.lintegral_indicator_eq_zero_of_ae_notMem S _ (Filter.Eventually.of_forall hf)

/-- **Rooted window limit at one root (Step 11.5 transported to the reference observation).** Given the rooted decoder
identification at the root `z` (`hId`), the reference window averages of `c` converge almost surely to the Step-11.5 limit
`P{alphaCanon γ ∈ E}`. The proof is `ae_rooted_window_frequency` plus eventual equality. -/
theorem ae_window_limit_at_root
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₂ : ℂ} {r₂ : ℝ}
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    (z : ℂ) {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (hId : ∃ (b : ℝ) (u : ℂ → ℝ), 0 < b ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧
      Real.circleAverage u 0 1 = 0 ∧ ∀ᵐ ω ∂P, ∀ᶠ N in atTop,
        ReferenceNullS11i.refWindowAverage c N (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)
          = windowFreqOf γ (ballRestrictPairing 7 ⁻¹' F) (addFunPairing (translatedPairing hC hcirc z ω) u) N) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N
        (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal) := by
  obtain ⟨b, u, hb, hu, hcomp, hu0, hid⟩ := hId
  filter_upwards [ae_rooted_window_frequency hCM hB hh γ z hb hF u hu hcomp hu0
    (fun ω => addFunPairing (translatedPairing hC hcirc z ω) u) (fun _ _ _ _ => rfl), hid] with ω h1 h2
  exact Tendsto.congr' (h2.mono fun N hN => hN.symm) h1

/-- **Step 6, reference-nullity (eq. (L)), from the rooted decoder identification.** Input `hId` holds for a.e. root of `A`;
the limit is `q = P{alphaCanon γ ∈ E}`, the Step-11.5 limit. Conclusion: for a.e. root `z ∈ B`, the failure set is
`P`-null at the reference observation `f_z`. -/
theorem ae_reference_nullity_of_rooted_identification
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (A : Set ℂ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (hId : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∃ (b : ℝ) (u : ℂ → ℝ), 0 < b ∧
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 ∧ ∀ᵐ ω ∂P, ∀ᶠ N in atTop,
        ReferenceNullS11i.refWindowAverage c N (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)
          = windowFreqOf γ (ballRestrictPairing 7 ⁻¹' F) (addFunPairing (translatedPairing hC hcirc z ω) u) N)
    (S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)))
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal)) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0 := by
  refine ae_reference_nullity_of_window_limit A c _ S hSfail ?_
  filter_upwards [hId] with z hz hA
  exact ae_window_limit_at_root hCM hB hh c z hF (hz hA)

/-- **Step 7, Campbell transfer to zero quantum bad mass (eq. (M)).** Given the reference-nullity (`href`, Step 6) of a
measurable failure set `S`, the mark-weighted Campbell integral of `1_S` against the LQG measure `μ_ω` over `B` vanishes
almost surely. This is the discharged Campbell glue `HarmonicBalls.S11w.ae_marked_null_of_reference_null_discharged`
(sides `hfin`, `hmeas` discharged there). No finite expectation of the quantum mass is needed. -/
theorem ae_quantum_bad_mass_eq_zero
    (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (href : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 :=
  HarmonicBalls.S11w.ae_marked_null_of_reference_null_discharged hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0 hS href

/-- **Steps 6 and 7 together** (the form n3 imports). From the rooted decoder identification `hId` and the measurable failure
set `S` (Step 5, n4), the zero quantum bad mass holds almost surely. -/
theorem ae_quantum_bad_mass_eq_zero_of_rooted_identification
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂) (A : Set ℂ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (hId : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∃ (b : ℝ) (u : ℂ → ℝ), 0 < b ∧
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 ∧ ∀ᵐ ω ∂P, ∀ᶠ N in atTop,
        ReferenceNullS11i.refWindowAverage c N (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)
          = windowFreqOf γ (ballRestrictPairing 7 ⁻¹' F) (addFunPairing (translatedPairing hC hcirc z ω) u) N)
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal)) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 :=
  ae_quantum_bad_mass_eq_zero hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0 hS
    (ae_reference_nullity_of_rooted_identification hCM hB hh A c hF hId S hSfail)

end FirstPassS11ai
