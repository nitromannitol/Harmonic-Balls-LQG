import HarmonicBalls.FirstPass.S8d.TorusGoodIterate
import HarmonicBalls.FirstPass.S8c.TorusGood
import HarmonicBalls.FirstPass.S8c.Measurability
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion

/-! # helper: the torus identity `hid` on the profile space, almost surely

Let `F : Ω → C(CircleParameter, ℝ)` be measurable with law `Q = P.map F`, let `Dec` be a measurable map from profiles to
measures on `ℂ`, and let `R` be measurable (in the application `R = continuousCircleDilation`). Suppose that, for `P`-a.e.
`ω`, all the measures `Dec (R^[k] (F ω))` are locally finite and, for each `k`, the dilation identity holds in the form
`Dec (R^[k+1] (F ω)) = c • (Dec (F ω)).map (dyadicScale (k+1))⁻¹ •` for some `c ∈ (0, ∞)`. Then, for every level `n`, the
level-`n` torus good event of `Dec` agrees almost everywhere with the preimage under the doubling-and-dilation map `T`
of the level-`0` good event, for the product measure `phaseTorusFieldMeasure Q`. This is the `hid_ae` hypothesis of
`torusPhaseTail_of_dilation_ae` (FirstPass/S8d/AeHid.lean), at the profile level.

The proof is a pullback along `Prod.map id F`: the null set is controlled by the `P`-null set of bad profiles, and the
pointwise identity is `s8d_torusGood_iterate_iff` (FirstPass/S8d/TorusGoodIterate.lean). No frozen input is used. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls

/-- The iterate of the product map acts coordinatewise. -/
theorem s8d_torus_iterate_prod (R : C(CircleParameter, ℝ) → C(CircleParameter, ℝ)) (n : ℕ)
    (p : PhaseTorus × C(CircleParameter, ℝ)) :
    (fun q : PhaseTorus × C(CircleParameter, ℝ) => (phaseTorusDouble q.1, R q.2))^[n] p =
      (phaseTorusDouble^[n] p.1, R^[n] p.2) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih]

/-- The level-`n` torus identity `hid` on the profile space, almost surely. -/
theorem s8d_torusGood_hid_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → C(CircleParameter, ℝ)) (hF : Measurable F)
    (Dec : C(CircleParameter, ℝ) → Measure ℂ) (hDec : Measurable Dec)
    (R : C(CircleParameter, ℝ) → C(CircleParameter, ℝ)) (hR : Measurable R)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hfin : ∀ᵐ ω ∂P, ∀ k : ℕ, IsLocallyFiniteMeasure (Dec (R^[k] (F ω))))
    (hdil : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      Dec (R^[k + 1] (F ω)) = c • (Dec (F ω)).map (fun z : ℂ => (dyadicScale (k + 1))⁻¹ • z))
    (n : ℕ) :
    torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n Dec =ᵐ[phaseTorusFieldMeasure (P.map F)]
      (fun p : PhaseTorus × C(CircleParameter, ℝ) => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹'
        torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 Dec := by
  cases n with
  | zero =>
    rw [Function.iterate_zero, Set.preimage_id]
  | succ k =>
    have hDbl : Continuous phaseTorusDouble := by
      unfold phaseTorusDouble
      exact ((continuous_const_smul (2 : ℕ)).comp continuous_fst).prodMk
        ((continuous_const_smul (2 : ℕ)).comp continuous_snd)
    have hT : Measurable (fun p : PhaseTorus × C(CircleParameter, ℝ) => (phaseTorusDouble p.1, R p.2)) :=
      (hDbl.measurable.comp measurable_fst).prodMk (hR.comp measurable_snd)
    have hTn := hT.iterate (k + 1)
    have hAm : MeasurableSet (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m (k + 1) Dec) :=
      measurableSet_torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha Dec hDec (k + 1)
    have hBm : MeasurableSet ((fun p : PhaseTorus × C(CircleParameter, ℝ) => (phaseTorusDouble p.1, R p.2))^[k + 1] ⁻¹'
        torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 Dec) :=
      hTn (measurableSet_torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha Dec hDec 0)
    have hΦ : Measurable (Prod.map (id : PhaseTorus → PhaseTorus) F) :=
      measurable_id.prodMap hF
    have hmap : phaseTorusFieldMeasure (P.map F) =
        (phaseTorusFieldMeasure P).map (Prod.map (id : PhaseTorus → PhaseTorus) F) := by
      unfold phaseTorusFieldMeasure
      symm
      rw [← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id]
    -- a set of profiles-times-phases that is bad for no profile-phase pair `P`-almost surely is null
    have key : ∀ D : Set (PhaseTorus × C(CircleParameter, ℝ)), MeasurableSet D →
        (∀ᵐ ω ∂P, ∀ θ : PhaseTorus, (θ, F ω) ∉ D) → phaseTorusFieldMeasure (P.map F) D = 0 := by
      intro D hD hgood
      rw [hmap, Measure.map_apply hΦ hD]
      have hN0 : P {ω | ¬ ∀ θ : PhaseTorus, (θ, F ω) ∉ D} = 0 := ae_iff.mp hgood
      obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN0
      refine measure_mono_null (t := univ ×ˢ N') (fun x hx => ⟨mem_univ _, hNN' (fun h => h x.1 hx)⟩) ?_
      rw [Measure.prod_prod, hN'0, mul_zero]
    have hgood : ∀ᵐ ω ∂P, ∀ θ : PhaseTorus,
        ((θ, F ω) ∈ torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m (k + 1) Dec ↔
          (θ, F ω) ∈ (fun p : PhaseTorus × C(CircleParameter, ℝ) => (phaseTorusDouble p.1, R p.2))^[k + 1] ⁻¹'
            torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 Dec) := by
      filter_upwards [hfin, hdil k] with ω hω1 hω2 θ
      obtain ⟨c, hc0, hcT, hid⟩ := hω2
      have : IsLocallyFiniteMeasure (Dec (F ω)) := by simpa using hω1 0
      have : IsLocallyFiniteMeasure (Dec (R^[k + 1] (F ω))) := hω1 (k + 1)
      have hA : (θ, F ω) ∈ torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m (k + 1) Dec ↔
          (PhaseVeryGoodAnnulus (finitePart (Dec (F ω))) β (dyadicScale (k + 1)) 0 N₀ a b C₁m C₁p C₂m C₂p C₃
              (torusPhase θ) ∧
            AnnulusBallComparison (finitePart (Dec (F ω))) (k + 1) 0 m) := Iff.rfl
      have hB : (θ, F ω) ∈ (fun p : PhaseTorus × C(CircleParameter, ℝ) => (phaseTorusDouble p.1, R p.2))^[k + 1] ⁻¹'
            torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 Dec ↔
          (PhaseVeryGoodAnnulus (finitePart (Dec (R^[k + 1] (F ω)))) β (dyadicScale 0) 0 N₀ a b C₁m C₁p C₂m C₂p C₃
              (torusPhase (phaseTorusDouble^[k + 1] θ)) ∧
            AnnulusBallComparison (finitePart (Dec (R^[k + 1] (F ω)))) 0 0 m) := by
        rw [Set.mem_preimage, s8d_torus_iterate_prod R (k + 1) (θ, F ω)]
        exact Iff.rfl
      rw [finitePart_eq_of_locallyFinite (Dec (F ω))] at hA
      rw [finitePart_eq_of_locallyFinite (Dec (R^[k + 1] (F ω)))] at hB
      rw [hA, hB]
      exact s8d_torusGood_iterate_iff (Dec (F ω)) (Dec (R^[k + 1] (F ω))) (k + 1) c hc0 hcT hid θ β N₀ a b
        C₁m C₁p C₂m C₂p C₃ m
    have hd1 := key _ (hAm.diff hBm) (hgood.mono fun ω h θ hmem => hmem.2 ((h θ).1 hmem.1))
    have hd2 := key _ (hBm.diff hAm) (hgood.mono fun ω h θ hmem => hmem.2 ((h θ).2 hmem.1))
    exact ae_eq_set.mpr ⟨hd1, hd2⟩

end HarmonicBalls
