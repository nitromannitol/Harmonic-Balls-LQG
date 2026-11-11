import HarmonicBalls.FirstPass.S8c.PhaseTail
import HarmonicBalls.FirstPass.S8c.RootCount

/-! # Transfer of the phase tail to the reference observations on the local domains

Given the phase tail (`LocalPhaseTailStep`, G-8-2 section 3 eq. (7)) for the reference measure `ν`, the reference
observations `V_j(z, ω) = localReferenceObservation ν j (z, ω)` lie almost surely in the recentred good set on the
product of `localDomain j` (Lebesgue) and `P`. The phase is the reflection `-z` (G-8-2 section 4: "apply (7) to w = -z");
Lebesgue measure is reflection invariant. Restriction to the reference observation uses `phaseCount_eventually_iff_normalized`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The phase tail, transferred to the reference observations on the local domain `D_j`. -/
theorem localReference_ae_mem_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Ω → Measure ℂ) (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hTail : ∀ᵐ x ∂((volume : Measure ℂ).prod P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν x.2) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ x.1 ∧
        AnnulusBallComparison (ν x.2) n 0 m}.ncard : ℝ))
    (hposν : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → 0 < ν ω (ball 0 r))
    (hlocν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω)) (j : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ x ∂((volume.restrict (localDomain j)).prod P),
      localReferenceObservation ν j x ∈ recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ := by
  have hr : 0 < localRadius j := localRadius_pos hj
  -- the reflection w ↦ -w preserves Lebesgue ⊗ P
  have hmp : MeasurePreserving (fun x : ℂ × Ω => (-x.1, x.2))
      ((volume : Measure ℂ).prod P) ((volume : Measure ℂ).prod P) :=
    (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id P)
  have hneg : ∀ᵐ x ∂((volume : Measure ℂ).prod P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν x.2) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (-x.1) ∧
        AnnulusBallComparison (ν x.2) n 0 m}.ncard : ℝ) :=
    hmp.quasiMeasurePreserving.ae hTail
  have hposX : ∀ᵐ x ∂((volume : Measure ℂ).prod P), ∀ r : ℝ, 0 < r → 0 < ν x.2 (ball 0 r) :=
    (Measure.quasiMeasurePreserving_snd).ae hposν
  have hlocX : ∀ᵐ x ∂((volume : Measure ℂ).prod P), IsLocallyFiniteMeasure (ν x.2) :=
    (Measure.quasiMeasurePreserving_snd).ae hlocν
  have hres : (volume.restrict (localDomain j)).prod P =
      ((volume : Measure ℂ).prod P).restrict (localDomain j ×ˢ univ) := by
    have h := Measure.prod_restrict (μ := (volume : Measure ℂ)) (ν := P) (localDomain j) univ
    rwa [Measure.restrict_univ] at h
  rw [hres]
  filter_upwards [ae_restrict_of_ae hneg, ae_restrict_of_ae hposX, ae_restrict_of_ae hlocX]
    with x hx hpx hlx
  have hpos' : 0 < ν x.2 (ball 0 (localRadius j / 2)) := hpx _ (half_pos hr)
  have := hlx
  have hfin := isFiniteMeasure_massNormalize_restrict (ν x.2) hr hpos'
  have hfp : finitePart (massNormalize (localRadius j) ((ν x.2).restrict (ball 0 (localRadius j)))) =
      massNormalize (localRadius j) ((ν x.2).restrict (ball 0 (localRadius j))) :=
    finitePart_eq_of_locallyFinite _
  have key := (phaseCount_eventually_iff_normalized (ν x.2) (localRadius j) hr hpos' β N₀
    a b C₁m C₁p C₂m C₂p C₃ m ζ (-x.1)).mp hx
  simp only [recentredGoodSet, localReferenceObservation, Set.mem_ofPred_eq]
  filter_upwards [key] with N hN
  have hset : {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n
        (x.1, massNormalize (localRadius j) ((ν x.2).restrict (ball 0 (localRadius j))))} =
      {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus
            (massNormalize (localRadius j) ((ν x.2).restrict (ball 0 (localRadius j)))) β
            (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (-x.1) ∧
        AnnulusBallComparison
            (massNormalize (localRadius j) ((ν x.2).restrict (ball 0 (localRadius j)))) n 0 m} := by
    ext n
    simp only [Set.mem_ofPred_eq, recentredScalePred, hfp]
  rw [hset]
  exact hN


end HarmonicBalls
