import HarmonicBalls.Proofs.Sec8.VeryGoodLocality
import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodScaling
import HarmonicBalls.Proofs.Sec8.LocalizedNormalizedMeasurePath
import HarmonicBalls.Proofs.Sec8.PhaseTorus
import HarmonicBalls.Proofs.Sec8.LocalizedPathBufferedLocality
import HarmonicBalls.Proofs.Sec8.GermPathFrequency

/-! # Locality of phase-shifted very-good annuli

The shifted lattice affects the centers inspected, but not the region on which
the event depends. The imported path development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The phase-shifted event depends only on its displayed regions. -/
theorem phaseVeryGoodAnnulus_restrict_of_subsets (μ : Measure ℂ) (βminus ρ : ℝ)
    (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (U : Set ℂ)
    (phase : ℂ)
    (hA : annulus x₀ (ρ / 4) (2 * ρ) ⊆ U)
    (hball : ∀ z ∈ annulus x₀ (ρ / 2) ρ, ∀ r ∈ Ioo 0 (ρ / 4), ball z r ⊆ U)
    (hgood : ∀ n : ℕ, ∀ z ∈ annulus x₀ (ρ / 2) ρ,
      ∀ r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ),
        annulus z (3 * r) (5 * r) ⊆ U) :
    PhaseVeryGoodAnnulus (μ.restrict U) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ phase ↔
      PhaseVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ phase := by
  have hcount (n : ℕ) (z : ℂ) (hz : z ∈ annulus x₀ (ρ / 2) ρ) :
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ.restrict U) r z a b} =
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b} := by
    ext r
    simp only [mem_ofPred_eq]
    by_cases hr : r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ)
    · rw [isGoodAnnulus_restrict μ r z a b U (hgood n z hz r hr)]
    · simp [hr]
  have hmass : (μ.restrict U) (annulus x₀ (ρ / 4) (2 * ρ)) =
      μ (annulus x₀ (ρ / 4) (2 * ρ)) := by
    have hAm : MeasurableSet (annulus x₀ (ρ / 4) (2 * ρ)) :=
      (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    rw [Measure.restrict_apply hAm, inter_eq_left.mpr hA]
  have hcriterion :
      (∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
        z - phase ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ.restrict U) r z a b}.ncard : ℝ)) ↔
      (∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
        z - phase ∈ Section6.scaledLattice (dyadicScale n * ρ / 100) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ)) := by
    constructor <;> intro H n hn z hz hl
    · simpa only [hcount n z hz] using H n hn z hz hl
    · simpa only [hcount n z hz] using H n hn z hz hl
  unfold PhaseVeryGoodAnnulus PhaseVeryGoodCriterionThree
  rw [annulusBallMassSize_restrict μ βminus ρ x₀ U hball,
    annulusGreenPotentialSup_restrict μ x₀ (ρ / 4) (2 * ρ) U hA, hmass, hcriterion]

/-- Every measure-dependent region in the very-good condition at scale `ρ`
is contained in the disk of radius `6ρ`. -/
theorem phaseVeryGoodAnnulus_restrict_ball_six (μ : Measure ℂ) (βminus ρ : ℝ)
    (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) (hρ : 0 < ρ) :
    PhaseVeryGoodAnnulus (μ.restrict (ball x₀ (6 * ρ))) βminus ρ x₀ N₀
        a b C₁m C₁p C₂m C₂p C₃ phase ↔
      PhaseVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ phase := by
  apply phaseVeryGoodAnnulus_restrict_of_subsets
  · exact Set.sdiff_subset.trans (ball_subset_ball (by linarith))
  · intro z hz r hr y hy
    have hz' : dist z x₀ < ρ := hz.1
    have hy' : dist y z < r := hy
    have htri := dist_triangle y z x₀
    change dist y x₀ < 6 * ρ
    linarith [hr.2]
  · intro n z hz r hr y hy
    have hz' : dist z x₀ < ρ := hz.1
    have hy' : dist y z < 5 * r := hy.1
    have hdyad : dyadicScale n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hsqrt : Real.sqrt (dyadicScale n) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hdyad
    have hrad : r ≤ ρ := hr.2.trans (by nlinarith)
    have htri := dist_triangle y z x₀
    change dist y x₀ < 6 * ρ
    linarith

/-- The unit-scale phase event and annulus comparison are determined by the
normalized restriction to the ball of radius six. -/
theorem phaseVeryGoodComparable_normalizedRestriction_ball_six
    (μ : Measure ℂ) (β : ℝ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (phase : ℂ) (hzero : μ (ball 0 6) ≠ 0) (htop : μ (ball 0 6) ≠ ∞) :
    (PhaseVeryGoodAnnulus (normalizedRestriction μ (ball 0 6)) β 1 0 N
        a b C₁m C₁p C₂m C₂p C₃ phase ∧
      AnnulusBallComparison (normalizedRestriction μ (ball 0 6)) 0 0 m) ↔
    (PhaseVeryGoodAnnulus μ β 1 0 N a b C₁m C₁p C₂m C₂p C₃ phase ∧
      AnnulusBallComparison μ 0 0 m) := by
  unfold normalizedRestriction
  rw [phaseVeryGoodAnnulus_smul _ _ _ _ _ _ _ _ _ _ _ _ _
      (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr hzero),
    annulusBallComparison_smul _ _ _ _
      (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr hzero)]
  apply and_congr
  · simpa using phaseVeryGoodAnnulus_restrict_ball_six μ β 1 0 N
      a b C₁m C₁p C₂m C₂p C₃ phase (by norm_num)
  · apply annulusBallComparison_restrict
    apply ball_subset_ball
    norm_num [dyadicScale]

/-- A coordinate of the localized dyadic path records the phase-shifted
very-good event and annulus comparison at the corresponding physical scale. -/
theorem phaseVeryGoodComparable_localizedDyadicMeasure
    (μ : Measure ℂ) (β : ℝ) (n N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (phase : ℂ)
    (hzero : (μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) (ball 0 6) ≠ 0)
    (htop : (μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) (ball 0 6) ≠ ∞) :
    (PhaseVeryGoodAnnulus (localizedDyadicMeasure (ball 0 6) μ n) β 1 0 N
        a b C₁m C₁p C₂m C₂p C₃ phase ∧
      AnnulusBallComparison (localizedDyadicMeasure (ball 0 6) μ n) 0 0 m) ↔
    (PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N
        a b C₁m C₁p C₂m C₂p C₃ (dyadicScale n • phase) ∧
      AnnulusBallComparison μ n 0 m) := by
  unfold localizedDyadicMeasure
  rw [phaseVeryGoodComparable_normalizedRestriction_ball_six _ β N
    a b C₁m C₁p C₂m C₂p C₃ m phase hzero htop,
    phaseVeryGoodAnnulus_map_inv_smul μ (dyadicScale_pos n),
    annulusBallComparison_map_dyadic]
  simp

/-- The doubling orbit of a torus phase records one fixed physical lattice
phase at every dyadic scale. -/
theorem phaseVeryGoodComparable_localizedDyadicMeasure_torus
    (μ : Measure ℂ) (β : ℝ) (n N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (phase : ℂ)
    (hzero : (μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) (ball 0 6) ≠ 0)
    (htop : (μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) (ball 0 6) ≠ ∞) :
    (PhaseVeryGoodAnnulus (localizedDyadicMeasure (ball 0 6) μ n) β 1 0 N
        a b C₁m C₁p C₂m C₂p C₃
        (torusPhase ((phaseTorusDouble^[n]) (phaseTorusOfComplex phase))) ∧
      AnnulusBallComparison (localizedDyadicMeasure (ball 0 6) μ n) 0 0 m) ↔
    (PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N
        a b C₁m C₁p C₂m C₂p C₃ phase ∧
      AnnulusBallComparison μ n 0 m) := by
  have horbit : (phaseTorusDouble^[n]) (phaseTorusOfComplex phase) =
      phaseTorusOfComplex ((dyadicScale n)⁻¹ • phase) := by
    simpa using (phaseTorusOfComplex_normalizedPhase (-phase) n).symm
  rw [horbit]
  have hp := phaseVeryGoodAnnulus_torusPhase_ofComplex
    (localizedDyadicMeasure (ball 0 6) μ n) β 0 N a b C₁m C₁p C₂m C₂p C₃
    ((dyadicScale n)⁻¹ • phase)
  simp only [show dyadicScale 0 = 1 by simp [dyadicScale]] at hp
  rw [hp, phaseVeryGoodComparable_localizedDyadicMeasure _ β n N
    a b C₁m C₁p C₂m C₂p C₃ m ((dyadicScale n)⁻¹ • phase) hzero htop]
  simp only [smul_smul, mul_inv_cancel₀ (dyadicScale_pos n).ne', one_smul]

/-- The canonical representative belongs to its original phase class. -/
theorem phaseTorusOfComplex_torusPhase (t : PhaseTorus) :
    phaseTorusOfComplex (torusPhase t) = t := by
  apply Prod.ext
  · simp only [phaseTorusOfComplex, torusPhase, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simp
    have h : 100 * (phaseCircleRep t.1 / 100) = phaseCircleRep t.1 := by ring
    rw [h, coe_phaseCircleRep]
  · simp only [phaseTorusOfComplex, torusPhase, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    simp only [mul_zero, mul_one, add_zero, zero_add]
    have h : 100 * (phaseCircleRep t.2 / 100) = phaseCircleRep t.2 := by ring
    rw [h, coe_phaseCircleRep]

/-- The normalized local phase event is measurable on the full measure space;
normalization supplies the local finiteness required for joint measurability. -/
theorem measurableSet_phaseVeryGoodComparable_normalizedRestriction
    (β : ℝ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {p : PhaseTorus × Measure ℂ |
      PhaseVeryGoodAnnulus (normalizedRestriction p.2 (ball 0 6)) β 1 0 N
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison (normalizedRestriction p.2 (ball 0 6)) 0 0 m} := by
  have hm : Measurable (fun p : PhaseTorus × Measure ℂ =>
      normalizedRestriction p.2 (ball 0 6)) :=
    (measurable_normalizedRestriction_measure (ball 0 6) isOpen_ball.measurableSet).comp
      measurable_snd
  have hf : ∀ p : PhaseTorus × Measure ℂ,
      IsLocallyFiniteMeasure (normalizedRestriction p.2 (ball 0 6)) := fun _ => inferInstance
  exact (measurableSet_phaseVeryGoodAnnulus (c := fun _ => (0 : ℂ)) hm hf
    measurable_const (measurable_torusPhase.comp measurable_fst) β 1 (by norm_num) N
    a b C₁m C₁p C₂m C₂p C₃ hunit).inter
    (measurableSet_annulusBallComparison_joint (c := fun _ => (0 : ℂ))
      hm hf measurable_const 0 m)

/-- Along the torus orbit, the measurable normalized observable is exactly the
physical event with fixed phase `torusPhase t`. -/
theorem phaseVeryGoodComparable_normalizedPath_torus
    (μ : Measure ℂ) (β : ℝ) (n N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (t : PhaseTorus)
    (hzero : (μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) (ball 0 6) ≠ 0)
    (htop : (μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) (ball 0 6) ≠ ∞) :
    (PhaseVeryGoodAnnulus
        (normalizedRestriction (localizedDyadicMeasure (ball 0 6) μ n) (ball 0 6)) β 1 0 N
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase ((phaseTorusDouble^[n]) t)) ∧
      AnnulusBallComparison
        (normalizedRestriction (localizedDyadicMeasure (ball 0 6) μ n) (ball 0 6)) 0 0 m) ↔
    (PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
      AnnulusBallComparison μ n 0 m) := by
  have hnorm : normalizedRestriction (localizedDyadicMeasure (ball 0 6) μ n) (ball 0 6) =
      localizedDyadicMeasure (ball 0 6) μ n := by
    unfold localizedDyadicMeasure
    exact normalizedRestriction_normalizedRestriction_of_subset _ isOpen_ball.measurableSet
      (Set.Subset.rfl) hzero htop
  rw [hnorm]
  simpa only [phaseTorusOfComplex_torusPhase] using
    phaseVeryGoodComparable_localizedDyadicMeasure_torus μ β n N
      a b C₁m C₁p C₂m C₂p C₃ m (torusPhase t) hzero htop

open Classical in
/-- An ergodic localized path and a strict one-scale mean bound imply the
phase-shifted physical block-frequency estimate for Haar-almost every phase. -/
theorem ae_phaseVeryGoodComparable_blockFrequency_of_localized_path
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (herg : Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 6) (μ ω) n)))
    (hmass : ∀ᵐ ω ∂P, ∀ n,
      (μ ω).map (fun z : ℂ => (dyadicScale n)⁻¹ • z) (ball 0 6) ≠ 0 ∧
      (μ ω).map (fun z : ℂ => (dyadicScale n)⁻¹ • z) (ball 0 6) ≠ ∞)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hmean : 1 - ζ < ∫ p : PhaseTorus × (ℕ → Measure ℂ), if
      PhaseVeryGoodAnnulus (normalizedRestriction (p.2 0) (ball 0 6)) β 1 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison (normalizedRestriction (p.2 0) (ball 0 6)) 0 0 m
      then (1 : ℝ) else 0
      ∂(((volume : Measure PhaseCircle).prod volume).prod
        (P.map (fun ω n => localizedDyadicMeasure (ball 0 6) (μ ω) n)))) :
    ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℝ) := by
  let X : ℕ → Ω → Measure ℂ := fun n ω => localizedDyadicMeasure (ball 0 6) (μ ω) n
  let A : Set (PhaseTorus × Measure ℂ) := {p |
    PhaseVeryGoodAnnulus (normalizedRestriction p.2 (ball 0 6)) β 1 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
    AnnulusBallComparison (normalizedRestriction p.2 (ball 0 6)) 0 0 m}
  have hX : ∀ n, Measurable (X n) := by
    intro n
    exact (measurable_pi_apply n).comp
      ((measurable_localizedDyadicMeasure (ball 0 6) isOpen_ball.measurableSet).comp hμ)
  have hA : MeasurableSet A :=
    measurableSet_phaseVeryGoodComparable_normalizedRestriction β N₀
      a b C₁m C₁p C₂m C₂p C₃ m hunit
  have hmean' : 1 - ζ < ∫ p : PhaseTorus × (ℕ → Measure ℂ),
      @ite ℝ ((p.1, p.2 0) ∈ A) (Classical.propDecidable _) 1 0
      ∂(((volume : Measure PhaseCircle).prod volume).prod (P.map (fun ω n => X n ω))) := by
    simp only [A, mem_ofPred_eq, X]
    convert hmean using 1
    apply integral_congr_ae
    filter_upwards [] with p
    split_ifs <;> rfl
  have hf := ae_phase_path_blockFrequency_of_ergodic_shift P X hX herg A hA ζ hmean'
  filter_upwards [hf, Measure.quasiMeasurePreserving_snd.ae hmass] with p hp hm
  filter_upwards [hp] with N hN
  have heq : {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      ((phaseTorusDouble^[n]) p.1, X n p.2) ∈ A} =
      {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
        AnnulusBallComparison (μ p.2) n 0 m} := by
    ext n
    simp only [mem_ofPred_eq, A, X]
    rw [phaseVeryGoodComparable_normalizedPath_torus _ β n N₀
      a b C₁m C₁p C₂m C₂p C₃ m p.1 (hm n).1 (hm n).2]
  simpa only [heq] using hN

end HarmonicBalls
