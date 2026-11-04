import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodProbability

/-! # Dyadic transport of the phase-shifted event

A dyadic pullback sends a doubled phase to the original physical phase. The
outer lattice permits reduction of the doubled phase modulo `ℤ² / 100`. -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- One normalized dyadic pullback transports the full phase-shifted event
at scale `n` to the event at scale `n + 1`. -/
theorem phaseVeryGoodAnnulus_normalizedPullback_dyadic_succ
    (μ : Measure ℂ) (hcirc : ℝ → ℂ → ℝ) (γ α β : ℝ)
    (n N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) :
    PhaseVeryGoodAnnulus (normalizedPullbackMeasure γ α (dyadicScale 1) hcirc μ)
        β (dyadicScale n) 0 N a b C₁m C₁p C₂m C₂p C₃ ((2 : ℝ) • phase) ↔
      PhaseVeryGoodAnnulus μ β (dyadicScale (n + 1)) 0 N
        a b C₁m C₁p C₂m C₂p C₃ phase := by
  rw [phaseVeryGoodAnnulus_normalizedPullback,
    phaseVeryGoodAnnulus_map_inv_smul μ (dyadicScale_pos 1)]
  simp only [dyadicScale, pow_succ, smul_smul]
  norm_num
  ring

/-- The annulus-ball comparison undergoes the same dyadic shift. -/
theorem annulusBallComparison_normalizedPullback_dyadic_succ
    (μ : Measure ℂ) (hcirc : ℝ → ℂ → ℝ) (γ α : ℝ) (n : ℕ) (m : ℝ) :
    AnnulusBallComparison (normalizedPullbackMeasure γ α (dyadicScale 1) hcirc μ) n 0 m ↔
      AnnulusBallComparison μ (n + 1) 0 m := by
  unfold normalizedPullbackMeasure
  rw [annulusBallComparison_smul, annulusBallComparison_map_dyadic]
  · simp only [Nat.add_comm]
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  · exact ENNReal.ofReal_ne_top

/-- A representative of the doubled phase modulo the outer lattice gives the
same dyadic transport for the complete event and comparison. -/
theorem phaseVeryGoodComparable_normalizedPullback_dyadic_succ
    (μ : Measure ℂ) (hcirc : ℝ → ℂ → ℝ) (γ α β : ℝ)
    (n N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (phase phase' : ℂ)
    (hphase : phase' - (2 : ℝ) • phase ∈ Section6.scaledLattice ((1 : ℝ) / 100)) :
    (PhaseVeryGoodAnnulus (normalizedPullbackMeasure γ α (dyadicScale 1) hcirc μ)
        β (dyadicScale n) 0 N a b C₁m C₁p C₂m C₂p C₃ phase' ∧
      AnnulusBallComparison (normalizedPullbackMeasure γ α (dyadicScale 1) hcirc μ) n 0 m) ↔
    (PhaseVeryGoodAnnulus μ β (dyadicScale (n + 1)) 0 N
        a b C₁m C₁p C₂m C₂p C₃ phase ∧ AnnulusBallComparison μ (n + 1) 0 m) := by
  have hperiod : phase' - (2 : ℝ) • phase ∈
      Section6.scaledLattice (dyadicScale n / 100) := by
    simpa only [mul_one] using scaledLattice_outer_subset_dyadic 1 n hphase
  have hp := phaseVeryGoodAnnulus_outer_period
    (normalizedPullbackMeasure γ α (dyadicScale 1) hcirc μ) β (dyadicScale n) 0 N
    a b C₁m C₁p C₂m C₂p C₃ ((2 : ℝ) • phase) hperiod
  have hp' : (2 : ℝ) • phase + (phase' - (2 : ℝ) • phase) = phase' := by abel
  rw [hp'] at hp
  rw [← hp, phaseVeryGoodAnnulus_normalizedPullback_dyadic_succ,
    annulusBallComparison_normalizedPullback_dyadic_succ]

end HarmonicBalls

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal Classical

/-- The phase-shifted good-scale sequence is stationary when the phase map
preserves its law, the normalized measure has the original law, and the
phase map represents doubling modulo the outer lattice. -/
theorem phaseVeryGoodComparable_stationary_of_pullback_law
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [SFinite P] (Q : Measure T) [SFinite Q]
    (D : T → T) (hD : Measurable D) (hQ : Q.map D = Q)
    (phase : T → ℂ) (hphase : Measurable phase)
    (hperiod : ∀ t, phase (D t) - (2 : ℝ) • phase t ∈
      Section6.scaledLattice ((1 : ℝ) / 100))
    (U V : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν})
    (hU : Measurable U) (hV : Measurable V) (hlaw : P.map V = P.map U)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α β : ℝ)
    (hVeq : ∀ ω, (V ω).val =
      normalizedPullbackMeasure γ α (dyadicScale 1) (hcirc ω) (U ω).val)
    (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    (Q.prod P).map (fun p n => if
      PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale (n + 1)) 0 N
        a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
      AnnulusBallComparison (U p.2).val (n + 1) 0 m then (1 : ℝ) else 0) =
    (Q.prod P).map (fun p n => if
      PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N
        a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
      AnnulusBallComparison (U p.2).val n 0 m then (1 : ℝ) else 0) := by
  classical
  let M := {ν : Measure ℂ // IsLocallyFiniteMeasure ν}
  let F : T × M → ℕ → ℝ := fun p n => if
    PhaseVeryGoodAnnulus p.2.val β (dyadicScale n) 0 N
      a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
    AnnulusBallComparison p.2.val n 0 m then 1 else 0
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro n
    have hval : Measurable (fun p : T × M => p.2.val) :=
      measurable_subtype_coe.comp measurable_snd
    have hfin : ∀ p : T × M, IsLocallyFiniteMeasure p.2.val := fun p => p.2.property
    have hevent := (measurableSet_phaseVeryGoodAnnulus (c := fun _ : T × M => (0 : ℂ)) hval hfin measurable_const
      (hphase.comp measurable_fst) β (dyadicScale n) (dyadicScale_pos n) N
      a b C₁m C₁p C₂m C₂p C₃ hunit).inter
      (measurableSet_annulusBallComparison_joint (c := fun _ : T × M => (0 : ℂ)) hval hfin measurable_const n m)
    exact measurable_const.piecewise hevent measurable_const
  have hmaps : (Q.prod P).map (fun p => (D p.1, V p.2)) =
      (Q.prod P).map (fun p => (p.1, U p.2)) := by
    change (Q.prod P).map (Prod.map D V) = (Q.prod P).map (Prod.map id U)
    rw [← Measure.map_prod_map Q P hD hV, ← Measure.map_prod_map Q P measurable_id hU,
      hQ, hlaw, Measure.map_id]
  have hfun : (fun p : T × Ω => F (D p.1, V p.2)) =
      (fun p n => if PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale (n + 1)) 0 N
        a b C₁m C₁p C₂m C₂p C₃ (phase p.1) ∧
        AnnulusBallComparison (U p.2).val (n + 1) 0 m then (1 : ℝ) else 0) := by
    funext p n
    dsimp only [F]
    rw [hVeq]
    simp only [phaseVeryGoodComparable_normalizedPullback_dyadic_succ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hperiod p.1)]
  calc
    _ = (Q.prod P).map (fun p : T × Ω => F (D p.1, V p.2)) := by rw [hfun]
    _ = ((Q.prod P).map (fun p : T × Ω => (D p.1, V p.2))).map F := by
      simpa only [Function.comp_def] using
        (Measure.map_map hF (hD.comp measurable_fst |>.prodMk (hV.comp measurable_snd))).symm
    _ = ((Q.prod P).map (fun p : T × Ω => (p.1, U p.2))).map F := by rw [hmaps]
    _ = _ := by
      simpa only [Function.comp_def, F] using
        (Measure.map_map hF (measurable_fst.prodMk (hU.comp measurable_snd)))

end HarmonicBalls
