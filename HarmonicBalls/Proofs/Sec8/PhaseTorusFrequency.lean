import HarmonicBalls.Proofs.Sec8.PhaseTorusLebesgue
import HarmonicBalls.Proofs.Sec8.PhaseErgodicFactor
import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodProbability
import HarmonicBalls.Proofs.Sec8.JointGoodScaleMean

/-! # Phase-torus block frequencies

The ergodic average used here is based on Leonardo Bonanno's LatticeProb
formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Filter Finset
open scoped Topology BigOperators

namespace HarmonicBalls

open Classical in
/-- Joint ergodicity and normalized-pullback transport turn a strict
one-scale mean bound into a block-frequency bound for Haar-almost every phase. -/
theorem ae_phaseTorus_blockFrequency_of_ergodic_rescaling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → Ω)
    (herg : Ergodic (Prod.map phaseTorusDouble R)
      (((volume : Measure PhaseCircle).prod volume).prod P))
    (U : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}) (hU : Measurable U)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α β : ℝ)
    (hUeq : ∀ᵐ ω ∂P, (U (R ω)).val =
      normalizedPullbackMeasure γ α (dyadicScale 1) (hcirc ω) (U ω).val)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hmean : 1 - ζ < ∫ p : PhaseTorus × Ω, if
      PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale 0) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
        AnnulusBallComparison (U p.2).val 0 0 m then (1 : ℝ) else 0
      ∂(((volume : Measure PhaseCircle).prod volume).prod P)) :
    ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤
          (({n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧
            PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
              a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
            AnnulusBallComparison (U p.2).val n 0 m}.ncard : ℕ) : ℝ) := by
  let Q : Measure PhaseTorus := (volume : Measure PhaseCircle).prod volume
  let X : ℕ → PhaseTorus × Ω → ℝ := fun n p => if
    PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison (U p.2).val n 0 m then 1 else 0
  have hval : Measurable (fun p : PhaseTorus × Ω => (U p.2).val) :=
    measurable_subtype_coe.comp (hU.comp measurable_snd)
  have hfin : ∀ p : PhaseTorus × Ω, IsLocallyFiniteMeasure (U p.2).val :=
    fun p => (U p.2).property
  have hm : ∀ n, Measurable (X n) := by
    intro n
    have hs := (measurableSet_phaseVeryGoodAnnulus
      (c := fun _ : PhaseTorus × Ω => (0 : ℂ)) hval hfin measurable_const
      (measurable_torusPhase.comp measurable_fst) β (dyadicScale n) (dyadicScale_pos n) N₀
      a b C₁m C₁p C₂m C₂p C₃ hunit).inter
      (measurableSet_annulusBallComparison_joint (c := fun _ : PhaseTorus × Ω => (0 : ℂ))
        hval hfin measurable_const n m)
    exact measurable_const.piecewise hs measurable_const
  have hb : ∀ n p, X n p ∈ Set.Icc (0 : ℝ) 1 := by
    intro n p
    dsimp only [X]
    split_ifs <;> norm_num
  have ht : ∀ᵐ p ∂(Q.prod P), ∀ n, X n (Prod.map phaseTorusDouble R p) = X (n + 1) p := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hUeq] with p hp
    intro n
    dsimp only [X, Prod.map]
    simp only [hp, phaseVeryGoodComparable_normalizedPullback_dyadic_succ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (torusPhase_double_sub_mem_lattice p.1)]
  have hconv := ae_tendsto_initialScaleAverage_of_ae_ergodic_transport (Q.prod P)
    (Prod.map phaseTorusDouble R) herg X hm hb ht
  filter_upwards [hconv] with p hp
  apply eventually_goodScale_block_ncard
    (fun n => PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison (U p.2).val n 0 m) hp
  exact hmean

open Classical in
/-- Uniform one-scale failure bounds and joint rescaling ergodicity imply the
block-frequency estimate for Lebesgue-dominated centre laws and dominated
comparison field laws, with the recentered measure identified explicitly. -/
theorem ae_ae_centered_blockFrequency_of_ergodic_rescaling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → Ω)
    (herg : Ergodic (Prod.map phaseTorusDouble R)
      (((volume : Measure PhaseCircle).prod volume).prod P))
    (U : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}) (hU : Measurable U)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α β : ℝ)
    (hUeq : ∀ᵐ ω ∂P, (U (R ω)).val =
      normalizedPullbackMeasure γ α (dyadicScale 1) (hcirc ω) (U ω).val)
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) (S : ℂ → Measure Ω)
    (hdom : ∀ᵐ z ∂ρ, S z ≪ P) (M : ℂ → Ω → Measure ℂ)
    (hcenter : ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(S z),
      (M z ω).map (fun w : ℂ => w - z) = (U ω).val)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ ε : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hε : 0 ≤ ε) (hεζ : ε < ζ)
    (hfail : ∀ phase : ℂ, P {ω | ¬
      (PhaseVeryGoodAnnulus (U ω).val β (dyadicScale 0) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ phase ∧
        AnnulusBallComparison (U ω).val 0 0 m)} ≤ ENNReal.ofReal ε) :
    ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(S z), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (M z ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  let Q : Measure PhaseTorus := (volume : Measure PhaseCircle).prod volume
  let A : Set (PhaseTorus × Ω) := {p |
    PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale 0) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison (U p.2).val 0 0 m}
  let X : PhaseTorus × Ω → ℝ := fun p => if p ∈ A then 1 else 0
  have hval : Measurable (fun p : PhaseTorus × Ω => (U p.2).val) :=
    measurable_subtype_coe.comp (hU.comp measurable_snd)
  have hfin : ∀ p : PhaseTorus × Ω, IsLocallyFiniteMeasure (U p.2).val :=
    fun p => (U p.2).property
  have hA : MeasurableSet A :=
    (measurableSet_phaseVeryGoodAnnulus
      (c := fun _ : PhaseTorus × Ω => (0 : ℂ)) hval hfin measurable_const
      (measurable_torusPhase.comp measurable_fst) β (dyadicScale 0) (dyadicScale_pos 0) N₀
      a b C₁m C₁p C₂m C₂p C₃ hunit).inter
      (measurableSet_annulusBallComparison_joint (c := fun _ : PhaseTorus × Ω => (0 : ℂ))
        hval hfin measurable_const 0 m)
  have hX : Measurable X := measurable_const.piecewise hA measurable_const
  have hprod : (Q.prod P) Aᶜ ≤ ENNReal.ofReal ε := by
    exact measure_prod_not_phaseVeryGoodComparable_le P Q
      (measurable_subtype_coe.comp hU) (fun ω => (U ω).property) measurable_torusPhase
      β (dyadicScale 0) (dyadicScale_pos 0) 0 N₀ 0
      a b C₁m C₁p C₂m C₂p C₃ m hunit hfail
  have hmean := integral_indicator_gt_of_failure_le (Q.prod P) A X hX
    (by intro p; dsimp only [X]; split_ifs <;> rfl) hε hεζ hprod
  have hphase := ae_phaseTorus_blockFrequency_of_ergodic_rescaling P R herg U hU
    hcirc γ α β hUeq N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hmean
  exact ae_ae_veryGoodComparableScaleFrequency_of_phase_torus P ρ hρ S hdom
    (fun ω => (U ω).val) M hcenter β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hphase

end HarmonicBalls
