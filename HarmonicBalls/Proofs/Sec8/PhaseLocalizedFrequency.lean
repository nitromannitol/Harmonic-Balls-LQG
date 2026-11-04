import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodLocality
import HarmonicBalls.Proofs.Sec8.JointGoodScaleMean
import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodProbability
import HarmonicBalls.Proofs.Sec8.PhaseTorusLebesgue

/-! # Phase frequency for localized LQG measures

The pointwise ergodic theorem used by the imported path results is due to
Leonardo Bonanno's `LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Positive finite reference-ball masses remain positive and finite after
any dyadic pullback. -/
theorem ae_dyadic_mapped_ball_pos_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hpos : ∀ᵐ ω ∂P, ∀ r, 0 < r → μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ n,
      (μ ω).map (fun z : ℂ => (dyadicScale n)⁻¹ • z) (ball 0 6) ≠ 0 ∧
      (μ ω).map (fun z : ℂ => (dyadicScale n)⁻¹ • z) (ball 0 6) ≠ ∞ := by
  filter_upwards [hpos] with ω hω n
  rw [Measure.map_apply (by fun_prop) isOpen_ball.measurableSet,
    preimage_inv_smul_ball_zero (dyadicScale_pos n)]
  exact hω _ (mul_pos (dyadicScale_pos n) (by norm_num))

open Classical in
/-- A uniform fixed-phase failure bound gives the strict mean required for
Birkhoff along the normalized path. -/
theorem phaseLocalizedPath_mean_gt_of_uniform_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hmass : ∀ᵐ ω ∂P, ∀ n,
      (μ ω).map (fun z : ℂ => (dyadicScale n)⁻¹ • z) (ball 0 6) ≠ 0 ∧
      (μ ω).map (fun z : ℂ => (dyadicScale n)⁻¹ • z) (ball 0 6) ≠ ∞)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ε ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hε : 0 ≤ ε) (hεζ : ε < ζ)
    (hfail : ∀ phase : ℂ, P {ω | ¬
      (PhaseVeryGoodAnnulus (μ ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase ∧
        AnnulusBallComparison (μ ω) 0 0 m)} ≤ ENNReal.ofReal ε) :
    1 - ζ < ∫ p : PhaseTorus × (ℕ → Measure ℂ), if
      PhaseVeryGoodAnnulus (normalizedRestriction (p.2 0) (ball 0 6)) β 1 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison (normalizedRestriction (p.2 0) (ball 0 6)) 0 0 m
      then (1 : ℝ) else 0
      ∂(((volume : Measure PhaseCircle).prod volume).prod
        (P.map (fun ω n => localizedDyadicMeasure (ball 0 6) (μ ω) n))) := by
  let Q : Measure PhaseTorus := (volume : Measure PhaseCircle).prod volume
  let path : Ω → ℕ → Measure ℂ := fun ω n => localizedDyadicMeasure (ball 0 6) (μ ω) n
  let A : Set (PhaseTorus × Measure ℂ) := {p |
    PhaseVeryGoodAnnulus (normalizedRestriction p.2 (ball 0 6)) β 1 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
    AnnulusBallComparison (normalizedRestriction p.2 (ball 0 6)) 0 0 m}
  let B : Set (PhaseTorus × (ℕ → Measure ℂ)) := {p | (p.1, p.2 0) ∈ A}
  let F : PhaseTorus × (ℕ → Measure ℂ) → ℝ := fun p => if p ∈ B then 1 else 0
  have hp : Measurable path := (measurable_localizedDyadicMeasure _ isOpen_ball.measurableSet).comp hμ
  have hA : MeasurableSet A := measurableSet_phaseVeryGoodComparable_normalizedRestriction β N₀
    a b C₁m C₁p C₂m C₂p C₃ m hunit
  have hB : MeasurableSet B := hA.preimage
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hF : Measurable F := measurable_const.piecewise hB measurable_const
  have hsection (t : PhaseTorus) : P {ω | ¬ ((t, path ω 0) ∈ A)} ≤ ENNReal.ofReal ε := by
    calc
      _ = P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β 1 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧ AnnulusBallComparison (μ ω) 0 0 m)} := by
        apply measure_congr
        filter_upwards [hmass] with ω hω
        simp only [mem_ofPred_eq, A, path]
        have hh := phaseVeryGoodComparable_normalizedPath_torus (μ ω) β 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ m t (hω 0).1 (hω 0).2
        apply propext
        simpa only [Function.iterate_zero, id_eq, dyadicScale, pow_zero] using not_congr hh
      _ ≤ ENNReal.ofReal ε := hfail (torusPhase t)
  have hpre : MeasurableSet {p : PhaseTorus × Ω | ¬ ((p.1, path p.2 0) ∈ A)} :=
    (hA.preimage (measurable_fst.prodMk ((measurable_pi_apply 0).comp (hp.comp measurable_snd)))).compl
  have hprod : (Q.prod P) {p : PhaseTorus × Ω | ¬ ((p.1, path p.2 0) ∈ A)} ≤ ENNReal.ofReal ε := by
    rw [Measure.prod_apply hpre]
    calc
      _ ≤ ∫⁻ _ : PhaseTorus, ENNReal.ofReal ε ∂Q := lintegral_mono hsection
      _ = ENNReal.ofReal ε := by simp [Q]
  have hmap : (Q.prod P).map (Prod.map id path) = Q.prod (P.map path) := by
    rw [← Measure.map_prod_map Q P measurable_id hp, Measure.map_id]
  have hfailB : (Q.prod (P.map path)) Bᶜ ≤ ENNReal.ofReal ε := by
    rw [← hmap, Measure.map_apply (measurable_id.prodMap hp) hB.compl]
    exact hprod
  have hmean := integral_indicator_gt_of_failure_le (Q.prod (P.map path)) B F hF
    (by intro p; by_cases hp : p ∈ B <;> simp [F, hp]) hε hεζ hfailB
  simpa only [F, B, A, path, Q, mem_ofPred_eq] using hmean

open Classical in
/-- Uniform failure bounds imply phase block frequency for any ergodic
localized path with almost-everywhere measurable random measure. -/
theorem ae_phaseVeryGoodComparable_blockFrequency_of_uniform_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (herg : Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 6) (μ ω) n)))
    (hpos : ∀ᵐ ω ∂P, ∀ r, 0 < r → μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ε ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hε : 0 ≤ ε) (hεζ : ε < ζ)
    (hfail : ∀ phase : ℂ, P {ω | ¬
      (PhaseVeryGoodAnnulus (μ ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase ∧
        AnnulusBallComparison (μ ω) 0 0 m)} ≤ ENNReal.ofReal ε) :
    ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℝ) := by
  let ν := hμ.mk μ
  have heq : μ =ᵐ[P] ν := hμ.ae_eq_mk
  have hposν : ∀ᵐ ω ∂P, ∀ r, 0 < r → ν ω (ball 0 r) ≠ 0 ∧ ν ω (ball 0 r) ≠ ∞ := by
    filter_upwards [hpos, heq] with ω hp he
    simpa only [← he] using hp
  have hmassν := ae_dyadic_mapped_ball_pos_finite P ν hposν
  have hpaths : (fun ω n => localizedDyadicMeasure (ball 0 6) (μ ω) n) =ᵐ[P]
      (fun ω n => localizedDyadicMeasure (ball 0 6) (ν ω) n) := by
    filter_upwards [heq] with ω he
    simp only [he]
  have hergν : Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 6) (ν ω) n)) := by
    rw [← Measure.map_congr hpaths]
    exact herg
  have hfailν (phase : ℂ) : P {ω | ¬
      (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase ∧
        AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal ε := by
    calc
      _ = P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β 1 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ phase ∧ AnnulusBallComparison (μ ω) 0 0 m)} := by
        apply measure_congr
        filter_upwards [heq] with ω he
        simp only [← he]
      _ ≤ ENNReal.ofReal ε := hfail phase
  have hmean := phaseLocalizedPath_mean_gt_of_uniform_failure P ν hμ.measurable_mk hmassν
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ε ζ hunit hε hεζ hfailν
  have hf := ae_phaseVeryGoodComparable_blockFrequency_of_localized_path P ν hμ.measurable_mk
    hergν hmassν β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hmean
  filter_upwards [hf, Measure.quasiMeasurePreserving_snd.ae heq] with p hp he
  simpa only [← he] using hp

universe u

open Classical in
/-- Whole-plane GFF scaling, full support and buffered field-local normalized
versions imply Haar-phase frequency from a uniform one-scale failure bound. -/
theorem IsWholePlaneGFF.ae_phaseVeryGoodComparable_blockFrequency_of_buffered_versions
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (hrep : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ε ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hε : 0 ≤ ε) (hεζ : ε < ζ)
    (hfail : ∀ phase : ℂ, P {ω | ¬
      (PhaseVeryGoodAnnulus (μ ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase ∧
        AnnulusBallComparison (μ ω) 0 0 m)} ≤ ENNReal.ofReal ε) :
    ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hp := ae_referenceBall_pos_finite P μ
    (hfull γ α hγ hγ2 hα Ω P hC hcirc μ hGFF hμ)
    (hμ.mono (fun _ h => h.isLocallyFiniteMeasure))
  have herg := hGFF.ergodic_localizedDyadicMeasure_shift_of_fullSupport hfull
    hγ hγ2 hα hμ hAff hCC 6 (by norm_num) hrep
  exact ae_phaseVeryGoodComparable_blockFrequency_of_uniform_failure P μ
    (hGFF.aemeasurable_lqgMeasure hμ) herg hp β N₀ a b C₁m C₁p C₂m C₂p C₃ m ε ζ
    hunit hε hεζ hfail

open Classical in
/-- The uniform one-scale estimates produce constants for the Haar-phase
block-frequency conclusion, assuming buffered normalized local versions. -/
theorem IsWholePlaneGFF.exists_ae_phaseVeryGoodComparable_blockFrequency
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hrep : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst 0 hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r))
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N →
      ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N
              a b C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
            AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℝ) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  let δ : ℝ≥0∞ := ENNReal.ofReal (ζ / 8)
  have hδ : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfail⟩ :=
    exists_phaseVeryGoodComparable_probability hgrowth hfull P hγ hγ2 hβ hc
      hGFF hμ hAff hCC hprev hunit hδ
  have hδsum : δ + δ + δ + δ = ENNReal.ofReal (ζ / 2) := by
    dsimp only [δ]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN
  apply hGFF.ae_phaseVeryGoodComparable_blockFrequency_of_buffered_versions hfull
    hγ hγ2 hQ hμ hAff hCC hrep β N a b C₁m C₁p C₂m C₂p c m (ζ / 2) ζ
    hunit (by positivity) (by linarith)
  intro phase
  simpa only [hδsum] using hfail N hN phase

open Classical in
/-- The phase-frequency estimate transfers to recentered measures under
Lebesgue-dominated center laws and dominated comparison field laws. -/
theorem IsWholePlaneGFF.exists_ae_ae_centered_veryGoodComparable_blockFrequency
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hrep : ∀ ε, 0 < ε → ∃ r ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst 0 hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r))
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) (R : ℂ → Measure Ω)
    (hdom : ∀ᵐ z ∂ρ, R z ≪ P) (M : ℂ → Ω → Measure ℂ)
    (hcenter : ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(R z),
      (M z ω).map (fun w : ℂ => w - z) = μ ω)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N → ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(R z), ∀ᶠ K : ℕ in atTop,
        (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (M z ω) β z N
          a b C₁m C₁p C₂m C₂p c m K : ℝ) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfreq⟩ :=
    hGFF.exists_ae_phaseVeryGoodComparable_blockFrequency hgrowth hfull
      hγ hγ2 hβ hc hμ hAff hCC hrep hprev hunit hζ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN
  exact ae_ae_veryGoodComparableScaleFrequency_of_phase_torus P ρ hρ R hdom
    μ M hcenter β N a b C₁m C₁p C₂m C₂p c m ζ (hfreq N hN)

end HarmonicBalls
