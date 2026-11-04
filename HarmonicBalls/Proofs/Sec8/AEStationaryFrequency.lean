import HarmonicBalls.Proofs.Sec8.AEIndicatorFrequency
import HarmonicBalls.Proofs.Sec8.VeryGoodStationarityAE

/-! # Measurable stationary versions of good-scale indicators

The pointwise ergodic theorem used through `AEIndicatorFrequency` is from
Leonardo Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace HarmonicBalls

/-- An almost-everywhere measurable stationary process has an everywhere
measurable stationary version, agreeing at every index almost surely. -/
theorem exists_measurable_stationary_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℕ → ℝ)
    (hstat : IdentDistrib F (fun ω n => F ω (n + 1)) P P) :
    ∃ X : ℕ → Ω → ℝ, (∀ n, Measurable (X n)) ∧
      (∀ n, (fun ω => X n ω) =ᵐ[P] fun ω => F ω n) ∧
      P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω) := by
  let G : Ω → ℕ → ℝ := hstat.aemeasurable_fst.mk F
  have hGm : Measurable G := hstat.aemeasurable_fst.measurable_mk
  have hG : G =ᵐ[P] F := hstat.aemeasurable_fst.ae_eq_mk.symm
  refine ⟨fun n ω => G ω n, fun n => (measurable_pi_apply n).comp hGm, ?_, ?_⟩
  · intro n
    filter_upwards [hG] with ω hω
    exact congrFun hω n
  · have hs : (fun ω n => G ω (n + 1)) =ᵐ[P] (fun ω n => F ω (n + 1)) := by
      filter_upwards [hG] with ω hω
      simp only [hω]
    exact (Measure.map_congr hs).trans (hstat.map_eq.symm.trans (Measure.map_congr hG).symm)

open Classical in
/-- A stationary good-scale process with local almost-sure versions obeys
its frequency bound when the local germ is trivial. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω => if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then (1 : ℝ) else 0)
          =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hstat : IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale (n + 1)) z N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (n + 1) z m then (1 : ℝ) else 0) P P)
    (hq : 1 - ζ < (P {ω | IsVeryGoodAnnulus (μ ω) βminus (dyadicScale 0) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 z m}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let F : Ω → ℕ → ℝ := fun ω n =>
    if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0
  obtain ⟨X, hXm, hX, hs⟩ := exists_measurable_stationary_version P F hstat
  have hlocal' : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n) := by
    intro ε hε
    obtain ⟨K, Y, hYm, hY⟩ := hlocal ε hε
    exact ⟨K, Y, hYm, fun n hn => (hX n).trans (hY n hn)⟩
  have hs' : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω) := by
    let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun x n => x (n + 1)
    have hm := congrArg (Measure.map shift) hs
    rw [Measure.map_map measurable_sequence_shift (Measurable.of_eval (fun n => hXm (n + 1))),
      Measure.map_map measurable_sequence_shift (Measurable.of_eval hXm)] at hm
    simpa [shift, Function.comp_def, Nat.add_assoc] using hm
  let A : Set Ω := {ω | IsVeryGoodAnnulus (μ ω) βminus (dyadicScale 0) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 z m}
  let B : Set Ω := (X 0) ⁻¹' {1}
  have hBm : MeasurableSet B := hXm 0 (measurableSet_singleton 1)
  have hAB : A =ᵐ[P] B := by
    filter_upwards [hX 0] with ω hω
    simp only [A, Set.mem_ofPred_eq, B, Set.mem_preimage, Set.mem_singleton_iff, F] at hω ⊢
    rw [hω]
    split_ifs <;> simp_all
  have hi : ∫ ω, X 0 ω ∂P = (P A).toReal := by
    have hXI : X 0 =ᵐ[P] B.indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [hX 0, hAB] with ω hω hab
      simp only [Set.indicator_apply, B, Set.mem_preimage, Set.mem_singleton_iff]
      simp only [F, A, Set.mem_ofPred_eq] at hω hab
      rw [hω]
      split_ifs <;> simp_all
    rw [integral_congr_ae hXI]
    change (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂P) = (P A).toReal
    rw [integral_indicator_one hBm, measureReal_def, ← measure_congr hAB]
  apply ae_eventually_veryGoodComparableScaleCount_of_stationary_ae_indicator P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X (∫ ω, X 0 ω ∂P) ζ germ r hr hcofinal hrmono hgmono
    hlocal' htrivial hX hXm hs' (integral_eq_first_of_stationary P X hXm hs)
  simpa only [hi] using hq

universe u

open Classical MarkovProcess in
/-- The LQG good-scale frequency bound follows from local representatives,
germ triviality, a one-scale probability estimate and the stated LQG inputs. -/
theorem ae_eventually_lqg_veryGoodComparableScaleCount_of_local_versions
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
          =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hq : 1 - ζ < (P {ω | IsVeryGoodAnnulus (μ ω) β (dyadicScale 0) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 0 m}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) β 0 N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  apply ae_eventually_veryGoodComparableScaleCount_of_identDistrib P μ β 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ m ζ germ r hr hcofinal hrmono hgmono hlocal htrivial
  · simpa only [Nat.add_comm 1] using
      identDistrib_lqg_veryGoodComparable_of_ae_point_avoidance hfull hγ hγ2 hα
        hGFF hμ hatom hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha hpolar
  · exact hq

end HarmonicBalls
