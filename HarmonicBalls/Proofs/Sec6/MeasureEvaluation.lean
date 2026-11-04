import HarmonicBalls.Proofs.Sec6.PotentialRatioAEMeasurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Almost-everywhere measurable evaluations of locally finite random measures -/

namespace HarmonicBalls.Section6

open MeasureTheory
open scoped ENNReal

/-- On a finite-mass open set, almost-everywhere measurable open-set evaluations
extend to all Borel-set evaluations. -/
theorem aemeasurable_measure_inter_open_of_open_evaluations
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure Ω) (μ : Ω → Measure X)
    (hopen : ∀ U : Set X, IsOpen U → AEMeasurable (fun ω => μ ω U) P)
    {B : Set X} (hB : IsOpen B) (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞)
    (A : Set X) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => μ ω (A ∩ B)) P := by
  refine MeasurableSpace.induction_on_inter BorelSpace.measurable_eq isPiSystem_isOpen
    (C := fun A _ => AEMeasurable (fun ω => μ ω (A ∩ B)) P) ?_ ?_ ?_ ?_ A hA
  · simp
  · intro U hU
    exact hopen _ (hU.inter hB)
  · intro U hU ih
    apply ((hopen B hB).sub ih).congr
    filter_upwards [hfin] with ω hω
    have hfin' : μ ω (U ∩ B) ≠ ∞ :=
      ne_top_of_le_ne_top hω (measure_mono Set.inter_subset_right)
    have heq : Uᶜ ∩ B = B \ (U ∩ B) := by ext x; simp [and_comm]
    rw [heq, measure_sdiff Set.inter_subset_right (hU.inter hB.measurableSet).nullMeasurableSet hfin']
    rfl
  · intro f hdisj hfm ih
    have hdisj' : Pairwise (Function.onFun Disjoint fun i => f i ∩ B) :=
      fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hm : AEMeasurable (fun ω => ∑' i : ℕ, μ ω (f i ∩ B)) P :=
      AEMeasurable.tsum (fun i => ih i)
    apply hm.congr
    filter_upwards [] with ω
    rw [Set.iUnion_inter, measure_iUnion hdisj' (fun i => (hfm i).inter hB.measurableSet)]

/-- Open-set evaluations determine almost-everywhere measurable Borel evaluations
for a random measure which is almost surely locally finite. -/
theorem aemeasurable_measure_of_open_evaluations
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hopen : ∀ U : Set ℂ, IsOpen U → AEMeasurable (fun ω => μ ω U) P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (A : Set ℂ) (hA : MeasurableSet A) : AEMeasurable (fun ω => μ ω A) P := by
  let B : ℕ → Set ℂ := fun n => Metric.ball 0 n
  have hBopen : ∀ n, IsOpen (B n) := fun _ => Metric.isOpen_ball
  have hBfin : ∀ n, ∀ᵐ ω ∂P, μ ω (B n) ≠ ∞ := by
    intro n
    filter_upwards [hloc] with ω hω
    have : IsLocallyFiniteMeasure (μ ω) := hω
    exact measure_ball_ne_top
  have hm : AEMeasurable (fun ω => ⨆ n, μ ω (A ∩ B n)) P :=
    .iSup fun n => aemeasurable_measure_inter_open_of_open_evaluations P μ hopen
      (hBopen n) (hBfin n) A hA
  apply hm.congr
  filter_upwards [] with ω
  have hmono : Monotone (fun n => A ∩ B n) := by
    intro m n hmn
    exact Set.inter_subset_inter_right _ (Metric.ball_subset_ball (by exact_mod_cast hmn))
  rw [← hmono.measure_iUnion]
  simp only [← Set.inter_iUnion, B, Metric.iUnion_ball_nat, Set.inter_univ]

universe u

/-- LQG locality and local finiteness imply that every deterministic Borel-set
mass is an almost everywhere measurable random variable. -/
theorem aemeasurable_lqg_measure_borel
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (A : Set ℂ) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => μ ω A) P := by
  apply aemeasurable_measure_of_open_evaluations P μ
    (fun U hU => aemeasurable_lqg_measure_open hγ hγ2 hα hGFF hμ hloc hU) ?_ A hA
  filter_upwards [hμ] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- The LQG potential extrema ratio on a deterministic smooth bounded domain is
almost everywhere measurable, using locality and the Hölder regularity input. -/
theorem aemeasurable_lqg_greenPotential_ratio_of_locality
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {O K : Set ℂ} (hO : IsSmoothBoundedOpen O) (hK : K ⊆ closure O) :
    AEMeasurable (fun ω =>
      ((⨅ z : K, ENNReal.ofReal (greenPotential O (μ ω) z)) /
        (⨆ z : O, ENNReal.ofReal (greenPotential O (μ ω) z))).toReal) P := by
  exact aemeasurable_lqg_greenPotential_ratio_of_evaluations hholder hγ hγ2 hα hGFF hμ
    (aemeasurable_lqg_measure_borel hγ hγ2 hα hGFF hμ hloc) hO hK

/-- A positive almost-everywhere measurable random variable admits a positive
deterministic lower quantile. -/
theorem exists_small_threshold_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Set.Ioo (0 : ℝ) 1, P {ω | X ω < a} ≤ δ := by
  have hpos' : ∀ᵐ ω ∂P, 0 < hX.mk X ω := by
    filter_upwards [hpos, hX.ae_eq_mk] with ω hp heq
    rwa [← heq]
  obtain ⟨a, ha, hsmall⟩ := exists_small_threshold P hX.measurable_mk hpos' hδ
  refine ⟨a, ha, ?_⟩
  have heq : {ω | X ω < a} =ᵐ[P] {ω | hX.mk X ω < a} := by
    filter_upwards [hX.ae_eq_mk] with ω hω
    simp only [hω]
  rwa [measure_congr heq]

/-- Scale-invariant lower tails imply positive recurrence when the reference
random variable is only almost everywhere measurable. -/
theorem ae_frequently_pos_of_equal_lower_tails_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → ℝ) (hX : AEMeasurable (X 0) P)
    (hpos : ∀ᵐ ω ∂P, 0 < X 0 ω)
    (hlaw : ∀ n : ℕ, ∀ a : ℝ, P {ω | X n ω < a} = P {ω | X 0 ω < a}) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N, a ≤ X n ω := by
  let Y : ℕ → Ω → ℝ := fun n ω => if n = 0 then hX.mk (X 0) ω else X n ω
  have heq : ∀ᵐ ω ∂P, ∀ n, Y n ω = X n ω := by
    filter_upwards [hX.ae_eq_mk] with ω hω n
    by_cases hn : n = 0
    · subst n
      simpa [Y] using hω.symm
    · simp [Y, hn]
  have hYm : Measurable (Y 0) := by simpa [Y] using hX.measurable_mk
  have hYpos : ∀ᵐ ω ∂P, 0 < Y 0 ω := by
    filter_upwards [hpos, heq] with ω hp he
    rw [he 0]
    exact hp
  have hYlaw : ∀ n a, P {ω | Y n ω < a} = P {ω | Y 0 ω < a} := by
    intro n a
    have hmeasure (k : ℕ) : P {ω | Y k ω < a} = P {ω | X k ω < a} := by
      apply measure_congr
      filter_upwards [heq] with ω hω
      simp only [hω k]
    rw [hmeasure n, hmeasure 0, hlaw n a]
  have hrec := ae_frequently_pos_of_equal_lower_tails P Y hYm hYpos hYlaw
  filter_upwards [hrec, heq] with ω hω he
  obtain ⟨a, ha, hfreq⟩ := hω
  refine ⟨a, ha, fun N => ?_⟩
  obtain ⟨n, hn, hval⟩ := hfreq N
  exact ⟨n, hn, hval.trans (he n).le⟩

end HarmonicBalls.Section6
